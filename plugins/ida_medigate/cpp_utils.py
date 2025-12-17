import logging
from functools import partial, lru_cache

import re
import ida_bytes
import ida_hexrays
import ida_name
import ida_typeinf
import ida_nalt
import ida_xref
import ida_idaapi
import idaapi
import idautils
import idc
from ida_idaapi import BADADDR
from . import utils
from .utils import batchmode

VTABLE_UNION_KEYWORD = "VTABLES"
VTABLES_UNION_VTABLE_FIELD_POSTFIX = ""
VTABLE_DELIMITER = "::"
VTABLE_POSTFIX = ida_typeinf.VTBL_SUFFIX
VTABLE_FIELD_NAME = ida_typeinf.VTBL_MEMNAME
VTABLE_INSTANCE_DELIMITER = VTABLE_DELIMITER
VTABLE_INSTANCE_KEYWORD = "vftable"
VTABLE_INSTANCE_POSTFIX = VTABLE_INSTANCE_DELIMITER + VTABLE_INSTANCE_KEYWORD
MF_BASECLASS = 0x400
PURE_VIRTUAL_NAME = '__cxa_pure_virtual'


def get_vtable_instance_name(class_name, parent_name=None):
    name = class_name + VTABLE_INSTANCE_POSTFIX
    if parent_name is not None:
        name += VTABLE_INSTANCE_DELIMITER + parent_name
    return name


def get_base_member_name(parent_name, offset):
    return "%s_%X" % (parent_name, offset)


def get_vtable_line(ea, stop_ea=None, ignore_list=None, pure_virtual_name=PURE_VIRTUAL_NAME):
    if stop_ea is not None and ea >= stop_ea:
        return None, 0
    if ignore_list is None:
        ignore_list = []
    func_ea = utils.get_ptr(ea)
    if func_ea in ignore_list:
        return None, 0
    is_pure_func = pure_virtual_name is not None and idc.GetDisasm(ea).endswith(pure_virtual_name)
    if not is_pure_func:
        if not utils.is_func(func_ea):
            func_ea -= 1 # ARM: function pointers point to func_start+1
        if not utils.is_func(func_ea):
            return None, 0
    return func_ea, ea + utils.WORD_LEN


def is_valid_vtable_name(member_name):
    return VTABLE_FIELD_NAME in member_name


def is_valid_vtable_type(member, member_type):
    if member_type.is_ptr():
        struct = utils.deref_struct_from_tinfo(member_type)
        return is_struct_vtable(struct)
    return False


def is_member_vtable(member):
    member_type = utils.get_member_tinfo(member)
    if not member_type or not isinstance(member_type, ida_typeinf.tinfo_t):
        return False
    if not is_valid_vtable_name(member.name):
        return False
    if not is_valid_vtable_type(member, member_type):
        return False
    return True


def is_struct_vtable(struct: ida_typeinf.tinfo_t):
    if struct is None:
        return False
    struct_name = struct.get_type_name()
    return VTABLE_POSTFIX in struct_name


def is_vtables_union(union):
    if union is None:
        return False
    if not union.is_union():
        return False
    union = ida_typeinf.tinfo_t()
    union_name = union.get_type_name()
    return is_vtables_union_name(union_name)


def is_vtables_union_name(union_name):
    return union_name.endswith(VTABLE_UNION_KEYWORD)


def find_vtable_at_offset(struct_ptr: ida_typeinf.tinfo_t, vtable_offset: int):
    current_struct = struct_ptr
    current_offset = 0
    _, member = struct_ptr.get_udm_by_offset(vtable_offset)
    if member is None:
        return None
    parents_vtables_classes = []
    current_offset += member.offset
    while current_offset < vtable_offset and member is not None:
        current_struct = utils.get_member_substruct(member)
        if current_struct is None:
            return None
        parents_vtables_classes.append(
            [
                current_struct.get_type_name(),
                vtable_offset - current_offset,
            ]
        )
        _, member = current_struct.get_udm_by_offset(vtable_offset - current_offset)
        if member is None:
            logging.exception(
                "Couldn't find vtable at offset %d for %d",
                vtable_offset - current_offset,
                struct_ptr.get_tid(),
            )
        current_offset += member.offset

    if current_offset != vtable_offset:
        return None

    while member is not None:
        if is_member_vtable(member):
            return member, current_struct, parents_vtables_classes
        current_struct = utils.get_member_substruct(member)
        if current_struct is None:
            return None
        parents_vtables_classes.append(
            [current_struct.get_type_name(), 0]
        )
        index, member = current_struct.get_udm(0)

    return None


def get_class_vtable_struct_name(class_name, vtable_offset_in_class):
    if vtable_offset_in_class == 0:
        return class_name + VTABLE_POSTFIX
    return "%s_%04X%s" % (class_name, vtable_offset_in_class, VTABLE_POSTFIX)


def get_class_vtable_field_name(class_name):
    return VTABLE_FIELD_NAME


def get_class_vtables_union_name(class_name):
    return class_name + VTABLE_DELIMITER + VTABLE_UNION_KEYWORD


def get_class_vtables_field_name(child_name):
    return child_name + VTABLES_UNION_VTABLE_FIELD_POSTFIX


def get_interface_empty_vtable_name():
    return "INTERFACE"


def install_vtables_union(
    class_name: str,
    class_vtable_member: ida_typeinf.udm_t=None,
    vtable_member_tinfo: ida_typeinf.tinfo_t=None,
    offset=0
):
    logging.debug(
        "install_vtables_union(%s, %s, %s)",
        class_name,
        class_vtable_member,
        str(vtable_member_tinfo),
    )
    if class_vtable_member and vtable_member_tinfo:
        old_vtable_sptr = utils.extract_struct_from_tinfo(vtable_member_tinfo)
        old_vtable_class_name = old_vtable_sptr.get_type_name()
    else:
        old_vtable_class_name = get_class_vtable_struct_name(class_name, offset)
        old_vtable_sptr = utils.get_sptr_by_name(old_vtable_class_name)
    vtables_union_name = old_vtable_class_name
    if old_vtable_sptr and (0 != old_vtable_sptr.rename_type(old_vtable_class_name + "_orig")):
        logging.exception(
            f"Failed changing {old_vtable_class_name}->"
            f"{old_vtable_class_name+'_orig'}"
        )
        # FIXME: why -1 and not None?
        return -1
    vtables_union_id = utils.get_or_create_struct_id(vtables_union_name, True)
    vtable_member_tinfo = utils.get_typeinf(old_vtable_class_name + "_orig")
    if vtables_union_id == BADADDR:
        logging.exception(
            "Cannot create union vtable for %s()%s",
            class_name,
            vtables_union_name,
        )
        # FIXME: why -1 and not None?
        return -1

    vtables_union = ida_typeinf.tinfo_t(tid=vtables_union_id)
    if not vtables_union:
        logging.exception("Could retrieve vtables union for %s", class_name)
        # FIXME: return -1?
    if vtable_member_tinfo is not None:
        vtables_union_vtable_field_name = get_class_vtables_field_name(class_name)
    else:
        vtables_union_vtable_field_name = get_interface_empty_vtable_name()
    utils.add_to_struct(vtables_union, vtables_union_vtable_field_name, vtable_member_tinfo)
    parent_struct = utils.get_sptr_by_name(class_name)
    flag = ida_bytes.FF_STRUCT
    mt = ida_nalt.opinfo_t()
    mt.tid = vtables_union_id
    struct = ida_typeinf.tinfo_t(tid=vtables_union_id)
    struct_size = struct.get_size()
    vtables_union_ptr_type = utils.get_typeinf_ptr(vtables_union_name)
    if class_vtable_member:
        logging.info(f"{class_vtable_member=}, {class_vtable_member=}, {offset=}, {flag=}")
        index, mem = parent_struct.get_udm_by_offset(class_vtable_member.offset)
    else:
        index, mem = parent_struct.get_udm_by_offset(offset)
        if index == -1:
            logging.info(f"{class_name=}, {vtables_union_ptr_type=}, {offset=}, {flag=}")
            index, mem = parent_struct.add_udm(get_class_vtable_field_name(class_name), vtables_union_ptr_type, offset, flag)
    logging.info(f"{mem.name=}")
    if is_valid_vtable_name(mem.name):
        logging.info(f"{index=}, {vtables_union_ptr_type=}, {mem.type=}, {flag=}")
        ret = parent_struct.set_udm_type(index, vtables_union_ptr_type, flag | ida_typeinf.TINFO_DEFINITE)
        logging.info(f"{ret}")
        ret = parent_struct.rename_udm(index, get_class_vtable_field_name(class_name))
        logging.info(f"{ret}")
        utils.refresh_struct(parent_struct)
    return vtables_union


def add_child_vtable(parent_name, child_name, child_vtable_id, offset):
    logging.debug(
        "add_child_vtable (%s, %s, %d)",
        parent_name,
        child_name,
        child_vtable_id,
    )
    parent_struct = utils.get_sptr_by_name(parent_name)
    _, parent_vtable_member = parent_struct.get_udm_by_offset(offset)
    vtable_member_tinfo = utils.get_member_tinfo(parent_vtable_member)
    parent_vtable_struct = utils.get_sptr_by_name(get_class_vtable_struct_name(parent_name, offset))
    if parent_vtable_struct is None:
        return
    pointed_struct = utils.extract_struct_from_tinfo(vtable_member_tinfo)
    logging.debug(f"{str(pointed_struct)=}, {str(parent_vtable_struct)=} {str(parent_vtable_member)=}")
    if (
        (pointed_struct is None)
        or (not is_struct_vtable(pointed_struct))
        or (parent_vtable_struct.get_tid() != pointed_struct.get_tid())
    ):
        parent_vtable_member = None
        logging.debug("Not a struct vtable: %s", str(vtable_member_tinfo))

    # TODO: Check that struct is a valid vtable by name
    #if not parent_vtable_struct.is_union():
    #    XXX obsoleted by ida9's own vtable processing
    #    logging.debug("%s vtable isn't union -> unionize it!", parent_name)
    #    parent_vtable_struct = install_vtables_union(
    #        parent_name, parent_vtable_member, vtable_member_tinfo, offset
    #    )

    child_vtable_name = ida_typeinf.tinfo_t(tid=child_vtable_id).get_type_name()
    child_vtable = utils.get_typeinf(child_vtable_name)
    logging.debug(
        "add_to_struct %s %s", parent_vtable_struct.get_tid(), str(child_vtable)
    )
    if ida_typeinf.tinfo_t(tid=child_vtable_id).get_size() == 0:
        utils.add_to_struct(
            ida_typeinf.tinfo_t(tid=child_vtable_id), "dummy", None
        )
    index, new_member = utils.add_to_struct(
        parent_vtable_struct, get_class_vtables_field_name(child_name), child_vtable
    )
#    ida_xref.add_dref(
#        new_member.type.get_tid(), child_vtable_id, ida_xref.XREF_USER | ida_xref.dr_O
#    )
#    ida_xref.add_dref(new_member.id, child_vtable_id, ida_xref.XREF_USER | ida_xref.dr_O)


def update_func_name_with_class(func_ea, class_name, overwrite=False):
    name = idc.get_name(func_ea)
    if name.startswith("sub_"):
        new_name = class_name + VTABLE_DELIMITER + name
        return utils.set_func_name(func_ea, new_name), True
    if overwrite:
        if (demangled := ida_name.demangle_name(name, idaapi.MNG_SHORT_FORM)):
            # 'sentry::Sentry::getDongleIds(sentry::DongleIdList *)' => 'getDongleIds'
            name = demangled.split("(",2)[0].split("::")[-1]
        if "::" in name: # not demangled name may have '::'
            name = name.split("::")[-1]
        if name.startswith("sub_"):
            new_name = class_name + VTABLE_DELIMITER + name
            return utils.set_func_name(func_ea, new_name), True
#    if name.startswith("~"):
#        name = "dtor"
    return name, False


def update_func_this(func_ea, this_type=None, flags=ida_typeinf.TINFO_DEFINITE, overwrite=False):
    functype = None
    try:
        func_details = utils.get_func_details(func_ea)
        logging.info(f"{func_details=}")
        if func_details is None:
            return None
        cc = func_details.get_explicit_cc()
        if cc != idaapi.CM_CC_THISCALL and cc != idaapi.CM_CC_FASTCALL:
            return None
        if this_type and len(func_details) > 0:
            if func_details[0].name == 'this' and not overwrite:
                return None
            func_details[0].name = "this"
            func_details[0].type = this_type
            functype = utils.update_func_details(func_ea, func_details, flags)
            logging.info(f"{functype=}")
    except ida_hexrays.DecompilationFailure as e:
        logging.exception("Couldn't decompile 0x%x", func_ea)
    return functype


def add_class_vtable(struct_ptr, vtable_name, offset=BADADDR, vtable_field_name=None):
    if vtable_field_name is None:
        class_name = struct_ptr.get_type_name()
        vtable_field_name = get_class_vtable_field_name(class_name)
    vtable_id = ida_typeinf.tinfo_t(name=vtable_name).get_tid()
    vtable_type_ptr = utils.get_typeinf_ptr(vtable_name)
    _, new_member = utils.add_to_struct(
        struct_ptr, vtable_field_name, vtable_type_ptr, offset, overwrite=True
    )
    if new_member is None:
        logging.warning(
            "vtable of %s couldn't added at offset 0x%X",
            str(vtable_type_ptr),
            offset,
        )
#    else:
#        ida_xref.add_dref(new_member.type.get_tid(), vtable_id, ida_xref.XREF_USER | ida_xref.dr_O)


@batchmode
def post_func_name_change(new_name, ea):
    """Handle function name change by updating related vtable struct members.
    
    When a function is renamed, this function:
    1. Finds all struct members that reference this function (via data xrefs)
    2. Extracts the last part of the function name (after splitting by VTABLE_DELIMITER)
    3. Converts it to a field name and renames the struct members
    
    Args:
        new_name: The new function name (may contain VTABLE_DELIMITER like "Class::method")
        ea: The function's effective address
    
    Returns:
        tuple: (function_to_call, list_of_args) for batch processing
    """
    # Extract the member name from the function name
    # Split by VTABLE_DELIMITER and use the last part, then convert to field name
    new_field_name = funcname2fieldname(new_name)
    
    # Get data references TO the function (returns list of EAs)
    ref_eas = idautils.DataRefsTo(ea)
    
    args_list = []
    processed_members = set()  # Avoid processing the same member twice
    
    for sid in ref_eas:
        # Avoid processing the same member twice
        if sid in processed_members:
            continue

        processed_members.add(sid)

        udm = ida_typeinf.udm_t()
        tif = ida_typeinf.tinfo_t()
        idx = tif.get_udm_by_tid(udm, sid) # This populates both tif (with struct) and udm (with member details)
        if idx == -1:
            continue
        
        print(f"[.] {tif.get_type_name()}.{udm.name} -> {new_field_name}")
        args_list.append([tif, idx, new_field_name])

    return utils.set_member_name, args_list


def post_struct_member_name_change(member, new_name):
    xrefs = idautils.XrefsFrom(member.type.get_tid())
    xrefs = filter(lambda x: x.type == ida_xref.dr_I and x.user == 1, xrefs)
    for xref in xrefs:
        if utils.is_func(xref.to):
            utils.set_func_name(xref.to, new_name)


def post_struct_member_type_change(member):
    xrefs = idautils.XrefsFrom(member.type.get_tid())
    xrefs = filter(lambda x: x.type == ida_xref.dr_I and x.user == 1, xrefs)
    for xref in xrefs:
        if utils.is_func(xref.to):
            function_ptr_tinfo = utils.get_member_tinfo(member)
            if function_ptr_tinfo.is_funcptr():
                function_tinfo = function_ptr_tinfo.get_pointed_object()
                if function_tinfo is not None:
                    ida_typeinf.apply_tinfo(
                        xref.to, function_tinfo, ida_typeinf.TINFO_DEFINITE
                    )


@batchmode
def post_func_type_change(pfn):
    ea = pfn.start_ea
    xrefs = idautils.XrefsTo(ea, ida_xref.XREF_USER)
    xrefs = list(filter(lambda x: x.type == ida_xref.dr_I and x.user == 1, xrefs))
    args_list = []
    if len(xrefs) == 0:
        return None, []
    try:
        xfunc = ida_hexrays.decompile(ea)
        func_ptr_typeinf = utils.get_typeinf_ptr(xfunc.type)
        for xref in xrefs:
            member = ida_typeinf.udm_t()
            ida_typeinf.tinfo_t().get_udm_by_tid(member, xref.frm)
            struct = ida_typeinf.tinfo_t(tid=xref.frm)
            index, _ = struct.get_udm(0)
            if member is not None and struct is not None:
                args_list.append(
                    [struct, index, func_ptr_typeinf, ida_typeinf.TINFO_DEFINITE]
                )
    except Exception:
        pass
    return ida_typeinf.tinfo_t.set_udm_type, args_list


def make_funcptr_pt(func, this_type):
    return utils.get_typeinf("void (*)(%s *)" % str(this_type))


def fix_userpurge(funcea, flags=ida_typeinf.TINFO_DEFINITE):
    """@return: True if __userpurge calling conv was found and fixed at funcea, otherwise False"""
    funcea = utils.get_func_start(funcea)
    if funcea == BADADDR:
        return False
    tif = utils.get_func_tinfo(funcea)
    if not tif:
        return False
    typestr = str(tif)
    if not typestr:
        return False
    if "__userpurge" not in typestr:
        return False
    typestr = typestr.replace("__userpurge", "(__thiscall)")
    typestr = re.sub(r"\@\<\w+\>", "", typestr)
    py_type = idc.parse_decl(typestr, idc.PT_SILENT)
    if not py_type:
        logging.warn("%08X Failed to fix userpurge", funcea)
        return False
    return idc.apply_type(funcea, py_type[1:], flags)


def funcname2fieldname(name):
    if (demangled := ida_name.demangle_name(name, idaapi.MNG_SHORT_FORM)):
        # 'sentry::Sentry::getDongleIds(sentry::DongleIdList *)' => 'getDongleIds'
        name = demangled.split("(",2)[0].split(VTABLE_DELIMITER)[-1]
    if "::" in name: # not demangled name may have '::' ?
        name = name.split("::")[-1]
    if name.startswith("~"):
        name = "dtor"
    if name.startswith("operator "):
        name = name[9:].strip()
    return name


def update_vtable_struct(
    functions_ea,
    vtable_struct,
    class_name,
    this_type=None,
    get_next_func_callback=get_vtable_line,
    vtable_head=None,
    ignore_list=None,
    add_dummy_member=False,
    parent_name=None,
    add_func_this=True,
    force_rename_vtable_head=False,  # rename vtable head even if it is already named by IDA
    overwrite=False,                 # rename methods AND update this ptr type even if already been named / set
):
    # pylint: disable=too-many-arguments,too-many-locals,too-many-branches
    # TODO: refactor
    if this_type is None:
        this_type = utils.get_typeinf_ptr(class_name)
    if not add_func_this:
        this_type = None
    func, next_func = get_next_func_callback(
        functions_ea,
        ignore_list=ignore_list,
    )
    dummy_i = 1
    function_count = 0
    while func is not None:
        new_func_name, _ = update_func_name_with_class(func, class_name, overwrite=overwrite)
        new_field_name = funcname2fieldname(new_func_name)
        func_ptr = None
        if ida_hexrays.init_hexrays_plugin():
            fix_userpurge(func, ida_typeinf.TINFO_GUESSED)
            update_func_this(func, this_type, ida_typeinf.TINFO_GUESSED, overwrite=overwrite)
            func_ptr = utils.get_typeinf_ptr(utils.get_func_tinfo(func))
        else:
            func_ptr = make_funcptr_pt(func, this_type)  # TODO: maybe try to get or guess type?
        if add_dummy_member:
            utils.add_to_struct(vtable_struct, "dummy_%d" % dummy_i, func_ptr)
            dummy_i += 1
        if not func_ptr:
            func_ptr = ida_typeinf.tinfo_t("void (*)(void)")
        if function_count == 0:
            # We did an hack for vtables contained in union vtable with one dummy member
            _, ptr_member = utils.add_to_struct(
                vtable_struct, new_field_name, func_ptr, 0, overwrite=True
            )
        else:
            _, ptr_member = utils.add_to_struct(
                vtable_struct,
                new_field_name,
                func_ptr,
                function_count * utils.WORD_LEN * utils.BYTE_SIZE,
                is_offset=True,
                overwrite=True
            )
        if ptr_member is None:
            logging.error(
                "Couldn't add %s(%s) to vtable struct 0x%X at offset 0x%X",
                new_field_name,
                str(func_ptr),
                vtable_struct.get_tid(),
            )
        # Get the member TID to add a reference from the struct member to the function EA
        field_idx = vtable_struct.find_udm(ptr_member, 0)
        if field_idx != -1:
            member_tid = vtable_struct.get_udm_tid(field_idx)
            if member_tid != BADADDR:
                ida_xref.add_dref(member_tid, func, ida_xref.XREF_USER | ida_xref.dr_I)
            else:
                logging.warning(
                    "Couldn't get member TID for %s in vtable struct 0x%X",
                    new_field_name,
                    vtable_struct.get_tid(),
                )
        else:
            logging.warning(
                "Couldn't find member index for %s in vtable struct 0x%X",
                new_field_name,
                vtable_struct.get_tid(),
            )
        # Set comment on the member with the function EA
        if field_idx != -1:
            field_cmt = f"{func:08x}"
            vtable_struct.set_udm_cmt(field_idx, field_cmt, False)
        func, next_func = get_next_func_callback(
            next_func, ignore_list=ignore_list
        )
        function_count += 1

    vtable_size = vtable_struct.get_size()

    if vtable_head is None:
        vtable_head = functions_ea
    ida_bytes.del_items(vtable_head, ida_bytes.DELIT_SIMPLE, vtable_size)
    ida_bytes.create_struct(vtable_head, vtable_size, vtable_struct.get_tid())
    if parent_name is None and this_type:
        parent = utils.deref_struct_from_tinfo(this_type)
        parent_name = parent.get_type_name()
        if parent_name == class_name:
            parent_name = None
    utils.set_name_retry(vtable_head, get_vtable_instance_name(class_name, parent_name))


def is_valid_func_char(c):
    ALLOWED_CHARS = [":", "_"]
    return c.isalnum() or c in ALLOWED_CHARS


def find_valid_cppname_in_line(line, idx):
    end_idx = idx
    start_idx = idx
    if len(line) < idx:
        return None
    while start_idx >= 0 and is_valid_func_char(line[start_idx]):
        if line[start_idx] == ":":
            if line[start_idx - 1] == ":":
                start_idx -= 1
            else:
                break
        start_idx -= 1
    while end_idx < len(line) and is_valid_func_char(line[end_idx]):
        if line[end_idx] == ":":
            if line[end_idx + 1] == ":":
                end_idx += 1
            else:
                break
        end_idx += 1
    if end_idx > start_idx:
        return line[start_idx + 1 : end_idx]
    return None


def get_overriden_func_names(union_name, offset, get_not_funcs_members=False):
    sptr = utils.get_sptr_by_name(union_name)
    res = []
    if not sptr.is_union():
        return res

    for i in range(sptr.get_size()):
        idx, member = sptr.get_udm_by_offset(i)
        if member is None: # Added check for None
            continue
        cls = member.name
        tinfo = utils.get_member_tinfo(member)
        logging.debug("Trying %s", cls)
        if cls == get_interface_empty_vtable_name() or not tinfo.is_ptr():
            continue
        pointed_obj = tinfo.get_pointed_object()
        if not pointed_obj.is_struct():
            continue
        vtable_sptr = utils.get_sptr_by_name(pointed_obj.get_final_type_name())
        if vtable_sptr.get_size() <= offset:
            continue
        idx, funcptr_member = vtable_sptr.get_udm_by_offset(offset)
        if funcptr_member is None: # Added check for None
            continue
        funcptr_type = utils.get_member_tinfo(funcptr_member)
        func_name = funcptr_member.name
        if not funcptr_type.is_funcptr() and not get_not_funcs_members:
            continue
        res.append((cls, func_name))
    return res


def set_polymorhpic_func_name(union_name, offset, name, force=False):
    for _, func_name in get_overriden_func_names(union_name, offset):
        func_name_splitted = func_name.split(VTABLE_DELIMITER)
        local_func_name = func_name_splitted[-1]
        if local_func_name != name and (force or local_func_name.startswith("sub_")):
            ea = utils.get_func_ea(func_name)
            if ea != BADADDR:
                new_func_name = VTABLE_DELIMITER.join(func_name_splitted[:-1])
                if new_func_name != "":
                    new_func_name += VTABLE_DELIMITER
                new_func_name += name
                logging.debug("%08X -> %s", ea, new_func_name)
                utils.set_func_name(ea, new_func_name)


def create_vtable_struct(sptr, name, vtable_offset, parent_name=None):
    logging.debug("create_vtable_struct(%s, 0x%X)", name, vtable_offset)
    vtable_details = find_vtable_at_offset(sptr, vtable_offset)
    parent_vtable_member = None
    parent_vtable_struct = None
    parents_chain = None
    if vtable_details is not None:
        logging.debug("Found parent vtable %s 0x%X", name, vtable_offset)
        (
            parent_vtable_member,
            parent_vtable_struct,
            parents_chain,
        ) = vtable_details
    else:
        logging.debug("Couldn't found parent vtable %s %d", name, vtable_offset)
    if parent_vtable_member is not None:
        parent_name = parent_vtable_struct.get_type_name()
    vtable_name = get_class_vtable_struct_name(name, vtable_offset)
    if vtable_offset == 0:
        this_type = utils.get_typeinf_ptr(name)
    else:
        this_type = utils.get_typeinf_ptr(parent_name)
    if vtable_name is None:
        logging.exception(
            "create_vtable_struct(%s, 0x%X): vtable_name is" " None",
            name,
            vtable_offset,
        )
    udt = ida_typeinf.udt_type_data_t()
    vtable_struct = utils.get_or_create_struct(vtable_name)
    if vtable_struct.get_tid() == BADADDR:
        logging.exception("Couldn't create struct %s", vtable_name)
#    if parents_chain:
#        for parent_name, offset in parents_chain:
#            add_child_vtable(parent_name, name, vtable_struct.get_tid(), offset * utils.BYTE_SIZE)
#    else:
    add_class_vtable(sptr, vtable_name, vtable_offset)

    return vtable_struct, this_type


# syntax sugar: make_struct("S40") creates struct of size 0x40
def make_struct(name, struct_size = None, parent_name = None):
    struc = utils.get_or_create_struct(name, parent_name=parent_name)

    if struct_size is None:
        if name.startswith("S"):
            struct_size = int(name[1:], 16)
        else:
            return 0

    cur_size = struc.get_size()
    if cur_size == 1 and struc.get_udm(0)[0] == -1:
        # empty struct get_size() returns 1
        cur_size = 0

    bt_int64 = ida_typeinf.tinfo_t(ida_typeinf.BT_INT64)
    bt_int32 = ida_typeinf.tinfo_t(ida_typeinf.BT_INT32)
    bt_int16 = ida_typeinf.tinfo_t(ida_typeinf.BT_INT16)
    bt_int08 = ida_typeinf.tinfo_t(ida_typeinf.BT_INT8)

    while cur_size < struct_size:
        field_name = "field_" + format(cur_size, "X")
        cur_offset = cur_size * utils.BYTE_SIZE

        if struct_size - cur_size >= 8 and utils.WORD_LEN == 8:
            r = utils.add_to_struct(struc, field_name, bt_int64, cur_offset)
            cur_size += 8

        elif struct_size - cur_size >= 4:
            r = utils.add_to_struct(struc, field_name, bt_int32, cur_offset)
            cur_size += 4

        elif struct_size - cur_size >= 2:
            r = utils.add_to_struct(struc, field_name, bt_int16, cur_offset)
            cur_size += 2

        elif struct_size - cur_size == 1:
            r = utils.add_to_struct(struc, field_name, bt_int08, cur_offset)
            cur_size += 1

        if not r:
            break
    return cur_size


def find_structs_by_size(size = None, min_size: int = 0, ignore_prefixes: list = []):
    """
    Enumerate all defined structures and filter those of a specified size.
    :param size: The size to filter structures by (in bytes).
    :return: A list of tuples (structure_name, structure_id, structure_size).
    """
    if size is None and min_size <= 0:
        raise ValueError("Either size or min_size must be specified")

    matching_structs = []

    # Iterate over all structures in IDA
    for idx in range(ida_struct.get_struc_qty()):
        sid = ida_struct.get_struc_by_idx(idx)
        if sid == BADADDR:
            continue

        struct = ida_struct.get_struc(sid)
        if not struct:
            continue

        # Check the size of the structure
        struct_size = ida_struct.get_struc_size(struct)
        if (size is None and struct_size >= min_size) or (size is not None and struct_size == size):
            name = ida_struct.get_struc_name(sid)
            if not any(name.startswith(prefix) for prefix in ignore_prefixes):
                matching_structs.append(name)

    return matching_structs

def make_vtable(
    class_name,
    struct_size=None,
    vtable_ea=None,
    vtable_ea_stop=None,
    offset_in_class=0,
    parent_name=None,
    add_func_this=True,
    _get_vtable_line=get_vtable_line,
    overwrite=False,
):
    if not vtable_ea and not vtable_ea_stop:
        vtable_ea, vtable_ea_stop = utils.get_selected_range_or_line()
    vtable_struct, this_type = create_vtable_struct(
        utils.get_or_create_struct(class_name, is_class=True, parent_name=parent_name),
        class_name,
        offset_in_class * utils.BYTE_SIZE,
        parent_name=parent_name
    )
    if struct_size:
        make_struct(class_name, struct_size)
    logging.info(f"{vtable_ea=}, {vtable_ea_stop=}, ")
    update_vtable_struct(
        vtable_ea,
        vtable_struct,
        class_name,
        this_type=this_type,
        get_next_func_callback=partial(_get_vtable_line, stop_ea=vtable_ea_stop),
        parent_name=parent_name,
        add_func_this=add_func_this,
        overwrite=overwrite,
    )


def add_baseclass(class_name, baseclass_name, baseclass_offset=0, to_refresh=False):
    member_name = get_base_member_name(baseclass_name, baseclass_offset)
    struct_ptr = utils.get_sptr_by_name(class_name)
    baseclass_ptr = utils.get_sptr_by_name(baseclass_name)
    if not struct_ptr or not baseclass_ptr:
        return False
    _, member = utils.add_to_struct(struct_ptr, member_name,
                                 member_type=utils.get_typeinf(baseclass_name),
                                 offset=baseclass_offset,
                                 overwrite=True)
    if not member:
        logging.debug(
            "add_baseclass(%s. %s): member not found",
            class_name,
            baseclass_name,
        )
        return False
    if to_refresh:
        utils.refresh_struct(struct_ptr)
    return True


@batchmode
def scan_all_vtables():
    """Scan all existing vtable structs and add missing references from members to function EAs.
    
    This function:
    1. Finds all structs that are vtables (by checking if name contains VTABLE_POSTFIX)
    2. For each vtable struct, iterates through all members
    3. For each member that has a comment with an EA, checks if a reference exists
    4. If no reference exists, adds a cross-reference from the member to the function EA
    
    Returns:
        tuple: (total_vtables_processed, total_references_added)
    """
    logging.info("Starting scan for missing vtable member references...")
    
    total_vtables_processed = 0
    total_references_added = 0
    
    # Iterate over all structures in IDA using idautils.Structs()
    for ordinal, sid, struct_name in idautils.Structs():
        if sid == BADADDR:
            continue
        
        # Get struct as tinfo_t to use our helper functions
        vtable_struct = ida_typeinf.tinfo_t()
        if not vtable_struct.get_type_by_tid(sid):
            continue
        
        # Check if this is a vtable struct
        if not is_struct_vtable(vtable_struct):
            continue
        
        # Get struct size - check for None or BADADDR
        struct_size = vtable_struct.get_size()
        if struct_size is None or struct_size == BADADDR or struct_size == 0:
            logging.debug("Skipping vtable struct %s: invalid size (%s)", struct_name, struct_size)
            continue
        
        total_vtables_processed += 1
        logging.debug("Processing vtable struct: %s (size: %d)", struct_name, struct_size)
        
        # Get all members using get_udt_details() - more reliable than iterating by offset
        udt = ida_typeinf.udt_type_data_t()
        if not vtable_struct.get_udt_details(udt):
            logging.debug("Could not get UDT details for %s", struct_name)
            continue
        
        # Iterate through all members
        for member_idx, member in enumerate(udt):
            try:
                # Skip gap members
                if member.is_gap():
                    continue
                
                # Get member ID using idc.get_member_id() - this is the same method IDA uses internally
                # Convert offset from bits to bytes for idc.get_member_id()
                struct_tid = vtable_struct.get_tid()
                member_offset_bytes = member.offset // utils.BYTE_SIZE
                member_tid = idc.get_member_id(struct_tid, member_offset_bytes)
                
                if member_tid == -1 or member_tid == BADADDR:
                    logging.debug(
                        "Could not get member ID for member %d (offset 0x%X bytes) in %s (struct_tid: 0x%X)",
                        member_idx,
                        member_offset_bytes,
                        struct_name,
                        struct_tid
                    )
                    continue
                
                # Check if member is a function pointer
                if not member.type.is_funcptr():
                    continue
                
                # Try to get the function EA from the member comment
                # Comments are set in format: f"{func:08x}"
                # Try to get comment from udm_t object first, then fallback to idc.get_member_cmt()
                member_cmt = None
                if hasattr(member, 'cmt') and member.cmt:
                    member_cmt = member.cmt
                else:
                    # Fallback: use idc.get_member_cmt() with struct TID and member offset
                    member_offset_bytes = member.offset // utils.BYTE_SIZE
                    member_cmt = idc.get_member_cmt(vtable_struct.get_tid(), member_offset_bytes, False)
                
                func_ea = None
                
                if member_cmt:
                    # Try to parse the EA from the comment (format: "08x" hex string)
                    try:
                        func_ea = int(member_cmt, 16)
                        if func_ea == 0 or func_ea == BADADDR:
                            func_ea = None
                    except (ValueError, TypeError):
                        pass
                
                # If we don't have an EA from comment, try to find vtable instance
                # and read the function pointer from memory
                if func_ea is None:
                    func_ea = _find_func_ea_from_vtable_instance(struct_name, member.offset)
                
                if func_ea is None or func_ea == BADADDR:
                    continue
                
                # Verify member_tid is actually a member ID (not a struct ID or other type)
                # Member IDs should be valid and point to a struct member
                if not idc.is_member_id(member_tid):
                    logging.warning(
                        "member_tid 0x%X for %s.%s is not a valid member ID, skipping",
                        member_tid,
                        struct_name,
                        member.name if member.name else f"offset_{member.offset}"
                    )
                    continue
                
                # Always delete any existing xref first to ensure we create a fresh, correct one
                # This fixes cases where xrefs were created with incorrect member_tid
                ida_xref.del_dref(member_tid, func_ea)
                
                # Add the correct reference from the member to the function
                if ida_xref.add_dref(member_tid, func_ea, ida_xref.XREF_USER | ida_xref.dr_I):
                        total_references_added += 1
                        logging.debug(
                            "Added xref from %s.%s (offset 0x%X) to function at 0x%X",
                            struct_name,
                            member.name if member.name else f"offset_{member.offset}",
                            member.offset,
                            func_ea
                        )
                else:
                    logging.warning(
                        "Failed to add xref from %s.%s to 0x%X",
                        struct_name,
                        member.name if member.name else f"offset_{member.offset}",
                        func_ea
                    )
                    
            except Exception as e:
                logging.exception(
                    "Error processing member %d (offset 0x%X) in vtable struct %s: %s",
                    member_idx,
                    member.offset if member else 0,
                    struct_name,
                    e
                )
                continue
    
    logging.info(
        "Completed scan: processed %d vtable structs, added %d missing references",
        total_vtables_processed,
        total_references_added
    )
    
    return total_vtables_processed, total_references_added


def _find_func_ea_from_vtable_instance(vtable_struct_name, member_offset):
    """Try to find the function EA by locating a vtable instance and reading the pointer.
    
    Args:
        vtable_struct_name: Name of the vtable struct
        member_offset: Offset of the member in the struct (in bits, need to convert to bytes)
    
    Returns:
        Function EA if found, None otherwise
    """
    # Extract class name from vtable struct name (remove VTABLE_POSTFIX)
    if VTABLE_POSTFIX not in vtable_struct_name:
        return None
    
    class_name = vtable_struct_name.replace(VTABLE_POSTFIX, "")
    # Handle offset-based vtable names like "Class_0004_vtbl"
    if "_" in class_name:
        parts = class_name.rsplit("_", 1)
        if len(parts) == 2 and len(parts[1]) == 4:
            try:
                int(parts[1], 16)  # Check if it's a hex offset
                class_name = parts[0]
            except ValueError:
                pass
    
    # Try to find vtable instance by name
    vtable_instance_name = get_vtable_instance_name(class_name)
    vtable_ea = ida_name.get_name_ea(BADADDR, vtable_instance_name)
    
    if vtable_ea == BADADDR:
        # Try with parent name variations
        # This is a best-effort approach
        return None
    
    # Convert member offset from bits to bytes
    member_offset_bytes = member_offset // utils.BYTE_SIZE
    
    # Read the function pointer from the vtable instance
    try:
        func_ea = utils.get_ptr(vtable_ea + member_offset_bytes)
        if func_ea and func_ea != BADADDR:
            # Adjust for ARM thumb mode if needed
            if not utils.is_func(func_ea):
                func_ea -= 1
                if not utils.is_func(func_ea):
                    return None
            return func_ea
    except Exception:
        pass
    
    return None
