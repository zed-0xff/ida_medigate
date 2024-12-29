import logging
import re
from functools import partial

import ida_bytes
import ida_hexrays
import ida_name
import ida_struct
import ida_xref
import idc
import idaapi
from idaapi import BADADDR

from . import utils

log = logging.getLogger("ida_medigate")


VTABLE_KEYWORD = "vftable"
VTABLE_UNION_KEYWORD = "VFTABLES"
# VTABLES_UNION_VTABLE_FIELD_POSTFIX = "_vftable"
VTABLES_UNION_VTABLE_FIELD_POSTFIX = ""
VTABLE_DELIMITER = "::"
VTABLE_POSTFIX = "_vftable"
VTABLE_FIELD_NAME = "vfptr"  # Name For vftable * field
VTABLE_INSTANCE_DELIMITER = VTABLE_DELIMITER
VTABLE_INSTANCE_KEYWORD = "vftable"
VTABLE_INSTANCE_POSTFIX = VTABLE_INSTANCE_DELIMITER + VTABLE_INSTANCE_KEYWORD


def get_vtable_instance_name(class_name, parent_name=None):
    name = class_name + VTABLE_INSTANCE_POSTFIX
    if parent_name is not None:
        name += VTABLE_INSTANCE_DELIMITER + parent_name
    return name


def get_base_member_name(parent_name, offset):
    return "%s_%X" % (parent_name, offset)


def get_vtable_line(ea, stop_ea=None, ignore_list=None, pure_virtual_name=None):
    if ignore_list is None:
        ignore_list = []
    func_ea = utils.get_ptr(ea)
    if not utils.is_func_start(func_ea):
        return None, 0
    if stop_ea is not None and ea >= stop_ea:
        return None, 0
    is_pure_func = pure_virtual_name is not None and idc.GetDisasm(ea).endswith(pure_virtual_name)
    if func_ea in ignore_list and not is_pure_func:
        return None, 0
    return func_ea, ea + utils.get_word_len()


def is_valid_vtable_name(member_name):
    return VTABLE_FIELD_NAME in member_name


def is_valid_vtable_type(member, member_type):
    if member_type.is_ptr():
        struct = utils.deref_struct_from_tinfo(member_type)
        return is_struct_vtable(struct)
    return False


def is_member_vtable(member):
    member_type = utils.get_member_tinfo(member)
    member_name = ida_struct.get_member_name(member.id)
    if not is_valid_vtable_name(member_name):
        return False
    if not is_valid_vtable_type(member, member_type):
        return False
    return True


def is_struct_vtable(struct):
    if struct is None:
        return False
    struct_name = ida_struct.get_struc_name(struct.id)
    return VTABLE_POSTFIX in struct_name


def is_vtables_union(union):
    if union is None:
        return False
    if not union.is_union():
        return False
    union_name = ida_struct.get_struc_name(union.id)
    return is_vtables_union_name(union_name)


def is_vtables_union_name(union_name):
    return union_name.endswith(VTABLE_UNION_KEYWORD)


def find_vtable_at_offset(struct_ptr, vtable_offset):
    current_struct = struct_ptr
    current_offset = 0
    member = ida_struct.get_member(current_struct, vtable_offset)
    if member is None:
        return None
    parents_vtables_classes = []
    current_offset += member.get_soff()
    while current_offset < vtable_offset and member is not None:
        current_struct = utils.get_member_substruct(member)
        if current_struct is None:
            return None
        parents_vtables_classes.append(
            [
                ida_struct.get_struc_name(current_struct.id),
                vtable_offset - current_offset,
            ]
        )
        member = ida_struct.get_member(current_struct, vtable_offset - current_offset)
        if member is None:
            log.exception(
                "Couldn't find vtable at offset %d for %d",
                vtable_offset - current_offset,
                struct_ptr.id,
            )
        current_offset += member.get_soff()

    if current_offset != vtable_offset:
        return None

    while member is not None:
        if is_member_vtable(member):
            return member, current_struct, parents_vtables_classes
        current_struct = utils.get_member_substruct(member)
        if current_struct is None:
            return None
        parents_vtables_classes.append([ida_struct.get_struc_name(current_struct.id), 0])
        member = ida_struct.get_member(current_struct, 0)

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


def install_vtables_union(class_name, class_vtable_member=None, vtable_member_tinfo=None, offset=0):
    # pylint: disable=too-many-locals
    # TODO: this function is too big and must be refactored
    log.debug(
        "install_vtables_union(%s, %s, %s)",
        class_name,
        class_vtable_member,
        str(vtable_member_tinfo),
    )
    if class_vtable_member and vtable_member_tinfo:
        old_vtable_sptr = utils.extract_struct_from_tinfo(vtable_member_tinfo)
        old_vtable_class_name = ida_struct.get_struc_name(old_vtable_sptr.id)
    else:
        old_vtable_class_name = get_class_vtable_struct_name(class_name, offset)
        old_vtable_sptr = utils.get_sptr_by_name(old_vtable_class_name)
    vtables_union_name = old_vtable_class_name
    if old_vtable_sptr and not ida_struct.set_struc_name(
        old_vtable_sptr.id, old_vtable_class_name + "_orig"
    ):
        # FIXME: why log exception?
        log.exception(
            "Failed changing %s->%s_orig",
            old_vtable_class_name,
            old_vtable_class_name,
        )
        # FIXME: why -1 and not None?
        return -1
    vtables_union_id = utils.get_or_create_struct_id(vtables_union_name, True)
    vtable_member_tinfo = utils.get_typeinf(old_vtable_class_name + "_orig")
    if vtables_union_id == BADADDR:
        log.exception(
            "Cannot create union vtable for %s()%s",
            class_name,
            vtables_union_name,
        )
        # FIXME: why -1 and not None?
        return -1

    vtables_union = ida_struct.get_struc(vtables_union_id)
    if not vtables_union:
        log.exception("Could retrieve vtables union for %s", class_name)
        # FIXME: return -1?
    if vtable_member_tinfo is not None:
        vtables_union_vtable_field_name = get_class_vtables_field_name(class_name)
    else:
        vtables_union_vtable_field_name = get_interface_empty_vtable_name()
    utils.add_to_struct(vtables_union, vtables_union_vtable_field_name, vtable_member_tinfo)
    parent_struct = utils.get_sptr_by_name(class_name)
    flag = idaapi.FF_STRUCT
    mt = idaapi.opinfo_t()
    mt.tid = vtables_union_id
    struct_size = ida_struct.get_struc_size(vtables_union_id)
    vtables_union_ptr_type = utils.get_typeinf_ptr(vtables_union_name)
    if class_vtable_member:
        member_ptr = class_vtable_member
    else:
        # FIXME: add_struc_member returns error code, not member id
        member_id = ida_struct.add_struc_member(
            parent_struct,
            get_class_vtable_field_name(class_name),
            offset,
            flag,
            mt,
            struct_size,
        )
        # FIXME: get_member_by_id returns tuple, not member ptr
        member_ptr = ida_struct.get_member_by_id(member_id)
    ida_struct.set_member_tinfo(
        parent_struct,
        member_ptr,
        0,
        vtables_union_ptr_type,
        idaapi.TINFO_DEFINITE,
    )
    # FIXME: might be None! Is this OK, considering we return -1 everywhere else?
    return vtables_union


def add_child_vtable(parent_name, child_name, child_vtable_id, offset):
    log.debug(
        "add_child_vtable (%s, %s, %d)",
        parent_name,
        child_name,
        child_vtable_id,
    )
    parent_vtable_member = ida_struct.get_member(utils.get_sptr_by_name(parent_name), offset)
    vtable_member_tinfo = utils.get_member_tinfo(parent_vtable_member)
    parent_vtable_struct = utils.get_sptr_by_name(get_class_vtable_struct_name(parent_name, offset))
    if parent_vtable_struct is None:
        return
    pointed_struct = utils.extract_struct_from_tinfo(vtable_member_tinfo)
    log.debug("pointed_struct: %s", str(pointed_struct))
    if (
        (pointed_struct is None)
        or (not is_struct_vtable(pointed_struct))
        or (parent_vtable_struct.id != pointed_struct.id)
    ):
        parent_vtable_member = None
        log.debug("Not a struct vtable: %s", str(vtable_member_tinfo))

    # TODO: Check that struct is a valid vtable by name
    if not parent_vtable_struct.is_union():
        log.debug("%s vtable isn't union -> unionize it!", parent_name)
        parent_vtable_struct = install_vtables_union(
            parent_name, parent_vtable_member, vtable_member_tinfo, offset
        )

    child_vtable_name = ida_struct.get_struc_name(child_vtable_id)
    child_vtable = utils.get_typeinf(child_vtable_name)
    log.debug("add_to_struct %d %s", parent_vtable_struct.id, str(child_vtable))
    if ida_struct.get_struc_size(child_vtable_id) == 0:
        utils.add_to_struct(ida_struct.get_struc(child_vtable_id), "dummy", None)
    new_member = utils.add_to_struct(
        parent_vtable_struct,
        get_class_vtables_field_name(child_name),
        child_vtable,
    )
    ida_xref.add_dref(new_member.id, child_vtable_id, ida_xref.XREF_USER | ida_xref.dr_O)


def update_func_name_with_class(func_ea, class_name):
    name = idc.get_name(func_ea)
    if name.startswith("sub_"):
        new_name = class_name + VTABLE_DELIMITER + name
        return utils.set_func_name(func_ea, new_name), True
    return name, False


def update_func_this(func_ea, this_type=None, flags=idc.TINFO_DEFINITE):
    #if idc.get_tinfo(func_ea) is not None:
    #    # don't touch any user defined type
    #    return False
    func_details = utils.get_func_details(func_ea)
    if not func_details:
        return False
    if func_details.cc != idaapi.CM_CC_THISCALL and func_details.cc != idaapi.CM_CC_FASTCALL:
        return False
    func_details[0].name = "this"
    if this_type:
        func_details[0].type = this_type
    return utils.apply_func_details(func_ea, func_details, flags)


def add_class_vtable(struct_ptr, vtable_name, offset=BADADDR, vtable_field_name=None):
    if vtable_field_name is None:
        class_name = ida_struct.get_struc_name(struct_ptr.id)
        vtable_field_name = get_class_vtable_field_name(class_name)
    vtable_id = ida_struct.get_struc_id(vtable_name)
    vtable_type_ptr = utils.get_typeinf_ptr(vtable_name)
    new_member = utils.add_to_struct(
        struct_ptr, vtable_field_name, vtable_type_ptr, offset, overwrite=True
    )
    if new_member is None:
        log.warning(
            "vtable of %s couldn't added at offset 0x%X",
            str(vtable_type_ptr),
            offset,
        )
    else:
        ida_xref.add_dref(new_member.id, vtable_id, ida_xref.XREF_USER | ida_xref.dr_O)


def make_funcptr_pt(func, this_type):
    return utils.get_typeinf("void (*)(%s *)" % str(this_type))


def fix_userpurge(funcea, flags=idc.TINFO_DEFINITE):
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
    PT_SILENT = 1  # in IDA7.0 idc.PT_SILENT=2, which is incorrect
    py_type = idc.parse_decl(typestr, PT_SILENT)
    if not py_type:
        log.warn("%08X Failed to fix userpurge", funcea)
        return False
    return idc.apply_type(funcea, py_type[1:], flags)


def update_vtable_struct(
    functions_ea,
    vtable_struct,
    class_name,
    this_type=None,
    get_next_func_callback=get_vtable_line,
    vtable_head=None,
    ignore_list=None,
    add_dummy_member=False,
    pure_virtual_name=None,
    parent_name=None,
    add_func_this=True,
    force_rename_vtable_head=False,  # rename vtable head even if it is already named by IDA
    # if it's not named, then it will be renamed anyway
):
    # pylint: disable=too-many-arguments,too-many-locals,too-many-branches
    # TODO: refactor
    if this_type is None:
        this_type = utils.get_typeinf_ptr(class_name)
    if not add_func_this:
        this_type = None
    func_ea, next_func = get_next_func_callback(
        functions_ea,
        ignore_list=ignore_list,
        pure_virtual_name=pure_virtual_name,
    )
    dummy_i = 1
    offset = 0
    while func_ea is not None:
        new_func_name, _ = update_func_name_with_class(func_ea, class_name)
        func_ptr = None
        if ida_hexrays.init_hexrays_plugin():
            fix_userpurge(func_ea, idc.TINFO_DEFINITE)
            update_func_this(func_ea, this_type, idc.TINFO_DEFINITE)
            func_ptr = utils.get_typeinf_ptr(utils.get_func_tinfo(func_ea))
        else:
            func_ptr = make_funcptr_pt(func_ea, this_type)  # TODO: maybe try to get or guess type?
        if add_dummy_member:
            utils.add_to_struct(vtable_struct, "dummy_%d" % dummy_i, func_ptr)
            dummy_i += 1
            offset += utils.get_word_len()
        ptr_member = utils.add_to_struct(
            vtable_struct, new_func_name, func_ptr, offset, overwrite=True, is_offs=True
        )
        if ptr_member is None:
            log.error(
                "Couldn't add %s(%s) to vtable struct 0x%X at offset 0x%X",
                new_func_name,
                str(func_ptr),
                vtable_struct.id,
                offset,
            )
        offset += utils.get_word_len()
        if not ida_xref.add_dref(ptr_member.id, func_ea, ida_xref.XREF_USER | ida_xref.dr_I):
            log.warn(
                "Couldn't create xref between member %s and func %s",
                ida_struct.get_member_name(ptr_member.id),
                idc.get_name(func_ea),
            )
        func_ea, next_func = get_next_func_callback(
            next_func,
            ignore_list=ignore_list,
            pure_virtual_name=pure_virtual_name,
        )

    vtable_size = ida_struct.get_struc_size(vtable_struct)

    if vtable_head is None:
        vtable_head = functions_ea
    # ida_bytes.del_items(vtable_head, ida_bytes.DELIT_SIMPLE, vtable_size)
    ida_bytes.create_struct(vtable_head, vtable_size, vtable_struct.id)
    if not idc.hasUserName(idc.get_full_flags(vtable_head)) or force_rename_vtable_head:
        if parent_name is None and this_type:
            parent = utils.deref_struct_from_tinfo(this_type)
            parent_name = ida_struct.get_struc_name(parent.id)
            if parent_name == class_name:
                parent_name = None
        idc.set_name(
            vtable_head,
            get_vtable_instance_name(class_name, parent_name),
            ida_name.SN_CHECK | ida_name.SN_FORCE,
        )


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
    if not sptr.is_union:
        return res

    for i in range(ida_struct.get_max_offset(sptr)):
        member = ida_struct.get_member(sptr, i)
        cls = ida_struct.get_member_name(member.id)
        tinfo = utils.get_member_tinfo(member)
        log.debug("Trying %s", cls)
        if cls == get_interface_empty_vtable_name() or not tinfo.is_ptr():
            continue
        pointed_obj = tinfo.get_pointed_object()
        if not pointed_obj.is_struct():
            continue
        vtable_sptr = utils.get_sptr_by_name(pointed_obj.get_final_type_name())
        if ida_struct.get_max_offset(vtable_sptr) <= offset:
            continue
        funcptr_member = ida_struct.get_member(vtable_sptr, offset)
        funcptr_type = utils.get_member_tinfo(funcptr_member)
        func_name = ida_struct.get_member_name(funcptr_member.id)
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
                log.debug("%08X -> %s", ea, new_func_name)
                utils.set_func_name(ea, new_func_name)


def create_class(class_name, has_vtable, parent_class=None):
    class_id = ida_struct.add_struc(BADADDR, class_name)
    class_ptr = ida_struct.get_struc(class_id)
    # if parent class ->
    # if has_vtable-> if not parent- create vtable, if parent - install vtable
    return class_ptr


def create_vtable_struct(sptr, name, vtable_offset, parent_name=None):
    log.debug("create_vtable_struct(%s, 0x%X)", name, vtable_offset)
    vtable_details = find_vtable_at_offset(sptr, vtable_offset)
    parent_vtable_member = None
    parent_vtable_struct = None
    parents_chain = None
    if vtable_details is not None:
        log.debug("Found parent vtable %s 0x%X", name, vtable_offset)
        (
            parent_vtable_member,
            parent_vtable_struct,
            parents_chain,
        ) = vtable_details
    else:
        log.debug("Couldn't found parent vtable %s 0x%X", name, vtable_offset)
    if parent_vtable_struct is not None and parent_vtable_member is not None:
        parent_name = ida_struct.get_struc_name(parent_vtable_struct.id)
    vtable_name = get_class_vtable_struct_name(name, vtable_offset)
    if vtable_offset == 0:
        this_type = utils.get_typeinf_ptr(name)
    else:
        this_type = utils.get_typeinf_ptr(parent_name)
    if vtable_name is None:
        log.exception(
            "create_vtable_struct(%s, 0x%X): vtable_name is" " None",
            name,
            vtable_offset,
        )
        return None, this_type
    vtable_id = ida_struct.get_struc_id(vtable_name)
    if vtable_id == BADADDR:
        vtable_id = ida_struct.add_struc(BADADDR, vtable_name, False)
    if vtable_id == BADADDR:
        log.exception("Couldn't create vtable struct %s", vtable_name)
        return None, this_type
    vtable_struct = ida_struct.get_struc(vtable_id)
    assert vtable_struct
    if parents_chain:
        for v_parent_name, offset in parents_chain:
            add_child_vtable(v_parent_name, name, vtable_id, offset)
    else:
        add_class_vtable(sptr, vtable_name, vtable_offset)

    return vtable_struct, this_type


def make_vtable(
    class_name,
    vtable_ea=None,
    vtable_ea_stop=None,
    offset_in_class=0,
    parent_name=None,
    add_func_this=True,
    _get_vtable_line=get_vtable_line,
):
    if not vtable_ea and not vtable_ea_stop:
        vtable_ea, vtable_ea_stop = utils.get_selected_range_or_line()
    vtable_struct, this_type = create_vtable_struct(
        utils.get_or_create_struct(class_name),
        class_name,
        offset_in_class,
        parent_name=parent_name,
    )
    if not vtable_struct:
        return
    update_vtable_struct(
        vtable_ea,
        vtable_struct,
        class_name,
        this_type=this_type,
        get_next_func_callback=partial(_get_vtable_line, stop_ea=vtable_ea_stop),
        parent_name=parent_name,
        add_func_this=add_func_this,
    )


def add_baseclass(class_name, baseclass_name, baseclass_offset=0, to_refresh=False):
    member_name = get_base_member_name(baseclass_name, baseclass_offset)
    struct_ptr = utils.get_sptr_by_name(class_name)
    baseclass_ptr = utils.get_sptr_by_name(baseclass_name)
    if not struct_ptr or not baseclass_ptr:
        return False
    member = utils.add_to_struct(
        struct_ptr,
        member_name,
        member_tif=utils.get_typeinf(baseclass_name),
        offset=baseclass_offset,
        overwrite=True,
    )
    if not member:
        log.debug(
            "add_baseclass(%s. %s): member not found",
            class_name,
            baseclass_name,
        )
        return False
    try:
        member.props |= ida_struct.MF_BASECLASS
        if to_refresh:
            utils.refresh_struct(struct_ptr)
    except AttributeError:
        # ida_struct.MF_BASECLASS does not exist in IDA 7.0
        pass
    return True
