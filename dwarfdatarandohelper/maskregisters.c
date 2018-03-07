#include <fcntl.h>     /* For open() */
#include <stdlib.h>     /* For exit() */
#include <unistd.h>     /* For close() */
#include <stdio.h>

#include <libnet.h>
#include <stdbool.h>
#include <libdwarf.h>
#include <dwarf.h>




static void read_cu_list(Dwarf_Debug dbg);

static void printSubprogramDetails(Dwarf_Debug dbg, Dwarf_Die print_me);

static void get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die, int in_level, Dwarf_Die parent_sub_program);

static void check_if_local_var(Dwarf_Debug dbg, Dwarf_Die print_me, Dwarf_Die parent_sub_program);




struct MaskRegisterLocation {
    unsigned long long program_counter;
    unsigned long long dwarf_format_register; //Need mapping with corresponding target ABI
    unsigned long long number_of_bytes_in_reg; //expecting this to be the only operation required to calculate the mask
//    unsigned long long effectiveMask;
//    unsigned long long originalMask;
    bool isValid;
};

static void
get_symbol_addr(Dwarf_Debug dgb, Dwarf_Die the_die, Dwarf_Addr subprogram_base_addr, Dwarf_Addr targetPC,
                struct MaskRegisterLocation *MaskLocation);
static bool getLocationResult(struct MaskRegisterLocation* maskLocation, Dwarf_Loc *op);


static Dwarf_Addr targetPC;

int
main(int argc, char **argv) {

    Dwarf_Debug dbg = 0;
    int fd = -1;
    const char *filepath = NULL;
    int res = DW_DLV_ERROR;
    Dwarf_Error error;
    Dwarf_Handler errhand = 0;
    Dwarf_Ptr errarg = 0;

    if (argc < 3) {
        printf("Not reading from stdin...! Usage: ./maskregisters binary_path <program_counter_in_hex_format_end_with_null_char>");
        return (0);
    } else {
        filepath = argv[1];
        fd = open(filepath, O_RDONLY);
        char *PC_VAL =  argv[2];
        targetPC = (Dwarf_Addr)strtol(PC_VAL, NULL, 16);
    }

    if (fd < 0) {
        printf("Failure attempting to open %s\n", filepath);
    }

    res = dwarf_init(fd, DW_DLC_READ, errhand, errarg, &dbg, &error);
    if (res != DW_DLV_OK) {
        printf("Giving up, cannot do DWARF processing\n");
        exit(1);
    }

    read_cu_list(dbg);

    res = dwarf_finish(dbg, &error);
    if (res != DW_DLV_OK) {
        printf("dwarf_finish failed!\n");
    }
    close(fd);
    return 0;
}

static void
read_cu_list(Dwarf_Debug dbg) {
    Dwarf_Unsigned cu_header_length = 0;
    Dwarf_Half version_stamp = 0;
    Dwarf_Unsigned abbrev_offset = 0;
    Dwarf_Half address_size = 0;
    Dwarf_Unsigned next_cu_header = 0;
    Dwarf_Error error;
    int cu_number = 0;

    for (;; ++cu_number) {
        Dwarf_Die no_die = 0;
        Dwarf_Die cu_die = 0;
        int res = DW_DLV_ERROR;
        res = dwarf_next_cu_header(dbg, &cu_header_length,
                                   &version_stamp, &abbrev_offset, &address_size,
                                   &next_cu_header, &error);
//        current_CU_base_addr

        if (res == DW_DLV_ERROR) {
            printf("Error in dwarf_next_cu_header\n");
            exit(1);
        }
        if (res == DW_DLV_NO_ENTRY) {
            printf("DONE\n");
            /* Done. */
            return;
        }
        /* The CU will have a single sibling, a cu_die. */
        res = dwarf_siblingof(dbg, no_die, &cu_die, &error);
        if (res == DW_DLV_ERROR) {
            printf("Error in dwarf_siblingof on CU die \n");
            exit(1);
        }
        if (res == DW_DLV_NO_ENTRY) {
            /* Impossible case. */
            printf("no entry! in dwarf_siblingof on CU die \n");
            exit(1);
        }

        get_die_and_siblings(dbg, cu_die, 0, NULL);

        dwarf_dealloc(dbg, cu_die, DW_DLA_DIE);

    }
}

static void
get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die, int in_level, Dwarf_Die parent_sub_program) {
    int res = DW_DLV_ERROR;
    Dwarf_Die cur_die = in_die;
    Dwarf_Die sib_die = in_die;
    Dwarf_Die child = 0;
    Dwarf_Error error;

    res = dwarf_child(cur_die, &child, &error);
    check_if_local_var(dbg, child, cur_die);
    if (res == DW_DLV_OK) { //DFS discovery of DIE continues here
        get_die_and_siblings(dbg, child, in_level + 1, in_die); /* recur on the first son */
        sib_die = child;
        while (res == DW_DLV_OK) {
            Dwarf_Die temp_sib_die = sib_die;
            res = dwarf_siblingof(dbg, temp_sib_die, &sib_die, &error);
            check_if_local_var(dbg, sib_die, cur_die);
            get_die_and_siblings(dbg, sib_die, in_level + 1, in_die); /* recur others */
        };

    }


    return;
}

static int isSubprogramDIE(Dwarf_Die die) {
    Dwarf_Error error = 0;
    Dwarf_Half tag = 0;
    const char *tagname = 0;
    int got_tag_name = !dwarf_tag(die, &tag, &error) && dwarf_get_TAG_name(tag, &tagname);
    return (tag == 46);
}

static void printSubprogramDetails(Dwarf_Debug dbg, Dwarf_Die print_me) {

    char *name = 0;
    Dwarf_Error error = 0;
    Dwarf_Half tag = 0;
    const char *tagname = 0;

    Dwarf_Bool bAttr;
    Dwarf_Attribute attr;

    Dwarf_Unsigned in_line;
    Dwarf_Unsigned in_file = 0;

    Dwarf_Locdesc *loc_list;
    Dwarf_Signed num_loc;

    Dwarf_Off ptr_address = 0;

    int has_line_data = !dwarf_hasattr(print_me, DW_AT_decl_line, &bAttr, &error) && bAttr;
    int got_name = !dwarf_diename(print_me, &name, &error);
    int got_line = !dwarf_attr(print_me, DW_AT_decl_line, &attr, &error) && !dwarf_formudata(attr, &in_line, &error);
    int got_file = !dwarf_attr(print_me, DW_AT_decl_file, &attr, &error) && !dwarf_formudata(attr, &in_file, &error);
    int got_loclist = !dwarf_hasattr(print_me, DW_AT_location, &bAttr, &error) &&
                      !dwarf_attr(print_me, DW_AT_location, &attr, &error)
                      && !dwarf_loclist(attr, &loc_list, &num_loc, &error);

    int got_tag_name = !dwarf_tag(print_me, &tag, &error) && dwarf_get_TAG_name(tag, &tagname);
    if (tag == 46) {
        printf("<%llu:%llu> tag: %d %s  name: %s \n", in_file, in_line, tag, tagname, name);
    }
    dwarf_dealloc(dbg, name, DW_DLA_STRING);

}

static void
get_symbol_addr(Dwarf_Debug dgb, Dwarf_Die the_die, Dwarf_Addr subprogram_base_addr, Dwarf_Addr targetPC,
                struct MaskRegisterLocation *MaskLocation) {

    Dwarf_Error err;
    Dwarf_Attribute *attrs;
    Dwarf_Addr lowpc, highpc;
    Dwarf_Signed attrcount, i;

    if (dwarf_attrlist(the_die, &attrs, &attrcount, &err) != DW_DLV_OK)
        printf("Error in dwarf_attlist\n");

    for (i = 0; i < attrcount; ++i) {
        Dwarf_Half attrcode;
        if (dwarf_whatattr(attrs[i], &attrcode, &err) != DW_DLV_OK)
            printf("Error in dwarf_whatattr\n");

        /* Take lowpc (function entry) */
        if (attrcode == DW_AT_low_pc)
            dwarf_formaddr(attrs[i], &lowpc, &err);

            /* Take highpc just for fun!*/
        else if (attrcode == DW_AT_high_pc)
            dwarf_highpc(the_die, &highpc, &err);

        if (attrcode == DW_AT_location) {
//            Dwarf_Half form;
//            Dwarf_Error form_err;
//            dwarf_whatform(attrs[i], &form, &form_err);
//            if (form_err != DW_DLV_OK) {
//                printf("Failed to process location for the MASK_VARIABLE");
//                exit(-1); //$TODO$ handle gracefully
//            }

//            if (form == DW_FORM_exprloc) {
//
//                //$TODO$ Need to handle this
//            }

//            dwarf_formexprloc()
//            $TODO$ Assuming loclistptr for now. if(form == DW_FORM_CLASS_LOCLISTPTR) {
//
//            }



            Dwarf_Signed lcount = 0;
            Dwarf_Locdesc **llbuf = 0;
            Dwarf_Error error = 0;
            int lres = 0;
            lres = dwarf_loclist_n(attrs[i], &llbuf, &lcount, &error);

            if (lres == DW_DLV_OK) {
                Dwarf_Signed dwarf_signed = 0;
                Dwarf_Addr relativeTargetPC = targetPC - subprogram_base_addr;
                for (dwarf_signed = 0; dwarf_signed < lcount; dwarf_signed++) {
                    /*  Use llbuf[i]. Both Dwarf_Locdesc and the
                        array of Dwarf_Loc it points to are
                        defined in libdwarf.h: they are
                        not opaque structs. */
                    Dwarf_Half no_of_ops = 0;
                    struct esb_s *string_out;
                    if (llbuf[dwarf_signed]->ld_lopc <= relativeTargetPC && llbuf[dwarf_signed]->ld_hipc >= relativeTargetPC) {
                        printf("Major milestone if you see this! \n");
                        no_of_ops = llbuf[dwarf_signed]->ld_cents;
                        Dwarf_Loc *op = &llbuf[dwarf_signed]->ld_s[0];

                        bool IsRegisterLocationOp = getLocationResult(MaskLocation, op);
                        if(!IsRegisterLocationOp) {
                            printf("Not a register location; \n");
                        } else {

                            if (no_of_ops > 2) {
                                printf("unexpected state; We handle only 2 DWARF operations for register locations! Requires investigation. \n");
                            } else {
                                MaskLocation->isValid = true;
                                MaskLocation->program_counter = targetPC;
                                Dwarf_Small target_op = op->lr_atom;
                                unsigned i = 1;
                                for (i = 1; i < no_of_ops; i++) {
                                    op = &llbuf[dwarf_signed]->ld_s[i];
                                    Dwarf_Small target_op = op->lr_atom;
                                    switch (target_op) {
                                        case DW_OP_piece:
                                            MaskLocation->number_of_bytes_in_reg = op->lr_number;
                                            break;
                                        default:
                                            printf("Unhandled DWARF OP ::[%c]", target_op);
                                    }
                                }
                            }
                        }
                    }
                    dwarf_dealloc(dgb, llbuf[dwarf_signed]->ld_s, DW_DLA_LOC_BLOCK);
                    dwarf_dealloc(dgb, llbuf[dwarf_signed], DW_DLA_LOCDESC);
                }
                dwarf_dealloc(dgb, llbuf, DW_DLA_LIST);
            }
        }
    }
}

static bool getLocationResult(struct MaskRegisterLocation *maskLocation, Dwarf_Loc *op) {
    Dwarf_Small target_op = op->lr_atom;

    switch (target_op) {
        case DW_OP_reg0: //rax
        case DW_OP_reg1: //rdx
        case DW_OP_reg2:
        case DW_OP_reg3:
        case DW_OP_reg4:
        case DW_OP_reg5:
//        case DW_OP_reg6:
//        case DW_OP_reg7:
        case DW_OP_reg8:
        case DW_OP_reg9:
        case DW_OP_reg10:
        case DW_OP_reg11:
        case DW_OP_reg12:
        case DW_OP_reg13:
        case DW_OP_reg14:
        case DW_OP_reg15:
//        case DW_OP_reg16:
//        case DW_OP_reg17:
//        case DW_OP_reg18:
//        case DW_OP_reg19:
//        case DW_OP_reg20:
//        case DW_OP_reg21:
//        case DW_OP_reg22:
//        case DW_OP_reg23:
//        case DW_OP_reg24:
//        case DW_OP_reg25:
//        case DW_OP_reg26:
//        case DW_OP_reg27:
//        case DW_OP_reg28:
//        case DW_OP_reg29:
//        case DW_OP_reg30:
//        case DW_OP_reg31:
            maskLocation->dwarf_format_register = target_op;
            maskLocation->isValid = true;
            printf("ONE OF 32 REGISTERS \n");
            return true;
//        case DW_OP_regx:
//            printf("DW_OP_regx LOCATION");
//            //$TODO$ handle next parameter to identify location
//            maskLocation->dwarf_format_register = target_op;
//            maskLocation->isValid = true;
//            return true;
        default:
            printf("Handle non register location op \n");
            break;
    }
    return false;
}


static void check_if_local_var(Dwarf_Debug dbg, Dwarf_Die print_me, Dwarf_Die parent_sub_program) {
//    Dwarf_Addr targetPC = 0x4023a0;
//    Dwarf_Addr targetPC = 0x402356;
    char *name = 0;
    Dwarf_Error error = 0;
    Dwarf_Half tag = 0;
    const char *tagname = 0;
    Dwarf_Line *line;

    Dwarf_Bool bAttr;
    Dwarf_Attribute attr;
    int res = 0;
    Dwarf_Unsigned in_line;
    Dwarf_Unsigned in_file = 0;

    Dwarf_Locdesc *loc_list;
    Dwarf_Signed num_loc;

    Dwarf_Off ptr_address = 0;

    int has_line_data = !dwarf_hasattr(print_me, DW_AT_decl_line, &bAttr, &error) && bAttr;
//    if(has_line_data){

    /* Here we know that we have debug information for line numbers
       in this compilation unit. Let's keep working */

    /* Using short-circuiting to ensure all steps are done in order; if a chain finishes, we know we have stored our values */
    int got_name = !dwarf_diename(print_me, &name, &error);
    int got_line = !dwarf_attr(print_me, DW_AT_decl_line, &attr, &error) && !dwarf_formudata(attr, &in_line, &error);
    int got_file = !dwarf_attr(print_me, DW_AT_decl_file, &attr, &error) && !dwarf_formudata(attr, &in_file, &error);
    int got_loclist = !dwarf_hasattr(print_me, DW_AT_location, &bAttr, &error) &&
                      !dwarf_attr(print_me, DW_AT_location, &attr, &error)
                      && !dwarf_loclist(attr, &loc_list, &num_loc, &error);

    int got_tag_name = !dwarf_tag(print_me, &tag, &error) && dwarf_get_TAG_name(tag, &tagname);

    if (name != NULL && (strstr(name, "DATARANDO_DEBUG_HELP") != NULL)) {

        //Found Variable

        printf("tag: %d %s  name: %s \n", tag, tagname, name);
        /* Location lists are structs; see ftp://ftp.sgi.com/sgi/dwarf/libdwarf.h */
        if (got_loclist && loc_list[0].ld_cents == 1) {
            printf("<%llu:%llu> tag: %d %s  name: %s loc: %lld\n", in_file, in_line, tag, tagname, name,
                   loc_list[0].ld_s[0].lr_number);
        }

        //$TODO$ Get parent subprogram's range
        //$TODO$ take current program counter at checkpoint as input
        //$TODO$ check if the program counter falls within the current subprogram's range

        Dwarf_Addr start;
        Dwarf_Addr end;
        Dwarf_Error err;

        int got_low_pc = !dwarf_lowpc(parent_sub_program, &start, &err);
        if (!got_low_pc) {
            printf("Base address not found! Returning from processing \n");
            return;
        }

        struct MaskRegisterLocation location;

        get_symbol_addr(dbg, print_me, start, targetPC, &location);

        if(location.isValid) {
            printf("Found a register \n");
            printf("\n");
            printf("pc: 0x%llu dwarf_format_register: 0x%llu number_of_bytes_in_reg: 0x%llu\n", location.program_counter, location.dwarf_format_register, location.number_of_bytes_in_reg);
        }

//        get_symbol_addr(dbg, parent_sub_program);
//        0x4023a0

        printSubprogramDetails(dbg, parent_sub_program);



        int got_high_pc = !dwarf_highpc(parent_sub_program, &end, &err);




        if (got_high_pc) {
            printf("highpc[%llu] \n", end);
        }

//        printSubprogramDetails(dbg, parent_sub_program);
//                Dwarf_Addr offset = *parent_sub_program->offset;
    }

    dwarf_dealloc(dbg, name, DW_DLA_STRING);
}