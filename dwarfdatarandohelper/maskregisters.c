#include <fcntl.h>     /* For open() */
#include <stdlib.h>     /* For exit() */
#include <unistd.h>     /* For close() */
#include <stdio.h>

#include <libnet.h>
#include <stdbool.h>
#include <libdwarf.h>
#include <dwarf.h>

static void read_cu_list(Dwarf_Debug dbg);

static void get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die, int in_level, Dwarf_Die parent_sub_program);

static void check_if_local_var(Dwarf_Debug dbg, Dwarf_Die print_me, Dwarf_Die parent_sub_program);

static int deal_with_fdes(Dwarf_Debug dbg);

struct MaskRegisterLocation {
  unsigned long long program_counter;
  unsigned long long dwarf_format_register; //Need mapping with corresponding target ABI
  unsigned long long number_of_bytes_in_reg; //expecting this to be the only operation required to calculate the mask
//    unsigned long long effectiveMask;
//    unsigned long long originalMask;
  unsigned int isValid;
};

static void
get_symbol_addr(Dwarf_Debug dgb, Dwarf_Die the_die, Dwarf_Addr subprogram_base_addr, Dwarf_Addr targetPC,
                char *variable_name);

static bool getLocationResult(struct MaskRegisterLocation *maskLocation, Dwarf_Loc *op);


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
    char *PC_VAL = argv[2];
    targetPC = (Dwarf_Addr) strtol(PC_VAL, NULL, 16);
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

  deal_with_fdes(dbg);
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


static void
get_symbol_addr(Dwarf_Debug dgb, Dwarf_Die the_die, Dwarf_Addr subprogram_base_addr, Dwarf_Addr targetPC, char *name) {

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
      //$TODO$ Assuming loclistptr for now. if(form == DW_FORM_CLASS_LOCLISTPTR). Other forms might be encountered e.g., DW_FORM_exprloc
      Dwarf_Signed lcount = 0;
      Dwarf_Locdesc **llbuf = 0;
      Dwarf_Error error = 0;
      int lres = dwarf_loclist_n(attrs[i], &llbuf, &lcount, &error);
      if (lres == DW_DLV_OK) {
        Dwarf_Signed dwarf_signed = 0;
        for (dwarf_signed = 0; dwarf_signed < lcount; dwarf_signed++) {
          Dwarf_Half no_of_ops = llbuf[dwarf_signed]->ld_cents;
          Dwarf_Loc *op = &llbuf[dwarf_signed]->ld_s[0];
          struct MaskRegisterLocation *MaskLocation;
          bool IsRegisterLocationOp = getLocationResult(MaskLocation, op);
          if (IsRegisterLocationOp) {
            if (no_of_ops > 2) {
              printf("unexpected state; We handle only 2 DWARF operations for register locations! Requires investigation. \n");
            } else {
              MaskLocation->program_counter = targetPC;
              if(no_of_ops == 2) {
                op = &llbuf[dwarf_signed]->ld_s[1];
                Dwarf_Small target_op = op->lr_atom;
                switch (target_op) {
                  case DW_OP_piece:
                    MaskLocation->number_of_bytes_in_reg = op->lr_number;
                    break;
                  default:
                    printf("Unhandled DWARF OP ::[%c]", target_op);
                }
              } else {
                MaskLocation->number_of_bytes_in_reg = 0;
              }
              printf("%s pc: 0x%llx dwarf_format_register: 0x%llx number_of_bytes_in_reg: 0x%llx low_pc: 0x%llx high_pc: 0x%llx\n",
                     name,
                     MaskLocation->program_counter,
                     MaskLocation->dwarf_format_register,
                     MaskLocation->number_of_bytes_in_reg,
                     (subprogram_base_addr + llbuf[dwarf_signed]->ld_lopc),
                     (subprogram_base_addr + llbuf[dwarf_signed]->ld_hipc));
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
  unsigned int target_op = op->lr_atom;

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
      maskLocation->isValid = 1;
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
  int got_name = !dwarf_diename(print_me, &name, &error);
  int got_line = !dwarf_attr(print_me, DW_AT_decl_line, &attr, &error) && !dwarf_formudata(attr, &in_line, &error);
  int got_file = !dwarf_attr(print_me, DW_AT_decl_file, &attr, &error) && !dwarf_formudata(attr, &in_file, &error);
  int got_loclist = !dwarf_hasattr(print_me, DW_AT_location, &bAttr, &error) &&
                    !dwarf_attr(print_me, DW_AT_location, &attr, &error)
                    && !dwarf_loclist(attr, &loc_list, &num_loc, &error);

  int got_tag_name = !dwarf_tag(print_me, &tag, &error) && dwarf_get_TAG_name(tag, &tagname);

  //$TODO$ arg_mask formal parameters hold masks as well. Both in registers and in stack.
  if (name != NULL && (strstr(name, "DATARANDO_DEBUG_HELP") != NULL   /*|| strstr(name, "arg_mask") != NULL*/)) {
    //Found Variable
    printf("tag: %d %s  name: %s \n", tag, tagname, name);

    /* Location lists are structs; see ftp://ftp.sgi.com/sgi/dwarf/libdwarf.h */
    if (got_loclist && loc_list[0].ld_cents == 1) {
      printf("<%llu:%llu> tag: %d %s  name: %s loc: %lld\n", in_file, in_line, tag, tagname, name,
             loc_list[0].ld_s[0].lr_number);
    }

    Dwarf_Addr start;
    Dwarf_Error err;

    int got_low_pc = !dwarf_lowpc(parent_sub_program, &start, &err);
    if (!got_low_pc) {
      printf("Base address not found! Returning from processing \n");
      return;
    }
    get_symbol_addr(dbg, print_me, start, targetPC, name);
  }

  dwarf_dealloc(dbg, name, DW_DLA_STRING);
}

static void read_frame_data(Dwarf_Debug dbg);

static void print_fde_instrs(Dwarf_Debug dbg, Dwarf_Fde fde,
                             Dwarf_Error *error, Dwarf_Signed fdenum);

static void print_regtable(Dwarf_Regtable3 *tab3);

static void print_cie_instrs(Dwarf_Cie cie, Dwarf_Error *error);

#define UNDEF_VAL 2000
#define SAME_VAL 2001
#define CFA_VAL 2002

static int deal_with_fdes(Dwarf_Debug dbg) {
  int regtabrulecount = 0;
  regtabrulecount = 1999;
  dwarf_set_frame_undefined_value(dbg, UNDEF_VAL);
  dwarf_set_frame_rule_initial_value(dbg, UNDEF_VAL);
  dwarf_set_frame_same_value(dbg, SAME_VAL);
  dwarf_set_frame_cfa_value(dbg, CFA_VAL);
  dwarf_set_frame_rule_table_size(dbg, regtabrulecount);

  read_frame_data(dbg);

//    Dwarf_Cie *cie_data = NULL;
//    Dwarf_Signed cie_element_count = 0;
//    Dwarf_Fde *fde_data = NULL;
//    Dwarf_Signed fde_element_count = 0;
//    Dwarf_Error err;
//    int res = dwarf_get_fde_list_eh(dbg, &cie_data,
//                                    &cie_element_count, &fde_data,
//                                    &fde_element_count, &err);
//    if (res != DW_DLV_OK) {
//        printf("Error Code: %d ", res);
//    }

}


static void
read_frame_data(Dwarf_Debug dbg) {
  Dwarf_Error error;
  Dwarf_Signed cie_element_count = 0;
  Dwarf_Signed fde_element_count = 0;
  Dwarf_Cie *cie_data = 0;
  Dwarf_Fde *fde_data = 0;
  int res = DW_DLV_ERROR;
  Dwarf_Signed fdenum = 0;


  /*  If you wish to read .eh_frame data, use
      dwarf_get_fde_list_eh() instead.  */
  res = dwarf_get_fde_list(dbg, &cie_data, &cie_element_count,
                           &fde_data, &fde_element_count, &error);
  if (res == DW_DLV_NO_ENTRY) {
    printf("No .debug_frame data present\n");
    printf("Try dwarf_get_fde_list_eh() to read .eh_frame data\n");
    res = dwarf_get_fde_list_eh(dbg, &cie_data, &cie_element_count,
                                &fde_data, &fde_element_count, &error);
    if (res == DW_DLV_NO_ENTRY) {
      printf("failed");
      exit(0);
    }
  }
  if (res == DW_DLV_ERROR) {
    printf("Error reading frame data ");
    exit(1);
  }
  printf("%" DW_PR_DSd " cies present. "
                 "%" DW_PR_DSd " fdes present. \n",
         cie_element_count, fde_element_count);
  /*if(fdenum >= fde_element_count) {
      printf("Want fde %d but only %" DW_PR_DSd " present\n",fdenum,
          fde_element_count);
      exit(1);
  }*/

  for (fdenum = 0; fdenum < fde_element_count; ++fdenum) {
    Dwarf_Cie cie = 0;
//        printf("Print cie of fde %" DW_PR_DSd  "\n",fdenum);
//        res = dwarf_get_cie_of_fde(fde_data[fdenum],&cie,&error);
//        if(res != DW_DLV_OK) {
//            printf("Error accessing fdenum %" DW_PR_DSd
//                " to get its cie\n",fdenum);
//            exit(1);
//        }
//        print_cie_instrs(cie,&error);
//        printf("Print fde %" DW_PR_DSd  "\n",fdenum);
    print_fde_instrs(dbg, fde_data[fdenum], &error, fdenum);
  }

  /* Done with the data. */
  dwarf_fde_cie_list_dealloc(dbg, cie_data, cie_element_count,
                             fde_data, fde_element_count);
  return;
}

static void
print_cie_instrs(Dwarf_Cie cie, Dwarf_Error *error) {
  int res = DW_DLV_ERROR;
  Dwarf_Unsigned bytes_in_cie = 0;
  Dwarf_Small version = 0;
  char *augmentation = 0;
  Dwarf_Unsigned code_alignment_factor = 0;
  Dwarf_Signed data_alignment_factor = 0;
  Dwarf_Half return_address_register_rule = 0;
  Dwarf_Ptr instrp = 0;
  Dwarf_Unsigned instr_len = 0;

  res = dwarf_get_cie_info(cie, &bytes_in_cie,
                           &version, &augmentation, &code_alignment_factor,
                           &data_alignment_factor, &return_address_register_rule,
                           &instrp, &instr_len, error);
  if (res != DW_DLV_OK) {
    printf("Unable to get cie info!\n");
    exit(1);
  }
}

static void
print_frame_instrs(Dwarf_Frame_Op *frame_op_list,
                   Dwarf_Signed frame_op_count) {
  Dwarf_Signed i = 0;
  printf("Base op. Ext op. Reg. Offset. Instr-offset.\n");
  for (i = 0; i < frame_op_count; ++i) {
    printf("[%" DW_PR_DSd "]", i);
    printf(" %d. ", frame_op_list[i].fp_base_op);
    printf(" %d. ", frame_op_list[i].fp_extended_op);
    printf(" %" DW_PR_DSd ". ", frame_op_list[i].fp_offset);
    printf(" 0x%" DW_PR_DUx ". ", frame_op_list[i].fp_instr_offset);
    printf("\n");
  }
}

static void
print_fde_instrs(Dwarf_Debug dbg,
                 Dwarf_Fde fde, Dwarf_Error *error, Dwarf_Signed fdenum) {
  int res;
  Dwarf_Addr lowpc = 0;
  Dwarf_Unsigned func_length = 0;
  Dwarf_Ptr fde_bytes;
  Dwarf_Unsigned fde_byte_length = 0;
  Dwarf_Off cie_offset = 0;
  Dwarf_Signed cie_index = 0;
  Dwarf_Off fde_offset = 0;
  Dwarf_Addr arbitrary_addr = 0;
  Dwarf_Addr actual_pc = 0;
  Dwarf_Regtable3 tab3;
  int oldrulecount = 0;
  Dwarf_Ptr outinstrs = 0;
  Dwarf_Unsigned instrslen = 0;
  Dwarf_Frame_Op *frame_op_list = 0;
  Dwarf_Signed frame_op_count = 0;
  Dwarf_Cie cie = 0;


  res = dwarf_get_fde_range(fde, &lowpc, &func_length, &fde_bytes,
                            &fde_byte_length, &cie_offset, &cie_index, &fde_offset, error);
  if (res != DW_DLV_OK) {
    printf("Problem getting fde range \n");
    exit(1);
  }

//    arbitrary_addr = lowpc + (func_length/2);
  arbitrary_addr = 0x402356;
  if (lowpc < arbitrary_addr && arbitrary_addr < (lowpc + func_length)) {

    printf("Print cie of fde %" DW_PR_DSd  "\n", fdenum);
    res = dwarf_get_cie_of_fde(fde, &cie, error);
    if (res != DW_DLV_OK) {
      printf("Error accessing fdenum %" DW_PR_DSd
                     " to get its cie\n", fdenum);
      exit(1);
    }
    print_cie_instrs(cie, error);
    printf("Print fde %" DW_PR_DSd  "\n", fdenum);

    printf("function low pc 0x%" DW_PR_DUx
                   "  and length 0x%" DW_PR_DUx
                   "  and addr we choose 0x%" DW_PR_DUx
                   "\n",
           lowpc, func_length, arbitrary_addr);

    /*  1 is arbitrary. We are winding up getting the
        rule count here while leaving things unchanged. */
    oldrulecount = dwarf_set_frame_rule_table_size(dbg, 1);
    dwarf_set_frame_rule_table_size(dbg, oldrulecount);

    tab3.rt3_reg_table_size = oldrulecount;
    tab3.rt3_rules = (struct Dwarf_Regtable_Entry3_s *) malloc(
            sizeof(struct Dwarf_Regtable_Entry3_s) * oldrulecount);
    if (!tab3.rt3_rules) {
      printf("Unable to malloc for %d rules\n", oldrulecount);
      exit(1);
    }

    res = dwarf_get_fde_info_for_all_regs3(fde, arbitrary_addr,
                                           &tab3, &actual_pc, error);

    if (res != DW_DLV_OK) {
      printf("dwarf_get_fde_info_for_all_regs3 failed!\n");
      exit(1);
    }
    print_regtable(&tab3);

    res = dwarf_get_fde_instr_bytes(fde, &outinstrs, &instrslen, error);
    if (res != DW_DLV_OK) {
      printf("dwarf_get_fde_instr_bytes failed!\n");
      exit(1);
    }
    res = dwarf_get_cie_of_fde(fde, &cie, error);
    if (res != DW_DLV_OK) {
      printf("Error getting cie from fde\n");
      exit(1);
    }

    res = dwarf_expand_frame_instructions(cie,
                                          outinstrs, instrslen, &frame_op_list,
                                          &frame_op_count, error);
    if (res != DW_DLV_OK) {
      printf("dwarf_expand_frame_instructions failed!\n");
      exit(1);
    }
    printf("Frame op count: %" DW_PR_DUu "\n", frame_op_count);
    print_frame_instrs(frame_op_list, frame_op_count);

    dwarf_dealloc(dbg, frame_op_list, DW_DLA_FRAME_BLOCK);
    free(tab3.rt3_rules);
  }
}

static void
print_reg(int r) {
  switch (r) {
    case SAME_VAL:
      printf(" %d SAME_VAL ", r);
      break;
    case UNDEF_VAL:
      printf(" %d UNDEF_VAL ", r);
      break;
    case CFA_VAL:
      printf(" %d (CFA) ", r);
      break;
    default:
      printf(" r%d ", r);
      break;
  }
}

static void
print_one_regentry(const char *prefix,
                   struct Dwarf_Regtable_Entry3_s *entry) {
  int is_cfa = !strcmp("cfa", prefix);
  printf("%s ", prefix);
  printf("type: %d %s ",
         entry->dw_value_type,
         (entry->dw_value_type == DW_EXPR_OFFSET) ? "DW_EXPR_OFFSET" :
         (entry->dw_value_type == DW_EXPR_VAL_OFFSET) ? "DW_EXPR_VAL_OFFSET" :
         (entry->dw_value_type == DW_EXPR_EXPRESSION) ? "DW_EXPR_EXPRESSION" :
         (entry->dw_value_type == DW_EXPR_VAL_EXPRESSION) ?
         "DW_EXPR_VAL_EXPRESSION" :
         "Unknown");
  switch (entry->dw_value_type) {
    case DW_EXPR_OFFSET:
      print_reg(entry->dw_regnum);
      printf(" offset_rel? %d ", entry->dw_offset_relevant);
      if (entry->dw_offset_relevant) {
        printf(" offset  %" DW_PR_DSd " ",
               entry->dw_offset_or_block_len);
        if (is_cfa) {
          printf("defines cfa value");
        } else {
          printf("address of value is CFA plus signed offset");
        }
        if (!is_cfa && entry->dw_regnum != CFA_VAL) {
          printf(" compiler botch, regnum != CFA_VAL");
        }
      } else {
        printf("value in register");
      }
      break;
    case DW_EXPR_VAL_OFFSET:
      print_reg(entry->dw_regnum);
      printf(" offset  %" DW_PR_DSd " ",
             entry->dw_offset_or_block_len);
      if (is_cfa) {
        printf("does this make sense? No?");
      } else {
        printf("value at CFA plus signed offset");
      }
      if (!is_cfa && entry->dw_regnum != CFA_VAL) {
        printf(" compiler botch, regnum != CFA_VAL");
      }
      break;
    case DW_EXPR_EXPRESSION:
      print_reg(entry->dw_regnum);
      printf(" offset_rel? %d ", entry->dw_offset_relevant);
      printf(" offset  %" DW_PR_DSd " ",
             entry->dw_offset_or_block_len);
      printf("Block ptr set? %s ", entry->dw_block_ptr ? "yes" : "no");
      printf(" Value is at address given by expr val ");
      /* printf(" block-ptr  0x%" DW_PR_DUx " ",
          (Dwarf_Unsigned)entry->dw_block_ptr); */
      break;
    case DW_EXPR_VAL_EXPRESSION:
      printf(" expression byte len  %" DW_PR_DSd " ",
             entry->dw_offset_or_block_len);
      printf("Block ptr set? %s ", entry->dw_block_ptr ? "yes" : "no");
      printf(" Value is expr val ");
      if (!entry->dw_block_ptr) {
        printf("Compiler botch. ");
      }
      /* printf(" block-ptr  0x%" DW_PR_DUx " ",
          (Dwarf_Unsigned)entry->dw_block_ptr); */
      break;
  }
  printf("\n");
}

static void
print_regtable(Dwarf_Regtable3 *tab3) {
  int r;
  /* We won't print too much. A bit arbitrary. */
  int max = 32;
  if (max > tab3->rt3_reg_table_size) {
    max = tab3->rt3_reg_table_size;
  }
  print_one_regentry("cfa", &tab3->rt3_cfa_rule);

  for (r = 0; r < max; r++) {
    char rn[30];
    snprintf(rn, sizeof(rn), "reg %d", r);
    print_one_regentry(rn, tab3->rt3_rules + r);
  }


}




