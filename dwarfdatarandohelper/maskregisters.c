#include <fcntl.h>     /* For open() */
#include <stdlib.h>     /* For exit() */
#include <unistd.h>     /* For close() */
#include <stdio.h>

#include <libnet.h>
#include <stdbool.h>
#include <libdwarf.h>
#include <dwarf.h>
#include "../dwarfdump/esb.h"

static void read_cu_list(Dwarf_Debug dbg);

struct SubRoutineList {
  Dwarf_Die *die;
  struct SubRoutineList *parent;
};

static void get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die, int in_level, Dwarf_Die parent_sub_program, struct SubRoutineList *parent_chain);

static void check_if_local_var(Dwarf_Debug dbg, Dwarf_Die print_me, Dwarf_Die parent_sub_program, struct SubRoutineList *parentRef);
static bool check_if_inlined_function(Dwarf_Debug dbg, Dwarf_Die parent_sub_program);
static int
get_abstract_origin_variable_name(Dwarf_Debug dbg,Dwarf_Attribute attr, Dwarf_Die *origin_die,
                                  char *name_out, unsigned maxlen);
static int deal_with_fdes(Dwarf_Debug dbg);

static void handle_regtable(Dwarf_Regtable3 *tab3);

static void print_one_regentry(const char *prefix,
                   struct Dwarf_Regtable_Entry3_s *entry,
                   int registerNumber);

static void getCFAlocation(struct Dwarf_Regtable_Entry3_s *entry);
struct MaskRegisterLocation {
  unsigned long long program_counter;
  unsigned long long dwarf_format_register; //Need mapping with corresponding target ABI
  unsigned long long number_of_bytes_in_reg; //expecting this to be the only operation required to calculate the mask
//    unsigned long long effectiveMask;
//    unsigned long long originalMask;
  unsigned int isRegisterBasedAddressing;
  unsigned long long offset;
};

static void get_symbol_addr(Dwarf_Debug dgb,
                            Dwarf_Die the_die,
                            Dwarf_Addr subprogram_base_addr,
                            Dwarf_Addr targetPC,
                            char *variable_name);

static bool getLocationResult(struct MaskRegisterLocation *maskLocation, Dwarf_Loc *op);


static Dwarf_Addr targetPC;



static Dwarf_Die getNonInlinedParent(struct SubRoutineList *subRoutineList) {
  while(subRoutineList->parent) {
    Dwarf_Die *parent = subRoutineList->parent->die;
    if(parent) {
      Dwarf_Error error = 0;
      Dwarf_Half parent_tag = 0;
      int got_parent_tag = !dwarf_tag(*parent, &parent_tag, &error);
      if (got_parent_tag && parent_tag == DW_TAG_subprogram) {
        return *parent;
      }
      if(subRoutineList->parent->parent != NULL) {
        subRoutineList = subRoutineList->parent->parent;
      } else {
        break;
      }
    }
  }
}


int
main(int argc, char **argv) {

  Dwarf_Debug dbg = 0;
  int fd = -1;
  const char *filepath = NULL;
  int res = DW_DLV_ERROR;
  Dwarf_Error error;
  Dwarf_Handler errhand = 0;
  Dwarf_Ptr errarg = 0;
  bool isFrameProcessingRequired = false;
  if (argc < 4) {
    printf("Not reading from stdin...! Usage: ./maskregisters binary_path <program_counter_in_hex_format_end_with_null_char>");
    return (0);
  } else {
    filepath = argv[1];
    fd = open(filepath, O_RDONLY);
    char *PC_VAL = argv[2];
    targetPC = (Dwarf_Addr) strtol(PC_VAL, NULL, 16);

    char *Frame_Info = argv[3];
    if(strstr(Frame_Info, "processfde") != NULL) {
      isFrameProcessingRequired = true;
    }
  }

  if (fd < 0) {
    printf("Failure attempting to open %s\n", filepath);
  }

  res = dwarf_init(fd, DW_DLC_READ, errhand, errarg, &dbg, &error);
  if (res != DW_DLV_OK) {
    printf("Giving up, cannot do DWARF processing\n");
    exit(EXIT_FAILURE);
  }
  if(!isFrameProcessingRequired) {
    read_cu_list(dbg);
  } else {
    deal_with_fdes(dbg);
  }

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
      exit(EXIT_FAILURE);
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
      exit(EXIT_FAILURE);
    }
    if (res == DW_DLV_NO_ENTRY) {
      /* Impossible case. */
      printf("no entry! in dwarf_siblingof on CU die \n");
      exit(EXIT_FAILURE);
    }
//    struct SubRoutineList *parentChain =(struct SubRoutineList*)malloc(sizeof(struct SubRoutineList)) ;
    get_die_and_siblings(dbg, cu_die, 0, NULL, NULL);
    //$TODO$ free parentChain
    dwarf_dealloc(dbg, cu_die, DW_DLA_DIE);

  }
}

static void freeParentChain(Dwarf_Debug dbg, struct SubRoutineList *node) {
  if(node == NULL) {
    return;
  }
  if(node->die != NULL) {
    dwarf_dealloc(dbg, node->die, DW_DLA_DIE);
  }
  freeParentChain(dbg, node->parent);
  if(node->parent != NULL) {
    free(node->parent);
  }
  if(node != NULL) {
    free(node);
  }
}


static void
get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die, int in_level, Dwarf_Die parent, struct SubRoutineList *parentChain) {
  int res = DW_DLV_ERROR;
  Dwarf_Die cur_die = in_die;
//  Dwarf_Die sib_die = in_die;
  Dwarf_Die child = 0;
  Dwarf_Error error;
  Dwarf_Error *errp = 0;
  for(;;) {
    Dwarf_Die sib_die = 0;
    res = dwarf_child(cur_die, &child, errp);

    if(res == DW_DLV_ERROR) {
      printf("Error in dwarf_child , level %d \n",in_level);
      exit(1);
    }
    if(res == DW_DLV_OK) {
      struct SubRoutineList *parentRef = parentChain;
      bool isInlindFunc = check_if_inlined_function(dbg, child);
      if(isInlindFunc) {
        Dwarf_Die *c = (Dwarf_Die *) malloc(sizeof(Dwarf_Die));
        struct SubRoutineList *subRoutineList = (struct SubRoutineList *) malloc(sizeof(struct SubRoutineList));
        *c = child;
        subRoutineList->die = c;
        subRoutineList->parent = (struct SubRoutineList *) malloc(sizeof(struct SubRoutineList));
        Dwarf_Die *actual_parent = (Dwarf_Die *) malloc(sizeof(Dwarf_Die));
        *actual_parent=cur_die;
        subRoutineList->parent->die = actual_parent;
        subRoutineList->parent->parent = parentRef;
        parentRef = subRoutineList;
      }

      check_if_local_var(dbg, child, cur_die, parentRef);
      get_die_and_siblings(dbg,child,
                           in_level+1, cur_die, parentRef);
      //$TODO$ free parentRef
      /* No longer need 'child' die. */
      dwarf_dealloc(dbg,child,DW_DLA_DIE);
      child = 0;
    }
    /* res == DW_DLV_NO_ENTRY or DW_DLV_OK */
    res = dwarf_siblingof_b(dbg,cur_die, 1, &sib_die,errp);
    if(res == DW_DLV_OK) {
      int next_abbrev_code = dwarf_die_abbrev_code(sib_die);
      struct SubRoutineList *parentRef = parentChain;
      bool isInlindFunc = check_if_inlined_function(dbg, sib_die);
      if(isInlindFunc) {
        Dwarf_Die *c = (Dwarf_Die *) malloc(sizeof(Dwarf_Die));
        struct SubRoutineList *subRoutineList = (struct SubRoutineList *) malloc(sizeof(struct SubRoutineList));
        *c = sib_die;
        subRoutineList->die = c;
        subRoutineList->parent = (struct SubRoutineList *) malloc(sizeof(struct SubRoutineList));
        Dwarf_Die *actual_parent = (Dwarf_Die *) malloc(sizeof(Dwarf_Die));
        *actual_parent=parent;
        subRoutineList->parent->die = actual_parent;
        subRoutineList->parent->parent = parentRef;
        parentRef = subRoutineList;
        parentChain = subRoutineList;
      }
      check_if_local_var(dbg, sib_die, parent, parentRef);
      //$TODO$ free parentRef
    }
    if(res == DW_DLV_ERROR) {
      char *em = errp?dwarf_errmsg(error):"Error siblingof_b";
      printf("Error in dwarf_siblingof_b , level %d :%s \n",
             in_level,em);
      exit(1);
    }
    if(res == DW_DLV_NO_ENTRY) {
      /* Done at this level. */
      break;
    }
    int next_abbrev_code = dwarf_die_abbrev_code(sib_die);
    /* res == DW_DLV_OK */
    if(cur_die != in_die) {
      dwarf_dealloc(dbg,cur_die,DW_DLA_DIE);
      cur_die = 0;
    }
    cur_die = sib_die;
  }
  

//  res = dwarf_child(cur_die, &child, &error);
//  if (res == DW_DLV_OK) { //DFS discovery of DIE continues here
//    check_if_local_var(dbg, child, cur_die);
//    get_die_and_siblings(dbg, child, in_level + 1); /* recur on the first son */
//    sib_die = child;
//    while (res == DW_DLV_OK) {
//      Dwarf_Die temp_sib_die = sib_die;
//      res = dwarf_siblingof(dbg, temp_sib_die, &sib_die, &error);
//      check_if_local_var(dbg, sib_die, cur_die);
//      get_die_and_siblings(dbg, sib_die, in_level + 1); /* recur others */
//    };
//
//  }
//  return;
//  freeParentChain(dbg, parentChain);
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
          struct MaskRegisterLocation *MaskLocation = (struct MaskRegisterLocation *)malloc(sizeof(struct MaskRegisterLocation));
          MaskLocation->isRegisterBasedAddressing = false;
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
                if(op->lr_atom >= DW_OP_breg0 && op->lr_atom <= DW_OP_breg31) {
                  MaskLocation->dwarf_format_register = (unsigned long long int) (op->lr_atom - 32);
                  MaskLocation->offset = op->lr_number;
                  //Not the only register based operation
                  MaskLocation->isRegisterBasedAddressing = true;
                }
              }
              printf("%s pc: 0x%llx dwarf_format_register: 0x%llx number_of_bytes_in_reg: 0x%llx low_pc: 0x%llx high_pc: 0x%llx offset: 0x%llx isRegisterBased: %s\n",
                     name,
                     MaskLocation->program_counter,
                     MaskLocation->dwarf_format_register,
                     MaskLocation->number_of_bytes_in_reg,
                     (subprogram_base_addr + llbuf[dwarf_signed]->ld_lopc),
                     (subprogram_base_addr + llbuf[dwarf_signed]->ld_hipc),
                     MaskLocation->offset,
                     (MaskLocation->isRegisterBasedAddressing) ? "true" : "false"
              );
            }
          } else {
//            free(MaskLocation);
//              printf("Stored in stack; Handle stack ops %s\n", name);
//            //$TODO$ Handle stack ops
//            exit(EXIT_FAILURE);
          }
          free(MaskLocation);
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
    case DW_OP_reg6:
      printf("Stored in Reg6; Handle stack ops\n");
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
      return true;
    case DW_OP_dup:
    case DW_OP_drop:
    case DW_OP_pick:
    case DW_OP_over:
    case DW_OP_swap:
    case DW_OP_rot:
    case DW_OP_deref:
    case DW_OP_deref_size:
    case DW_OP_xderef:
    case DW_OP_push_object_address:
    case DW_OP_form_tls_address:
    case DW_OP_call_frame_cfa:
      printf("Stored in stack; Handle stack ops\n");
      break;

//        case DW_OP_regx:
//            printf("DW_OP_regx LOCATION");
//            //$TODO$ handle next parameter to identify location
//            maskLocation->dwarf_format_register = target_op;
//            return true;
    default:
      if(target_op >= DW_OP_breg0 && target_op <= DW_OP_breg31) {
        printf("Register based addressing; \n");
        return true;
      }
      if(target_op == DW_OP_fbreg){
        printf("Register based addressing; fbreg \n");
      }

//      printf("Handle non register location op \n");
//      exit(EXIT_FAILURE);
      return false;
//      break;
  }
  return false;
}

static bool check_if_inlined_function(Dwarf_Debug dbg, Dwarf_Die print_me) {
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
  if(tag == DW_TAG_inlined_subroutine || tag == DW_TAG_lexical_block) {
    printf("tag: %d %s  name: %s abbrev: %d\n", tag, tagname, name, dwarf_die_abbrev_code(print_me));
    return true;
  }
  return false;
}
///home/prabhu/emt_proj/repos/test/exp2/target_apps/test_datarando_refresh2

static void check_if_local_var(Dwarf_Debug dbg, Dwarf_Die print_me, Dwarf_Die parent_die, struct SubRoutineList *parentRef) {
//    Dwarf_Addr targetPC = 0x4023a0;
//    Dwarf_Addr targetPC = 0x402356;
  char *name = 0;
  Dwarf_Error error = 0;
  Dwarf_Half tag = 0;
  Dwarf_Half parent_tag = 0;
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

  int got_tag_name = !dwarf_tag(print_me, &tag, &error) && !dwarf_get_TAG_name(tag, &tagname);



  char *origin_name = (char *)malloc(100);

  Dwarf_Attribute abstract_origin;

  Dwarf_Die parent_sub_program = parent_die;
  if(got_tag_name && tag == DW_TAG_variable) {
    int got_parent_tag = !dwarf_tag(parent_die, &parent_tag, &error);
    if (got_parent_tag && parent_tag == DW_TAG_inlined_subroutine) {

      int got_abstract_origin_attr = !dwarf_attr(print_me, DW_AT_abstract_origin, &abstract_origin, &error);
      if (got_abstract_origin_attr) {
        if(name == NULL) {
          Dwarf_Die *origin_die = (Dwarf_Die *) malloc(sizeof(Dwarf_Die *));
          get_abstract_origin_variable_name(dbg, abstract_origin, origin_die, origin_name, 80);
          printf("origin name: %s\n", origin_name);
          name = origin_name;
          dwarf_dealloc(dbg, origin_die, DW_DLA_DIE);
        }
      }
      struct SubRoutineList *temp = parentRef;
      while (temp != NULL) {
        got_parent_tag = !dwarf_tag(*temp->die, &parent_tag, &error);
        if(got_parent_tag && parent_tag == DW_TAG_lexical_block) {
          printf("Found scope we cannot process for:: [%s]\n", origin_name);
          return;
        }
        if(got_parent_tag && parent_tag == DW_TAG_subprogram) {
          parent_sub_program = *temp->die;
          break;
        }
        temp = temp->parent;
      }
    }
  }


//$TODO$ arg_mask formal parameters hold masks as well. Both in registers and in stack.
  if (name != NULL && (strstr(name, "DATARANDO_DEBUG_HELP") != NULL   /*|| strstr(name, "arg_mask") != NULL*/)) {
    Dwarf_Unsigned inline_val;
    char *parent_name = 0;
    int got_parent_name = !dwarf_diename(parent_sub_program, &parent_name, &error);
    int got_inline = !dwarf_attr(parent_sub_program, DW_AT_inline, &attr, &error) && !dwarf_formudata(attr, &inline_val, &error);
    if(got_inline && inline_val == 1) {
      if(got_parent_name) {
        char *target_fun = "cfar";
        if(strncmp(parent_name, target_fun, 4) == 0) {
          printf("put breakpoint now \n");
        }
        printf("Inside Inlined Function: [%s] ", parent_name);
      }
      printf("Ignoring this instance name: %s \n", name);
    } else {
      char *target_string="cfar_check_fd";
      if(strcmp(parent_name, target_string) == 0) {
        printf("Found inlined function");
      }
      //Found Variable
      printf("tag: %d %s  name: %s parent_function: %s\n", tag, tagname, name, parent_name);

      /* Location lists are structs; see ftp://ftp.sgi.com/sgi/dwarf/libdwarf.h */
      if (got_loclist && loc_list[0].ld_cents == 1) {
        printf("<%llu:%llu> tag: %d %s  name: %s loc: %lld\n", in_file, in_line, tag, tagname, name,
               loc_list[0].ld_s[0].lr_number);
      }

      Dwarf_Addr start;
      Dwarf_Error err;

      int got_low_pc = !dwarf_lowpc(parent_sub_program, &start, &err);
      if (!got_low_pc) {
        Dwarf_Attribute attrib = 0;
        int has_range_attr = !dwarf_hasattr(print_me, DW_AT_ranges, &bAttr, &error) && bAttr;
        if(has_range_attr) {
//          dwarf_attr(parent_sub_program, DW_AT_inline, &attrib, &error);
//          Dwarf_Half theform = 0;
//
//          struct esb_s rangesstr;
//          esb_constructor(&rangesstr);
//
//          int rv = dwarf_whatform(attrib, &theform, &error);
//          if (rv == DW_DLV_ERROR) {
//            printf("Range attribute form error\n");
//            exit(EXIT_FAILURE);
//          } else if (rv == DW_DLV_NO_ENTRY) {
//            esb_destructor(&rangesstr);
//            printf("Range attribute with no entry\n");
//            exit(EXIT_FAILURE);
//          }
//
//          esb_empty_string(&rangesstr);
//
////          get_attr_value(dbg, tag, NULL,
////                         0, attrib, NULL, 0, &rangesstr,
////                         FALSE, verbose);
////          print_range_attribute(dbg, die, attr, attr_in, theform,
////                                pd_dwarf_names_print_on_error, print_information,
////                                &append_extra_string,
////                                &esb_extra);
////          esb_empty_string(&valname);
////          esb_append(&valname, esb_get_string(&rangesstr));
//          esb_destructor(&rangesstr);
          printf("Handle rangestr \n");

        } else {
          printf("Base address not found! Returning from processing \n");
          exit(EXIT_FAILURE);
        }
      }
      get_symbol_addr(dbg, print_me, start, targetPC, name);
    }
  }

  dwarf_dealloc(dbg, name, DW_DLA_STRING);
  dwarf_dealloc(dbg, origin_name, DW_DLA_STRING);
}

static void read_frame_data(Dwarf_Debug dbg);

static void print_fde_instrs(Dwarf_Debug dbg, Dwarf_Fde fde,
                             Dwarf_Error *error, Dwarf_Signed fdenum);

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
      printf("failed. Expecting frame info");
      exit(EXIT_FAILURE);
    }
  }
  if (res == DW_DLV_ERROR) {
    printf("Error reading frame data ");
    exit(EXIT_FAILURE);
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
    exit(EXIT_FAILURE);
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
    exit(EXIT_FAILURE);
  }

//    arbitrary_addr = lowpc + (func_length/2);
  //targetPC in this context is the return address
//  targetPC = 0x402347;
  if (lowpc < targetPC && targetPC < (lowpc + func_length)) {

    printf("Print cie of fde %" DW_PR_DSd  "\n", fdenum);
    res = dwarf_get_cie_of_fde(fde, &cie, error);
    if (res != DW_DLV_OK) {
      printf("Error accessing fdenum %" DW_PR_DSd
                     " to get its cie\n", fdenum);
      exit(EXIT_FAILURE);
    }
    print_cie_instrs(cie, error);
    printf("Print fde %" DW_PR_DSd  "\n", fdenum);

    printf("function low pc 0x%" DW_PR_DUx
                   "  and length 0x%" DW_PR_DUx
                   "  and addr we choose 0x%" DW_PR_DUx
                   "\n",
           lowpc, func_length, targetPC);

    /*  1 is arbitrary. We are winding up getting the
        rule count here while leaving things unchanged. */
    oldrulecount = dwarf_set_frame_rule_table_size(dbg, 1);
    dwarf_set_frame_rule_table_size(dbg, oldrulecount);

    tab3.rt3_reg_table_size = oldrulecount;
    tab3.rt3_rules = (struct Dwarf_Regtable_Entry3_s *) malloc(
            sizeof(struct Dwarf_Regtable_Entry3_s) * oldrulecount);
    if (!tab3.rt3_rules) {
      printf("Unable to malloc for %d rules\n", oldrulecount);
      exit(EXIT_FAILURE);
    }

    res = dwarf_get_fde_info_for_all_regs3(fde, targetPC,
                                           &tab3, &actual_pc, error);

    if (res != DW_DLV_OK) {
      printf("dwarf_get_fde_info_for_all_regs3 failed!\n");
      exit(EXIT_FAILURE);
    }
    getCFAlocation(&(tab3.rt3_cfa_rule));
    handle_regtable(&tab3);

    res = dwarf_get_fde_instr_bytes(fde, &outinstrs, &instrslen, error);
    if (res != DW_DLV_OK) {
      printf("dwarf_get_fde_instr_bytes failed!\n");
      exit(EXIT_FAILURE);
    }
    res = dwarf_get_cie_of_fde(fde, &cie, error);
    if (res != DW_DLV_OK) {
      printf("Error getting cie from fde\n");
      exit(EXIT_FAILURE);
    }

    res = dwarf_expand_frame_instructions(cie,
                                          outinstrs, instrslen, &frame_op_list,
                                          &frame_op_count, error);
    if (res != DW_DLV_OK) {
      printf("dwarf_expand_frame_instructions failed!\n");
      exit(EXIT_FAILURE);
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
      printf(" DW_OP_reg%d ", r);
      break;
  }
}

static void
print_one_regentry(const char *prefix,
                   struct Dwarf_Regtable_Entry3_s *entry,
                   int registerNumber) {
  if(entry->dw_regnum == UNDEF_VAL) {
    return;
  }
  if(entry->dw_regnum == SAME_VAL) {
    //$TODO$ handle SAME_VAL
    //$TODO$ PRINT WHICH REGISTER IS ACTUALLY USING THIS AND USE IN EMT
    exit(EXIT_FAILURE);
  }
  printf("RegistersAlive type: %d register:",
         entry->dw_value_type);
  print_reg(registerNumber);
  printf("ValueType: %s",
         (entry->dw_value_type == DW_EXPR_OFFSET) ? "DW_EXPR_OFFSET" :
         (entry->dw_value_type == DW_EXPR_VAL_OFFSET) ? "DW_EXPR_VAL_OFFSET" :
         (entry->dw_value_type == DW_EXPR_EXPRESSION) ? "DW_EXPR_EXPRESSION" :
         (entry->dw_value_type == DW_EXPR_VAL_EXPRESSION) ?
         "DW_EXPR_VAL_EXPRESSION" :
         "Unknown");

  switch (entry->dw_value_type) {
    case DW_EXPR_OFFSET:
//      print_reg(entry->dw_regnum);
//      printf(" offset_rel? %d ", entry->dw_offset_relevant);
      if (entry->dw_offset_relevant) {
        printf(" offset %" DW_PR_DSd " ", entry->dw_offset_or_block_len);
      } else {
        //$TODO$ If this happens flip the register value if it is mask
        printf("value in register");
        //$TODO$ Unhandled case
        exit(EXIT_FAILURE);
      }
      break;
    case DW_EXPR_VAL_OFFSET:
      printf(" offset %" DW_PR_DSd " ",
             entry->dw_offset_or_block_len);
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
handle_regtable(Dwarf_Regtable3 *tab3) {
  int r;
  /* We won't print too much. A bit arbitrary. */
  int max = 32;
  if (max > tab3->rt3_reg_table_size) {
    max = tab3->rt3_reg_table_size;
  }
  for (r = 0; r < max; r++) {
    char rn[30];
    snprintf(rn, sizeof(rn), "reg %d", r);
    print_one_regentry(rn, tab3->rt3_rules + r, r);
  }
}

static void
getCFAlocation(struct Dwarf_Regtable_Entry3_s *CFA_Entry) {
  printf("CFA type: %d register:", CFA_Entry->dw_value_type);
  print_reg(CFA_Entry->dw_regnum);
  if (CFA_Entry->dw_offset_relevant) {
    printf("offset %" DW_PR_DSd " \n", CFA_Entry->dw_offset_or_block_len);
  }
}

/* For inlined functions, try to find name */
static int
get_abstract_origin_variable_name(Dwarf_Debug dbg,Dwarf_Attribute attr, Dwarf_Die *origin_die,
                             char *name_out, unsigned maxlen)
{
  Dwarf_Off off = 0;

  Dwarf_Attribute *atlist = NULL;
  Dwarf_Signed atcnt = 0;
  Dwarf_Signed i = 0;
  int dres = 0;
  int atres = 0;
  int name_found = 0;
  int res = 0;
  Dwarf_Error err = 0;

  res = dwarf_global_formref(attr,&off,&err);
  if (res != DW_DLV_OK) {
    return DW_DLV_NO_ENTRY;
  }
  dres = dwarf_offdie(dbg,off,origin_die,&err);
  if (dres != DW_DLV_OK) {
    return DW_DLV_NO_ENTRY;
  }
  atres = dwarf_attrlist(*origin_die, &atlist, &atcnt, &err);
  if (atres != DW_DLV_OK) {
    dwarf_dealloc(dbg,*origin_die,DW_DLA_DIE);
    return DW_DLV_NO_ENTRY;
  }
  for (i = 0; i < atcnt; i++) {
    Dwarf_Half lattr = 0;
    int ares = 0;

    ares = dwarf_whatattr(atlist[i], &lattr, &err);
    if (ares == DW_DLV_ERROR) {
      break;
    } else if (ares == DW_DLV_OK) {
      if (lattr == DW_AT_name) {
        int sres = 0;
        char* temps = 0;
        sres = dwarf_formstring(atlist[i], &temps, &err);
        if (sres == DW_DLV_OK) {
          strncpy(name_out, temps, strlen(temps));
          name_out[strlen(temps)] = '\0';
          name_found = 1;
          break;
        }
      }
    }
  }
  for (i = 0; i < atcnt; i++) {
    dwarf_dealloc(dbg, atlist[i], DW_DLA_ATTR);
  }
  dwarf_dealloc(dbg, atlist, DW_DLA_LIST);
  if (!name_found) {
    return DW_DLV_NO_ENTRY;
  }
  return DW_DLV_OK;
}