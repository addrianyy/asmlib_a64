#pragma once
#include <cstdint>
#include <span>
#include <vector>

#include "Types.hpp"

namespace a64 {

class Label {
  friend class Assembler;

  uint64_t index;

  explicit Label(uint64_t index) : index(index) {}
};

class Assembler {
  struct Fixup {
    enum class Type {
      B,
      Tb,
      Adr,
      Adrp,
      Bcond_Cb_Ldr,
    };

    Type type;
    uint64_t label;
    uint64_t location;
  };

  std::vector<uint32_t> instructions;
  std::vector<uint64_t> labels;
  std::vector<Fixup> fixups;

  void emit(uint32_t instruction);
  void emit_fixup(Label label, Fixup::Type type);

  void encode_add_sub_imm(Reg rd, Reg rn, uint64_t imm, bool sub_op, bool set_flags);
  void encode_add_sub_shifted(Reg rd,
                              Reg rn,
                              Reg rm,
                              uint32_t shift_amount,
                              Shift shift,
                              bool sub_op,
                              bool set_flags);
  void encode_bitwise_imm(Reg rd, Reg rn, uint64_t imm, uint32_t opc);
  void encode_bitwise_shifted(Reg rd,
                              Reg rn,
                              Reg rm,
                              uint32_t shift_amount,
                              Shift shift,
                              uint32_t opc,
                              bool invert);

  void encode_move_wide(Reg rd, uint64_t imm, uint64_t shift, uint32_t opc);

  void encode_adr(Reg rd, Label label, uint32_t op);

  void encode_shift_reg(Reg rd, Reg rn, Reg rm, uint32_t op2);
  void encode_mul(Reg rd, Reg rn, Reg rm, Reg ra, uint32_t op);
  void encode_div(Reg rd, Reg rn, Reg rm, uint32_t op);
  void encode_bit_scan(Reg rd, Reg rn, uint32_t op);
  void encode_cond_select(Reg rd, Reg rn, Reg rm, Condition condition, uint32_t op, uint32_t o2);

  void encode_mem_imm_unscaled(Reg rt, Reg rn, int64_t imm, uint32_t size, uint32_t opc);
  void encode_mem_imm_unsigned_offset(Reg rt, Reg rn, uint64_t imm, uint32_t size, uint32_t opc);
  void encode_mem_imm_writeback(Reg rt,
                                Reg rn,
                                int64_t imm,
                                uint32_t size,
                                uint32_t opc,
                                bool post_index);
  void encode_mem_imm(Reg rt,
                      Reg rn,
                      int64_t imm,
                      Writeback writeback,
                      uint32_t size,
                      uint32_t opc);

  void
  encode_mem_reg(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend, uint32_t size, uint32_t opc);

  void encode_mem_label(Reg rt, Label label, uint32_t opc);

  void encode_mem_pair(Reg rt1,
                       Reg rt2,
                       Reg rn,
                       int64_t imm,
                       Writeback writeback,
                       uint32_t opc,
                       uint32_t l);

  void encode_cb(Reg rt, Label label, uint32_t op);
  void encode_tb(Reg rt, uint64_t bit, Label label, uint32_t op);

  void encode_b_imm(Label label, bool op);

  void encode_br_indirect(Reg rn, uint32_t op);

 public:
  void add(Reg rd, Reg rn, uint64_t imm);
  void adds(Reg rd, Reg rn, uint64_t imm);
  void sub(Reg rd, Reg rn, uint64_t imm);
  void subs(Reg rd, Reg rn, uint64_t imm);
  void cmp(Reg rn, uint64_t imm);
  void cmn(Reg rn, uint64_t imm);

  void and_(Reg rd, Reg rn, uint64_t imm);
  void ands(Reg rd, Reg rn, uint64_t imm);
  void eor(Reg rd, Reg rn, uint64_t imm);
  void orr(Reg rd, Reg rn, uint64_t imm);
  void tst(Reg rn, uint64_t imm);

  void movz(Reg rd, uint64_t imm, uint64_t shift = 0);
  void movk(Reg rd, uint64_t imm, uint64_t shift = 0);
  void movn(Reg rd, uint64_t imm, uint64_t shift = 0);

  void adr(Reg rd, Label label);
  void adrp(Reg rd, Label label);

  void add(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void adds(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void sub(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void subs(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void cmp(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void cmn(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void neg(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void negs(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);

  void and_(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void ands(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void bic(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void bics(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void eor(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void eon(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void orr(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void orn(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void mvn(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
  void tst(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);

  void mov(Reg rd, Reg rn);

  void asr(Reg rd, Reg rn, Reg rm);
  void lsl(Reg rd, Reg rn, Reg rm);
  void lsr(Reg rd, Reg rn, Reg rm);
  void ror(Reg rd, Reg rn, Reg rm);

  void madd(Reg rd, Reg rn, Reg rm, Reg ra);
  void msub(Reg rd, Reg rn, Reg rm, Reg ra);
  void mneg(Reg rd, Reg rn, Reg rm);
  void mul(Reg rd, Reg rn, Reg rm);

  void sdiv(Reg rd, Reg rn, Reg rm);
  void udiv(Reg rd, Reg rn, Reg rm);

  void cls(Reg rd, Reg rn);
  void clz(Reg rd, Reg rn);

  void csel(Reg rd, Reg rn, Reg rm, Condition condition);
  void csinc(Reg rd, Reg rn, Reg rm, Condition condition);
  void cset(Reg rd, Condition condition);

  void ldr(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
  void ldrh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
  void ldrb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
  void ldrsw(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
  void ldrsh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
  void ldrsb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);

  void str(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
  void strh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
  void strb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);

  void ldr(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
  void ldrh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
  void ldrb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
  void ldrsw(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
  void ldrsh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
  void ldrsb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);

  void str(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
  void strh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
  void strb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);

  void ldr(Reg rt, Label label);
  void ldrsw(Reg rt, Label label);

  void ldp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
  void ldpsw(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None);

  void stp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None);

  void b(Condition condition, Label label);
  void cbz(Reg rt, Label label);
  void cbnz(Reg rt, Label label);
  void tbz(Reg rt, uint64_t bit, Label label);
  void tbnz(Reg rt, uint64_t bit, Label label);

  void b(Label label);
  void bl(Label label);

  void blr(Reg rn);
  void br(Reg rn);
  void ret(Reg rn);

  void svc(uint16_t imm);
  void brk(uint16_t imm);

  Label allocate_label();
  void insert_label(Label label);
  Label insert_label();

  void apply_fixups();
  std::span<const uint32_t> assembled_instructions() const;
};

}  // namespace a64