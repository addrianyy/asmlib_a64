#pragma once
#include <cstdint>
#include <span>
#include <vector>

#include "Types.hpp"

namespace a64 {

class Status {
 public:
  enum class Code {
    Success,
    UImmTooLarge,
    SImmTooLarge,
    SpOperandForbidden,
    ZrOperandForbidden,
    Non64bitOperandForbidden,
    Non64bitAddressForbidden,
    MemoryOffsetUnaligned,
    RegistersMismatched,
    ShiftAmountInvalid,
    ShiftTypeInvalid,
    BitmaskInvalid,
    BitmaskInvalidFor32Bit,
  };

 private:
  Code code_ = Code::Success;

 public:
  Status() = default;
  explicit Status(Code code) : code_(code) {}

  Code code() const { return code_; }

  operator bool() const { return code_ == Code::Success; }
};

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

  Status encode_add_sub_imm(Reg rd, Reg rn, uint64_t imm, bool sub_op, bool set_flags);
  Status encode_add_sub_shifted(Reg rd,
                                Reg rn,
                                Reg rm,
                                uint32_t shift_amount,
                                Shift shift,
                                bool sub_op,
                                bool set_flags);
  Status encode_bitwise_imm(Reg rd, Reg rn, uint64_t imm, uint32_t opc);
  Status encode_bitwise_shifted(Reg rd,
                                Reg rn,
                                Reg rm,
                                uint32_t shift_amount,
                                Shift shift,
                                uint32_t opc,
                                bool invert);

  Status encode_move_wide(Reg rd, uint64_t imm, uint64_t shift, uint32_t opc);
  Status encode_adr(Reg rd, Label label, uint32_t op);
  Status encode_bitfield_move(Reg rd, Reg rn, uint64_t immr, uint64_t imms, uint32_t opc);
  Status encode_extr(Reg rd, Reg rn, Reg rm, uint64_t lsb);

  Status encode_shift_reg(Reg rd, Reg rn, Reg rm, uint32_t op2);
  Status encode_mul(Reg rd, Reg rn, Reg rm, Reg ra, uint32_t op);
  Status encode_div(Reg rd, Reg rn, Reg rm, uint32_t op);
  Status encode_bit_scan(Reg rd, Reg rn, uint32_t op);
  Status encode_cond_select(Reg rd, Reg rn, Reg rm, Condition condition, uint32_t op, uint32_t o2);

  Status encode_mem_imm_unscaled(Reg rt, Reg rn, int64_t imm, uint32_t size, uint32_t opc);
  Status encode_mem_imm_unsigned_offset(Reg rt, Reg rn, uint64_t imm, uint32_t size, uint32_t opc);
  Status encode_mem_imm_writeback(Reg rt,
                                  Reg rn,
                                  int64_t imm,
                                  uint32_t size,
                                  uint32_t opc,
                                  bool post_index);
  Status encode_mem_imm(Reg rt,
                        Reg rn,
                        int64_t imm,
                        Writeback writeback,
                        uint32_t size,
                        uint32_t opc);
  Status
  encode_mem_reg(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend, uint32_t size, uint32_t opc);
  Status encode_mem_label(Reg rt, Label label, uint32_t opc);
  Status encode_mem_pair(Reg rt1,
                         Reg rt2,
                         Reg rn,
                         int64_t imm,
                         Writeback writeback,
                         uint32_t opc,
                         uint32_t l);

  Status encode_cb(Reg rt, Label label, uint32_t op);
  Status encode_tb(Reg rt, uint64_t bit, Label label, uint32_t op);
  Status encode_b_imm(Label label, bool op);
  Status encode_br_indirect(Reg rn, uint32_t op);

  void assert_instruction_encoded(const char* instruction_name, Status status);

 public:
#include "Instructions.inc"

  Label allocate_label();
  void insert_label(Label label);
  Label insert_label();

  void apply_fixups();
  std::span<const uint32_t> assembled_instructions() const;
};

}  // namespace a64