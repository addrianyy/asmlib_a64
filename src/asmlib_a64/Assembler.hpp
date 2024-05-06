#pragma once
#include <cstdint>
#include <limits>
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
    InvalidWriteback,
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

  constexpr static uint32_t invalid_index = std::numeric_limits<uint32_t>::max();

  uint32_t index{invalid_index};

  explicit Label(uint32_t index) : index(index) {}

 public:
  Label() = default;

  operator bool() const { return index != invalid_index; }
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

    Type type{};
    Label label;
    uint32_t location{};
  };

  std::vector<uint32_t> instructions;
  std::vector<uint32_t> labels;
  std::vector<Fixup> fixups;

  void emit(uint32_t instruction);
  void emit_fixup(Label label, Fixup::Type type);

  Status encode_add_sub_imm(Register rd, Register rn, uint64_t imm, bool sub_op, bool set_flags);
  Status encode_bitwise_imm(Register rd, Register rn, uint64_t imm, uint32_t opc);
  Status encode_move_wide(Register rd, uint64_t imm, uint64_t shift, uint32_t opc);
  Status encode_adr(Register rd, Label label, uint32_t op);
  Status encode_bitfield_move(Register rd, Register rn, uint64_t immr, uint64_t imms, uint32_t opc);
  Status encode_extr(Register rd, Register rn, Register rm, uint64_t lsb);

  Status encode_add_sub_shifted(Register rd,
                                Register rn,
                                Register rm,
                                uint32_t shift_amount,
                                Shift shift,
                                bool sub_op,
                                bool set_flags);
  Status encode_bitwise_shifted(Register rd,
                                Register rn,
                                Register rm,
                                uint32_t shift_amount,
                                Shift shift,
                                uint32_t opc,
                                bool invert);
  Status encode_shift_reg(Register rd, Register rn, Register rm, uint32_t op2);
  Status encode_mul(Register rd, Register rn, Register rm, Register ra, uint32_t op);
  Status encode_div(Register rd, Register rn, Register rm, uint32_t op);
  Status encode_bit_scan(Register rd, Register rn, uint32_t op);
  Status encode_cond_select(Register rd,
                            Register rn,
                            Register rm,
                            Condition condition,
                            uint32_t op,
                            uint32_t o2);

  Status encode_mem_imm_unscaled(Register rt,
                                 Register rn,
                                 int64_t imm,
                                 uint32_t size,
                                 uint32_t opc);
  Status encode_mem_imm_unsigned_offset(Register rt,
                                        Register rn,
                                        uint64_t imm,
                                        uint32_t size,
                                        uint32_t opc);
  Status encode_mem_imm_writeback(Register rt,
                                  Register rn,
                                  int64_t imm,
                                  uint32_t size,
                                  uint32_t opc,
                                  bool post_index);
  Status encode_mem_imm(Register rt,
                        Register rn,
                        int64_t imm,
                        Writeback writeback,
                        uint32_t size,
                        uint32_t opc);
  Status encode_mem_reg(Register rt,
                        Register rn,
                        Register rm,
                        Scale scale,
                        Extend extend,
                        uint32_t size,
                        uint32_t opc);
  Status encode_mem_label(Register rt, Label label, uint32_t opc);
  Status encode_mem_pair(Register rt1,
                         Register rt2,
                         Register rn,
                         int64_t imm,
                         Writeback writeback,
                         uint32_t opc,
                         uint32_t l);
  Status encode_mem_acq_rel(Register rt, Register rn, uint32_t size, uint32_t l);

  Status encode_cb(Register rt, Label label, uint32_t op);
  Status encode_tb(Register rt, uint64_t bit, Label label, uint32_t op);
  Status encode_b_imm(Label label, bool op);
  Status encode_br_indirect(Register rn, uint32_t op);

  void assert_instruction_encoded(const char* instruction_name, Status status);

  void apply_fixup(const Fixup& fixup);
  void apply_fixups();

 public:
#include "Instructions.inc"

  uintptr_t instruction_offset() const { return instructions.size(); }
  uintptr_t byte_offset() const { return instruction_offset() * sizeof(uint32_t); }

  Label allocate_label();
  void insert_label(Label label);
  Label insert_label();

  bool is_label_inserted(Label label) const;

  std::span<const uint32_t> assembled_instructions();

  void clear();
};

}  // namespace a64