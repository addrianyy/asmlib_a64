#include "Assembler.hpp"

#if __has_include(<base/Error.hpp> )
#include <base/Error.hpp>
#define A64_ASM_ASSERT verify
#else
#include <cstdio>
#include <cstdlib>
#define A64_ASM_ASSERT(value, message)                  \
  do {                                                  \
    const auto _assert_value = (value);                 \
    if (!_assert_value) {                               \
      std::printf("asmlib_a64 error: %s\n", (message)); \
      std::exit(1);                                     \
    }                                                   \
  } while (0)
#endif

using namespace a64;

template <typename T>
static bool fits_within_bits_signed(T value, uint32_t bits) {
  const auto uvalue = uint64_t(value);
  const auto mask = (uint64_t(1) << bits) - 1;
  const auto inv_mask = ~mask;

  const auto last_bit = (uvalue >> (bits - 1)) & 1;
  const auto masked_off = uvalue & inv_mask;

  return masked_off == ((last_bit == 1 ? std::numeric_limits<uint64_t>::max() : 0) & inv_mask);
}

template <typename T>
static bool fits_within_bits_unsigned(T value, uint32_t bits) {
  return uint64_t(value) < (uint64_t(1) << bits);
}

static uint32_t register_index(Reg r) {
  const auto ri = uint32_t(r);

  if (ri <= uint32_t(Reg::Xzr)) {
    return ri - uint32_t(Reg::X0);
  }
  if (ri == uint32_t(Reg::Sp)) {
    return 31;
  }

  if (ri <= uint32_t(Reg::Wzr)) {
    return ri - uint32_t(Reg::W0);
  }
  if (ri == uint32_t(Reg::Wsp)) {
    return 31;
  }

  return 0;
}

static bool is_register_64bit(Reg r) {
  return uint32_t(r) <= uint32_t(Reg::Sp);
}
static bool is_register_sp(Reg r) {
  return r == Reg::Sp || r == Reg::Wsp;
}
static bool is_register_zr(Reg r) {
  return r == Reg::Xzr || r == Reg::Wzr;
}

static Reg to_zero(Reg r) {
  return is_register_64bit(r) ? Reg::Xzr : Reg::Wzr;
}

void Assembler::emit(uint32_t instruction) {
  instructions.push_back(instruction);
}

void Assembler::emit_fixup(Label label, Fixup::Type type) {
  fixups.push_back(Fixup{
    .location = instructions.size(),
    .label = label.index,
    .type = type,
  });
}

void Assembler::encode_add_sub_imm(Reg rd, Reg rn, uint64_t imm, bool sub_op, bool set_flags) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn), "register size mismatch");
  A64_ASM_ASSERT(!is_register_zr(rd) && !is_register_zr(rn), "cannot encode xzr/wzr");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);

  uint32_t shift = 0;

  constexpr auto pow12 = uint64_t(1) << 12;
  if (imm >= pow12) {
    A64_ASM_ASSERT((imm & (pow12 - 1)) == 0, "cannot encode imm12: lower bits are not 0");

    shift = 1;
    imm = imm >> 12;

    A64_ASM_ASSERT(imm < pow12, "cannot encode imm12: number too large");
  }

  emit((uint32_t(is_64bit) << 31) | (uint32_t(sub_op) << 30) | (uint32_t(set_flags) << 29) |
       (uint32_t(0b100010) << 23) | (uint32_t(shift) << 22) | (uint32_t(imm) << 10) |
       (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));
}

void Assembler::encode_add_sub_shifted(Reg rd,
                                       Reg rn,
                                       Reg rm,
                                       uint32_t shift_amount,
                                       Shift shift,
                                       bool sub_op,
                                       bool set_flags) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm),
                 "register size mismatch");
  A64_ASM_ASSERT(!is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm),
                 "cannot encode xsp/wsp");
  A64_ASM_ASSERT(shift == Shift::Lsl || shift == Shift::Lsr || shift == Shift::Asr,
                 "invalid shift type");
  A64_ASM_ASSERT(fits_within_bits_unsigned(shift_amount, 6),
                 "cannot encode shift amount: number too large");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(sub_op) << 30) | (uint32_t(set_flags) << 29) |
       (uint32_t(0b01011) << 24) | (uint32_t(shift) << 22) | (uint32_t(rmi) << 16) |
       (uint32_t(shift_amount) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));
}

void Assembler::encode_bitwise_imm(Reg rd, Reg rn, uint64_t imm, uint32_t opc) {
  const auto is_64bit = is_register_64bit(rd);
  const auto max_imm_bits = 12 + (is_64bit ? 1 : 0);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn), "register size mismatch");
  A64_ASM_ASSERT(!is_register_zr(rd) && !is_register_zr(rn), "cannot encode xzr/wzr");
  A64_ASM_ASSERT(fits_within_bits_unsigned(imm, max_imm_bits),
                 "cannot encode imm12/imm13: number too large");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);

  const uint32_t encoded_imm = 0;
  A64_ASM_ASSERT(false, "TODO: encoding aarch64 bitmasks is not working yet");

  emit((uint32_t(is_64bit) << 31) | (uint32_t(opc) << 29) | (uint32_t(0b100100) << 23) |
       (uint32_t(encoded_imm) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));
}

void Assembler::encode_bitwise_shifted(Reg rd,
                                       Reg rn,
                                       Reg rm,
                                       uint32_t shift_amount,
                                       Shift shift,
                                       uint32_t opc,
                                       bool invert) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm),
                 "register size mismatch");
  A64_ASM_ASSERT(!is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm),
                 "cannot encode xsp/wsp");
  A64_ASM_ASSERT(fits_within_bits_unsigned(shift_amount, 6),
                 "cannot encode shift amount: number too large");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(opc) << 29) | (uint32_t(0b01010) << 24) |
       (uint32_t(shift) << 22) | (uint32_t(invert) << 21) | (uint32_t(rmi) << 16) |
       (uint32_t(shift_amount) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));
}

void Assembler::encode_move_wide(Reg rd, uint64_t imm, uint64_t shift, uint32_t opc) {
  const auto is_64bit = is_register_64bit(rd);
  const auto hw = shift / 16;

  A64_ASM_ASSERT(!is_register_sp(rd), "cannot encode xsp/wsp");

  A64_ASM_ASSERT(hw * 16 == shift && shift <= 48, "shift must be one of: 0, 16, 32, 64");
  if (!is_64bit) {
    A64_ASM_ASSERT(hw <= 1, "cannot shift by more than 16 for 32 bit movX");
  }

  A64_ASM_ASSERT(fits_within_bits_unsigned(imm, 16), "cannot encode imm16: number too big");

  const auto rdi = register_index(rd);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(opc) << 29) | (uint32_t(0b100101) << 23) |
       (uint32_t(hw) << 21) | (uint32_t(imm) << 5) | (uint32_t(rdi) << 0));
}

void Assembler::encode_adr(Reg rd, Label label, uint32_t op) {
  A64_ASM_ASSERT(is_register_64bit(rd), "adr needs 64 bit register");
  A64_ASM_ASSERT(!is_register_sp(rd), "cannot encode xsp/wsp");

  const auto rdi = register_index(rd);

  emit_fixup(label, op == 0 ? Fixup::Type::Adr : Fixup::Type::Adrp);
  emit((uint32_t(op) << 31) | (uint32_t(0b10000) << 24) | (uint32_t(rdi) << 0));
}

void Assembler::encode_shift_reg(Reg rd, Reg rn, Reg rm, uint32_t op2) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm),
                 "register size mismatch");
  A64_ASM_ASSERT(!is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm),
                 "cannot encode xsp/wsp");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b0011010110) << 21) | (uint32_t(rmi) << 16) |
       (uint32_t(0b0010) << 12) | (uint32_t(op2) << 10) | (uint32_t(rni) << 5) |
       (uint32_t(rdi) << 0));
}

void Assembler::encode_mul(Reg rd, Reg rn, Reg rm, Reg ra, uint32_t op) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm) &&
                   is_64bit == is_register_64bit(ra),
                 "register size mismatch");
  A64_ASM_ASSERT(
    !is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm) && !is_register_sp(ra),
    "cannot encode xsp/wsp");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);
  const auto rai = register_index(ra);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b0011011000) << 21) | (uint32_t(rmi) << 16) |
       (uint32_t(op) << 15) | (uint32_t(rai) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));
}

void Assembler::encode_div(Reg rd, Reg rn, Reg rm, uint32_t op) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm),
                 "register size mismatch");
  A64_ASM_ASSERT(!is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm),
                 "cannot encode xsp/wsp");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b0011010110) << 21) | (uint32_t(rmi) << 16) |
       (uint32_t(0b00001) << 11) | (uint32_t(op) << 10) | (uint32_t(rni) << 5) |
       (uint32_t(rdi) << 0));
}

void Assembler::encode_bit_scan(Reg rd, Reg rn, uint32_t op) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn), "register size mismatch");
  A64_ASM_ASSERT(!is_register_sp(rd) && !is_register_sp(rn), "cannot encode xsp/wsp");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b10110101100000000010) << 11) |
       (uint32_t(op) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));
}

void Assembler::encode_cond_select(Reg rd,
                                   Reg rn,
                                   Reg rm,
                                   Condition condition,
                                   uint32_t op,
                                   uint32_t o2) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_ASSERT(is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm),
                 "register size mismatch");
  A64_ASM_ASSERT(!is_register_sp(rd) && !is_register_sp(rn), "cannot encode xsp/wsp");

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(op) << 30) | (uint32_t(0b011010100) << 21) |
       (uint32_t(rmi) << 16) | (uint32_t(condition) << 12) | (uint32_t(o2) << 10) |
       (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));
}

void Assembler::encode_mem_imm_unscaled(Reg rt, Reg rn, int64_t imm, uint32_t size, uint32_t opc) {
  A64_ASM_ASSERT(is_register_64bit(rn), "address register must be 64 bit");
  A64_ASM_ASSERT(!is_register_zr(rn), "cannot encode xzr/wzr as address");
  A64_ASM_ASSERT(!is_register_sp(rt), "cannot encode xsp/esp as value");
  A64_ASM_ASSERT(fits_within_bits_signed(imm, 9), "cannot encode imm9: number too large");

  const auto rti = register_index(rt);
  const auto rni = register_index(rn);

  emit((uint32_t(size) << 30) | (uint32_t(0b111000) << 24) | (uint32_t(opc) << 22) |
       ((uint32_t(imm) & 0b111'111'111) << 12) | (uint32_t(rni) << 5) | (uint32_t(rti) << 0));
}

void Assembler::encode_mem_imm_unsigned_offset(Reg rt,
                                               Reg rn,
                                               uint64_t imm,
                                               uint32_t size,
                                               uint32_t opc) {
  A64_ASM_ASSERT(is_register_64bit(rn), "address register must be 64 bit");
  A64_ASM_ASSERT(!is_register_zr(rn), "cannot encode xzr/wzr as address");
  A64_ASM_ASSERT(!is_register_sp(rt), "cannot encode xsp/esp as value");
  A64_ASM_ASSERT(fits_within_bits_unsigned(imm, 12), "cannot encode imm12: number too large");

  const auto rti = register_index(rt);
  const auto rni = register_index(rn);

  emit((uint32_t(size) << 30) | (uint32_t(0b111001) << 24) | (uint32_t(opc) << 22) |
       ((uint32_t(imm) & 0b111'111'111'111) << 10) | (uint32_t(rni) << 5) | (uint32_t(rti) << 0));
}

void Assembler::encode_mem_imm_writeback(Reg rt,
                                         Reg rn,
                                         int64_t imm,
                                         uint32_t size,
                                         uint32_t opc,
                                         bool post_index) {
  A64_ASM_ASSERT(is_register_64bit(rn), "address register must be 64 bit");
  A64_ASM_ASSERT(!is_register_zr(rn), "cannot encode xzr/wzr as address");
  A64_ASM_ASSERT(!is_register_sp(rt), "cannot encode xsp/esp as value");
  A64_ASM_ASSERT(fits_within_bits_signed(imm, 9), "cannot encode imm12: number too large");

  const auto rti = register_index(rt);
  const auto rni = register_index(rn);

  const auto op2 = post_index ? 0b01 : 0b11;

  emit((uint32_t(size) << 30) | (uint32_t(0b111000) << 24) | (uint32_t(opc) << 22) |
       ((uint32_t(imm) & 0b111'111'111) << 12) | (uint32_t(op2) << 10) | (uint32_t(rni) << 5) |
       (uint32_t(rti) << 0));
}

void Assembler::encode_mem_imm(Reg rt,
                               Reg rn,
                               int64_t imm,
                               Writeback writeback,
                               uint32_t size,
                               uint32_t opc) {
  if (writeback == Writeback::None) {
    if (imm >= 0) {
      // size is log2
      const auto uimm = uint64_t(imm);
      const auto scaled_uimm = uimm >> size;
      if ((scaled_uimm << size) == uimm) {
        return encode_mem_imm_unsigned_offset(rt, rn, scaled_uimm, size, opc);
      }
    }

    return encode_mem_imm_unscaled(rt, rn, imm, size, opc);
  } else {
    return encode_mem_imm_writeback(rt, rn, imm, size, opc, writeback == Writeback::Post);
  }
}

void Assembler::encode_mem_reg(Reg rt,
                               Reg rn,
                               Reg rm,
                               Scale scale,
                               Extend extend,
                               uint32_t size,
                               uint32_t opc) {
  A64_ASM_ASSERT(is_register_64bit(rn), "address register must be 64 bit");
  A64_ASM_ASSERT(!is_register_zr(rn), "cannot encode xzr/wzr as address");
  A64_ASM_ASSERT(!is_register_sp(rt) && !is_register_sp(rn),
                 "cannot encode xsp/wsp as value or index");

  const auto rti = register_index(rt);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  const auto option = uint32_t(extend);
  const auto s = scale == Scale::DataSize ? 1 : 0;

  emit((uint32_t(size) << 30) | (uint32_t(0b111000) << 24) | (uint32_t(opc) << 22) |
       (uint32_t(0b1) << 21) | (uint32_t(rmi) << 16) | (uint32_t(option) << 13) |
       (uint32_t(s) << 12) | (uint32_t(0b1) << 11) | (uint32_t(rni) << 5) | (uint32_t(rti) << 0));
}

void Assembler::encode_mem_label(Reg rt, Label label, uint32_t opc) {
  A64_ASM_ASSERT(!is_register_sp(rt), "cannot encode sp as value");

  const auto rti = register_index(rt);

  emit_fixup(label, Fixup::Type::Bcond_Cb_Ldr);
  emit((uint32_t(opc) << 30) | (uint32_t(0b011000) << 24) | (uint32_t(rti) << 0));
}

void Assembler::encode_mem_pair(Reg rt1,
                                Reg rt2,
                                Reg rn,
                                int64_t imm,
                                Writeback writeback,
                                uint32_t opc,
                                uint32_t l) {
  A64_ASM_ASSERT(is_register_64bit(rn), "address register must be 64 bit");
  A64_ASM_ASSERT(!is_register_zr(rn), "cannot encode xzr/wzr as address");
  A64_ASM_ASSERT(!is_register_sp(rt1) && !is_register_sp(rt2), "cannot encode xsp/esp as value");
  A64_ASM_ASSERT(is_register_64bit(rt1) == is_register_64bit(rt2), "register size mismatch");

  const auto rt1i = register_index(rt1);
  const auto rt2i = register_index(rt2);
  const auto rni = register_index(rn);

  uint32_t writeback_c = 0;
  switch (writeback) {
    case Writeback::Post:
      writeback_c = 0b01;
      break;
    case Writeback::Pre:
      writeback_c = 0b11;
      break;
    case Writeback::None:
      writeback_c = 0b10;
      break;
  }

  const uint32_t scale = opc == 0b10 ? 3 : 2;

  const auto scaled_imm = imm >> scale;
  A64_ASM_ASSERT((scaled_imm << scale) == imm, "cannot encode mempair imm: not aligned");
  A64_ASM_ASSERT(fits_within_bits_signed(scaled_imm, 7), "cannot encode imm7: number too large");

  emit((uint32_t(opc) << 30) | (uint32_t(0b10100) << 25) | (uint32_t(writeback_c) << 23) |
       (uint32_t(l) << 22) | ((uint32_t(scaled_imm) & 0b1111111) << 15) | (uint32_t(rt2i) << 10) |
       (uint32_t(rni) << 5) | (uint32_t(rt1i) << 0));
}

void Assembler::encode_cb(Reg rt, Label label, uint32_t op) {
  const auto is_64bit = is_register_64bit(rt);

  A64_ASM_ASSERT(!is_register_sp(rt), "cannot encode xsp/esp");

  const auto rti = register_index(rt);

  emit_fixup(label, Fixup::Type::Bcond_Cb_Ldr);
  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b011010) << 25) | (uint32_t(op) << 24) |
       ((uint32_t(rti) << 0)));
}

void Assembler::encode_tb(Reg rt, uint64_t bit, Label label, uint32_t op) {
  const auto is_64bit = is_register_64bit(rt);

  A64_ASM_ASSERT(!is_register_sp(rt), "cannot encode xsp/esp");
  A64_ASM_ASSERT(bit < (is_64bit ? 64 : 32), "cannot encode bit imm: too large number");

  const auto rti = register_index(rt);

  emit_fixup(label, Fixup::Type::Tb);
  emit((uint32_t(bit >= 32) << 31) | (uint32_t(0b011011) << 25) | (uint32_t(op) << 24) |
       (uint32_t(bit & 0b11111) << 19) | ((uint32_t(rti) << 0)));
}

void Assembler::encode_b_imm(Label label, bool op) {
  emit_fixup(label, Fixup::Type::B);
  emit((uint32_t(op) << 31) | (uint32_t(0b00101) << 26));
}

void Assembler::encode_br_indirect(Reg rn, uint32_t op) {
  A64_ASM_ASSERT(is_register_64bit(rn), "indirect branches must use 64 bit registers");
  A64_ASM_ASSERT(!is_register_sp(rn), "cannot encode xsp/esp");

  const auto rni = register_index(rn);

  emit((uint32_t(0b1101011000011111000000) << 10) | (uint32_t(op) << 21) | (uint32_t(rni) << 5));
}

void Assembler::add(Reg rd, Reg rn, uint64_t imm) {
  encode_add_sub_imm(rd, rn, imm, false, false);
}
void Assembler::adds(Reg rd, Reg rn, uint64_t imm) {
  encode_add_sub_imm(rd, rn, imm, false, true);
}
void Assembler::sub(Reg rd, Reg rn, uint64_t imm) {
  encode_add_sub_imm(rd, rn, imm, true, false);
}
void Assembler::subs(Reg rd, Reg rn, uint64_t imm) {
  encode_add_sub_imm(rd, rn, imm, true, true);
}
void Assembler::cmp(Reg rn, uint64_t imm) {
  subs(to_zero(rn), rn, imm);
}
void Assembler::cmn(Reg rn, uint64_t imm) {
  adds(to_zero(rn), rn, imm);
}

void Assembler::and_(Reg rd, Reg rn, uint64_t imm) {
  encode_bitwise_imm(rd, rn, imm, 0b00);
}
void Assembler::ands(Reg rd, Reg rn, uint64_t imm) {
  encode_bitwise_imm(rd, rn, imm, 0b11);
}
void Assembler::eor(Reg rd, Reg rn, uint64_t imm) {
  encode_bitwise_imm(rd, rn, imm, 0b10);
}
void Assembler::orr(Reg rd, Reg rn, uint64_t imm) {
  encode_bitwise_imm(rd, rn, imm, 0b01);
}
void Assembler::tst(Reg rn, uint64_t imm) {
  ands(to_zero(rn), rn, imm);
}

void Assembler::movz(Reg rd, uint64_t imm, uint64_t shift) {
  encode_move_wide(rd, imm, shift, 0b10);
}
void Assembler::movk(Reg rd, uint64_t imm, uint64_t shift) {
  encode_move_wide(rd, imm, shift, 0b11);
}
void Assembler::movn(Reg rd, uint64_t imm, uint64_t shift) {
  encode_move_wide(rd, imm, shift, 0b00);
}

void Assembler::adr(Reg rd, Label label) {
  encode_adr(rd, label, 0);
}

void Assembler::adrp(Reg rd, Label label) {
  encode_adr(rd, label, 1);
}

void Assembler::add(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_add_sub_shifted(rd, rn, rm, shift_amount, shift, false, false);
}
void Assembler::adds(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_add_sub_shifted(rd, rn, rm, shift_amount, shift, false, true);
}
void Assembler::sub(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_add_sub_shifted(rd, rn, rm, shift_amount, shift, true, false);
}
void Assembler::subs(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_add_sub_shifted(rd, rn, rm, shift_amount, shift, true, true);
}
void Assembler::cmp(Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  subs(to_zero(rn), rn, rm, shift_amount, shift);
}
void Assembler::cmn(Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  adds(to_zero(rn), rn, rm, shift_amount, shift);
}

void Assembler::neg(Reg rd, Reg rm, uint64_t shift_amount, Shift shift) {
  sub(rd, to_zero(rm), rm, shift_amount, shift);
}
void Assembler::negs(Reg rd, Reg rm, uint64_t shift_amount, Shift shift) {
  subs(rd, to_zero(rm), rm, shift_amount, shift);
}

void Assembler::and_(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b00, false);
}
void Assembler::ands(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b11, false);
}
void Assembler::bic(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b00, true);
}
void Assembler::bics(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b11, true);
}
void Assembler::eor(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b10, false);
}
void Assembler::eon(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b10, true);
}
void Assembler::orr(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b01, false);
}
void Assembler::orn(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b01, true);
}
void Assembler::mvn(Reg rd, Reg rm, uint64_t shift_amount, Shift shift) {
  orn(rd, to_zero(rm), rm, shift_amount, shift);
}
void Assembler::tst(Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  ands(to_zero(rn), rn, rm, shift_amount, shift);
}
void Assembler::mov(Reg rd, Reg rn) {
  if (is_register_sp(rd) || is_register_sp(rn)) {
    add(rd, rn, 0);
  } else {
    orr(rd, to_zero(rd), rn);
  }
}

void Assembler::asr(Reg rd, Reg rn, Reg rm) {
  encode_shift_reg(rd, rn, rm, 0b10);
}
void Assembler::lsl(Reg rd, Reg rn, Reg rm) {
  encode_shift_reg(rd, rn, rm, 0b00);
}
void Assembler::lsr(Reg rd, Reg rn, Reg rm) {
  encode_shift_reg(rd, rn, rm, 0b01);
}
void Assembler::ror(Reg rd, Reg rn, Reg rm) {
  encode_shift_reg(rd, rn, rm, 0b11);
}

void Assembler::madd(Reg rd, Reg rn, Reg rm, Reg ra) {
  encode_mul(rd, rn, rm, ra, 0);
}
void Assembler::msub(Reg rd, Reg rn, Reg rm, Reg ra) {
  encode_mul(rd, rn, rm, ra, 1);
}
void Assembler::mneg(Reg rd, Reg rn, Reg rm) {
  msub(rd, rn, rm, to_zero(rm));
}
void Assembler::mul(Reg rd, Reg rn, Reg rm) {
  madd(rd, rn, rm, to_zero(rm));
}

void Assembler::sdiv(Reg rd, Reg rn, Reg rm) {
  encode_div(rd, rn, rm, 1);
}
void Assembler::udiv(Reg rd, Reg rn, Reg rm) {
  encode_div(rd, rn, rm, 0);
}

void Assembler::cls(Reg rd, Reg rn) {
  encode_bit_scan(rd, rn, 1);
}
void Assembler::clz(Reg rd, Reg rn) {
  encode_bit_scan(rd, rn, 0);
}

void Assembler::csel(Reg rd, Reg rn, Reg rm, Condition condition) {
  encode_cond_select(rd, rn, rm, condition, 0, 0);
}
void Assembler::csinc(Reg rd, Reg rn, Reg rm, Condition condition) {
  encode_cond_select(rd, rn, rm, condition, 0, 1);
}
void Assembler::csinc(Reg rd, Condition condition) {
  csinc(rd, to_zero(rd), to_zero(rd), condition);
}

void Assembler::ldr(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  encode_mem_imm(rt, rn, imm, writeback, is_register_64bit(rt) ? 0b11 : 0b10, 0b01);
}
void Assembler::ldrh(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  encode_mem_imm(rt, rn, imm, writeback, 0b01, 0b01);
}
void Assembler::ldrb(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  encode_mem_imm(rt, rn, imm, writeback, 0b00, 0b01);
}
void Assembler::ldrsw(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  A64_ASM_ASSERT(is_register_64bit(rt), "rt must be 64 bit for ldrsw");
  encode_mem_imm(rt, rn, imm, writeback, 0b10, 0b10);
}
void Assembler::ldrsh(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  encode_mem_imm(rt, rn, imm, writeback, 0b01, is_register_64bit(rt) ? 0b10 : 0b11);
}
void Assembler::ldrsb(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  encode_mem_imm(rt, rn, imm, writeback, 0b00, is_register_64bit(rt) ? 0b10 : 0b11);
}

void Assembler::str(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  encode_mem_imm(rt, rn, imm, writeback, is_register_64bit(rt) ? 0b11 : 0b10, 0b00);
}
void Assembler::strh(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  encode_mem_imm(rt, rn, imm, writeback, 0b01, 0b00);
}
void Assembler::strb(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  encode_mem_imm(rt, rn, imm, writeback, 0b00, 0b00);
}

void Assembler::ldr(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  encode_mem_reg(rt, rn, rm, scale, extend, is_register_64bit(rt) ? 0b11 : 0b10, 0b01);
}
void Assembler::ldrh(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  encode_mem_reg(rt, rn, rm, scale, extend, 0b01, 0b01);
}
void Assembler::ldrb(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  encode_mem_reg(rt, rn, rm, scale, extend, 0b00, 0b01);
}
void Assembler::ldrsw(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  A64_ASM_ASSERT(is_register_64bit(rt), "rt must be 64 bit for ldrsw");
  encode_mem_reg(rt, rn, rm, scale, extend, 0b10, 0b10);
}
void Assembler::ldrsh(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  encode_mem_reg(rt, rn, rm, scale, extend, 0b01, is_register_64bit(rt) ? 0b10 : 0b11);
}
void Assembler::ldrsb(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  encode_mem_reg(rt, rn, rm, scale, extend, 0b00, is_register_64bit(rt) ? 0b10 : 0b11);
}

void Assembler::str(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  encode_mem_reg(rt, rn, rm, scale, extend, is_register_64bit(rt) ? 0b11 : 0b10, 0b00);
}
void Assembler::strh(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  encode_mem_reg(rt, rn, rm, scale, extend, 0b01, 0b00);
}
void Assembler::strb(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  encode_mem_reg(rt, rn, rm, scale, extend, 0b00, 0b00);
}

void Assembler::ldr(Reg rt, Label label) {
  encode_mem_label(rt, label, is_register_64bit(rt) ? 0b01 : 0b00);
}
void Assembler::ldrsw(Reg rt, Label label) {
  A64_ASM_ASSERT(is_register_64bit(rt), "rt must be 64 bit for ldrsw");
  encode_mem_label(rt, label, 0b10);
}

void Assembler::ldp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_pair(rt1, rt2, rn, imm, writeback, is_register_64bit(rt1) ? 0b10 : 0b00, 1);
}
void Assembler::ldpsw(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback) {
  A64_ASM_ASSERT(is_register_64bit(rt1), "rt must be 64 bit for ldpsw");
  return encode_mem_pair(rt1, rt2, rn, imm, writeback, 0b01, 1);
}
void Assembler::stp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_pair(rt1, rt2, rn, imm, writeback, is_register_64bit(rt1) ? 0b10 : 0b00, 0);
}

void Assembler::b(Condition condition, Label label) {
  emit_fixup(label, Fixup::Type::Bcond_Cb_Ldr);
  emit((uint32_t(0b01010100) << 24) | (uint32_t(condition) << 0));
}

void Assembler::cbz(Reg rt, Label label) {
  encode_cb(rt, label, 0);
}
void Assembler::cbnz(Reg rt, Label label) {
  encode_cb(rt, label, 1);
}
void Assembler::tbz(Reg rt, uint64_t bit, Label label) {
  encode_tb(rt, bit, label, 0);
}
void Assembler::tbnz(Reg rt, uint64_t bit, Label label) {
  encode_tb(rt, bit, label, 1);
}

void Assembler::b(Label label) {
  encode_b_imm(label, false);
}

void Assembler::bl(Label label) {
  encode_b_imm(label, true);
}

void Assembler::blr(Reg rn) {
  encode_br_indirect(rn, 0b01);
}

void Assembler::br(Reg rn) {
  encode_br_indirect(rn, 0b00);
}

void Assembler::ret(Reg rn) {
  encode_br_indirect(rn, 0b10);
}

void Assembler::svc(uint16_t imm) {
  emit((uint32_t(0b11010100000) << 21) | (uint32_t(imm) << 5) | (uint32_t(1) << 0));
}
void Assembler::brk(uint16_t imm) {
  emit((uint32_t(0b11010100001) << 21) | (uint32_t(imm) << 5));
}

Label Assembler::allocate_label() {
  const auto index = labels.size();
  labels.emplace_back(std::numeric_limits<uint64_t>::max());
  return Label{index};
}

void Assembler::insert_label(Label label) {
  A64_ASM_ASSERT(labels[label.index] == std::numeric_limits<uint64_t>::max(),
                 "cannot place the same label more than once");
  labels[label.index] = instructions.size();
}

Label Assembler::insert_label() {
  const auto l = allocate_label();
  insert_label(l);
  return l;
}

void Assembler::apply_fixups() {
  for (const auto& fixup : fixups) {
    const auto target = labels[fixup.label];
    A64_ASM_ASSERT(target != std::numeric_limits<uint64_t>::max(), "label cannot be resolved");

    uint32_t size{};
    uint32_t shift{};

    const auto delta = int64_t(target) - int64_t(fixup.location);

    bool skip = false;

    switch (fixup.type) {
      case Fixup::Type::B: {
        size = 26;
        shift = 0;
        break;
      }

      case Fixup::Type::Bcond_Cb_Ldr: {
        size = 19;
        shift = 5;
        break;
      }

      case Fixup::Type::Tb: {
        size = 14;
        shift = 5;
        break;
      }

      case Fixup::Type::Adr:
      case Fixup::Type::Adrp: {
        const auto delta2 = fixup.type == Fixup::Type::Adrp ? (delta >> 12) : delta;

        A64_ASM_ASSERT(fits_within_bits_signed(delta2, 21),
                       "cannot fixup: adr/adrpdelta doesn't fit in imm field");

        // TODO: is this correct for adrp?
        const auto delta_masked = uint64_t(delta2 & ((uint32_t(1) << 21) - 1));

        instructions[fixup.location] |= (delta_masked & 0b11) << 29;
        instructions[fixup.location] |= (delta_masked >> 2) << 5;
        skip = true;

        break;
      }

      default: {
        A64_ASM_ASSERT(false, "unreachable code");
      }
    }

    if (!skip) {
      A64_ASM_ASSERT(fits_within_bits_signed(delta, size),
                     "cannot fixup: delta doesn't fit in imm field");
      instructions[fixup.location] |= uint64_t(delta & ((uint32_t(1) << size) - 1)) << shift;
    }
  }
}

std::span<const uint32_t> Assembler::assembled_instructions() const {
  return instructions;
}