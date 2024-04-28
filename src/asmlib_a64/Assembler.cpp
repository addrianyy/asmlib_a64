#include "Assembler.hpp"

#include <bit>

#if __has_include(<base/Error.hpp> )
#include <base/Error.hpp>
#define A64_ASM_ASSERT verify
#define A64_ASM_HAS_FORMATTED_ASSERT
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

#define A64_ASM_CHECK(error_code, check)       \
  do {                                         \
    if (!(check)) {                            \
      return Status{Status::Code::error_code}; \
    }                                          \
  } while (0);

using namespace a64;

static const char* status_code_description(Status::Code code) {
  using C = Status::Code;

  // clang-format off
  switch (code) {
    case C::Success: return "success";
    case C::UImmTooLarge: return "unsigned immediate is too large";
    case C::SImmTooLarge: return "signed immediate is too large";
    case C::SpOperandForbidden: return "xsp/wsp operand is forbidden";
    case C::ZrOperandForbidden: return "xzr/wzr operand is forbidden";
    case C::Non64bitOperandForbidden: return "non 64 bit operand is forbidden";
    case C::Non64bitAddressForbidden: return "non 64 bit address operand is forbidden";
    case C::MemoryOffsetUnaligned: return "memory offset is unligned";
    case C::RegistersMismatched: return "registers have mismatched sizes";
    case C::ShiftAmountInvalid: return "shift amount is invalid";
    case C::ShiftTypeInvalid: return "shift type is invalid";
    case C::BitmaskInvalid: return "bitmask is invalid";
    case C::BitmaskInvalidFor32Bit: return "bitmask is invalid for 32 bit operation";
    default: {
      A64_ASM_ASSERT(false, "unknown status code");
    }
  }
  // clang-format on

  return "";
}

template <typename T>
static std::make_unsigned_t<T> positive_modulo(std::make_signed_t<T> i, std::make_unsigned_t<T> n) {
  const auto ns = std::make_signed_t<T>(n);
  return std::make_unsigned_t<T>((i % ns + ns) % ns);
}

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

struct EncodedBitmaskImmediate {
  uint8_t n{};
  uint8_t imms{};
  uint8_t immr{};

  static bool from_bitmask(uint64_t value, EncodedBitmaskImmediate& encoded) {
    // https://kddnewton.com/2022/08/11/aarch64-bitmask-immediates.html

    constexpr static auto is_mask = [](uint64_t imm) { return ((imm + 1) & imm) == 0; };
    constexpr static auto is_shifted_mask = [](uint64_t imm) { return is_mask((imm - 1) | imm); };

    if (value == 0 || value == std::numeric_limits<uint64_t>::max()) {
      return false;
    }

    uint64_t imm = value;
    uint32_t size = 64;

    while (true) {
      size >>= 1;
      const auto mask = (uint64_t(1) << size) - 1;

      if ((imm & mask) != ((imm >> size) & mask)) {
        size <<= 1;
        break;
      }

      if (size <= 2) {
        break;
      }
    }

    const auto mask = std::numeric_limits<uint64_t>::max() >> (64 - size);

    imm &= mask;

    uint32_t trailing_ones = 0;
    uint32_t left_rotations = 0;

    if (is_shifted_mask(imm)) {
      left_rotations = std::countr_zero(imm);
      trailing_ones = std::countr_one(imm >> left_rotations);
    } else {
      imm |= ~mask;

      if (!is_shifted_mask(~imm)) {
        return false;
      }

      const auto leading_ones = std::countl_one(imm);

      left_rotations = 64 - leading_ones;
      trailing_ones = leading_ones + std::countr_one(imm) - (64 - size);
    }

    const auto immr = (size - left_rotations) & (size - 1);
    const auto imms = (~(size - 1) << 1) | (trailing_ones - 1);
    const auto n = ((imms >> 6) & 1) ^ 1;

    encoded = {
      .n = uint8_t(n),
      .imms = uint8_t(imms & 0x3f),
      .immr = uint8_t(immr & 0x3f),
    };

    return true;
  }
};

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

Status Assembler::encode_add_sub_imm(Reg rd, Reg rn, uint64_t imm, bool sub_op, bool set_flags) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched, is_64bit == is_register_64bit(rn));
  A64_ASM_CHECK(ZrOperandForbidden, !is_register_zr(rd) && !is_register_zr(rn));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);

  uint32_t shift = 0;

  constexpr auto pow12 = uint64_t(1) << 12;
  if (imm >= pow12) {
    A64_ASM_CHECK(UImmTooLarge, (imm & (pow12 - 1)) == 0);

    shift = 1;
    imm = imm >> 12;

    A64_ASM_CHECK(UImmTooLarge, imm < pow12);
  }

  emit((uint32_t(is_64bit) << 31) | (uint32_t(sub_op) << 30) | (uint32_t(set_flags) << 29) |
       (uint32_t(0b100010) << 23) | (uint32_t(shift) << 22) | (uint32_t(imm) << 10) |
       (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_add_sub_shifted(Reg rd,
                                         Reg rn,
                                         Reg rm,
                                         uint32_t shift_amount,
                                         Shift shift,
                                         bool sub_op,
                                         bool set_flags) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched,
                is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm));
  A64_ASM_CHECK(SpOperandForbidden,
                !is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm));
  A64_ASM_CHECK(ShiftTypeInvalid,
                shift == Shift::Lsl || shift == Shift::Lsr || shift == Shift::Asr);
  A64_ASM_CHECK(UImmTooLarge, fits_within_bits_unsigned(shift_amount, 6));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(sub_op) << 30) | (uint32_t(set_flags) << 29) |
       (uint32_t(0b01011) << 24) | (uint32_t(shift) << 22) | (uint32_t(rmi) << 16) |
       (uint32_t(shift_amount) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_bitwise_imm(Reg rd, Reg rn, uint64_t imm, uint32_t opc) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched, is_64bit == is_register_64bit(rn));
  A64_ASM_CHECK(ZrOperandForbidden, !is_register_zr(rd) && !is_register_zr(rn));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);

  EncodedBitmaskImmediate encoded_bitmask;
  const auto can_encode = EncodedBitmaskImmediate::from_bitmask(imm, encoded_bitmask);
  A64_ASM_CHECK(BitmaskInvalid, can_encode);

  if (!is_64bit) {
    A64_ASM_CHECK(BitmaskInvalidFor32Bit, encoded_bitmask.n == 0);
  }

  emit((uint32_t(is_64bit) << 31) | (uint32_t(opc) << 29) | (uint32_t(0b100100) << 23) |
       (uint32_t(encoded_bitmask.n) << 22) | (uint32_t(encoded_bitmask.immr) << 16) |
       (uint32_t(encoded_bitmask.imms) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_bitwise_shifted(Reg rd,
                                         Reg rn,
                                         Reg rm,
                                         uint32_t shift_amount,
                                         Shift shift,
                                         uint32_t opc,
                                         bool invert) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched,
                is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm));
  A64_ASM_CHECK(SpOperandForbidden,
                !is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm));
  A64_ASM_CHECK(UImmTooLarge, fits_within_bits_unsigned(shift_amount, 6));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(opc) << 29) | (uint32_t(0b01010) << 24) |
       (uint32_t(shift) << 22) | (uint32_t(invert) << 21) | (uint32_t(rmi) << 16) |
       (uint32_t(shift_amount) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_move_wide(Reg rd, uint64_t imm, uint64_t shift, uint32_t opc) {
  const auto is_64bit = is_register_64bit(rd);
  const auto hw = shift / 16;

  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rd));

  A64_ASM_CHECK(ShiftAmountInvalid, hw * 16 == shift && shift <= 48);
  if (!is_64bit) {
    A64_ASM_CHECK(ShiftAmountInvalid, hw <= 1);
  }

  A64_ASM_CHECK(UImmTooLarge, fits_within_bits_unsigned(imm, 16));

  const auto rdi = register_index(rd);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(opc) << 29) | (uint32_t(0b100101) << 23) |
       (uint32_t(hw) << 21) | (uint32_t(imm) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_adr(Reg rd, Label label, uint32_t op) {
  A64_ASM_CHECK(Non64bitOperandForbidden, is_register_64bit(rd));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rd));

  const auto rdi = register_index(rd);

  emit_fixup(label, op == 0 ? Fixup::Type::Adr : Fixup::Type::Adrp);
  emit((uint32_t(op) << 31) | (uint32_t(0b10000) << 24) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_bitfield_move(Reg rd, Reg rn, uint64_t immr, uint64_t imms, uint32_t opc) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched, is_64bit == is_register_64bit(rn));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rd) && !is_register_sp(rn));

  const uint32_t max_imm_bits = is_64bit ? 6 : 5;
  A64_ASM_CHECK(UImmTooLarge, fits_within_bits_unsigned(immr, max_imm_bits) &&
                                fits_within_bits_unsigned(imms, max_imm_bits));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(opc) << 29) | (uint32_t(0b100110) << 23) |
       (uint32_t(is_64bit) << 22) | (uint32_t(immr) << 16) | (uint32_t(imms) << 10) |
       (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_extr(Reg rd, Reg rn, Reg rm, uint64_t lsb) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched,
                is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm));
  A64_ASM_CHECK(SpOperandForbidden,
                !is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm));

  const uint32_t max_imm_bits = is_64bit ? 6 : 5;
  A64_ASM_CHECK(UImmTooLarge, fits_within_bits_unsigned(lsb, max_imm_bits));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b100111) << 23) |
       (uint32_t(is_64bit << 22) | (uint32_t(rmi) << 16) | (uint32_t(lsb) << 10) |
        (uint32_t(rni) << 5) | (uint32_t(rdi) << 0)));

  return {};
}

Status Assembler::encode_shift_reg(Reg rd, Reg rn, Reg rm, uint32_t op2) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched,
                is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm));
  A64_ASM_CHECK(SpOperandForbidden,
                !is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b0011010110) << 21) | (uint32_t(rmi) << 16) |
       (uint32_t(0b0010) << 12) | (uint32_t(op2) << 10) | (uint32_t(rni) << 5) |
       (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_mul(Reg rd, Reg rn, Reg rm, Reg ra, uint32_t op) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched, is_64bit == is_register_64bit(rn) &&
                                       is_64bit == is_register_64bit(rm) &&
                                       is_64bit == is_register_64bit(ra));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rd) && !is_register_sp(rn) &&
                                      !is_register_sp(rm) && !is_register_sp(ra));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);
  const auto rai = register_index(ra);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b0011011000) << 21) | (uint32_t(rmi) << 16) |
       (uint32_t(op) << 15) | (uint32_t(rai) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_div(Reg rd, Reg rn, Reg rm, uint32_t op) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched,
                is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm));
  A64_ASM_CHECK(SpOperandForbidden,
                !is_register_sp(rd) && !is_register_sp(rn) && !is_register_sp(rm));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b0011010110) << 21) | (uint32_t(rmi) << 16) |
       (uint32_t(0b00001) << 11) | (uint32_t(op) << 10) | (uint32_t(rni) << 5) |
       (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_bit_scan(Reg rd, Reg rn, uint32_t op) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched, is_64bit == is_register_64bit(rn));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rd) && !is_register_sp(rn));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b10110101100000000010) << 11) |
       (uint32_t(op) << 10) | (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_cond_select(Reg rd,
                                     Reg rn,
                                     Reg rm,
                                     Condition condition,
                                     uint32_t op,
                                     uint32_t o2) {
  const auto is_64bit = is_register_64bit(rd);

  A64_ASM_CHECK(RegistersMismatched,
                is_64bit == is_register_64bit(rn) && is_64bit == is_register_64bit(rm));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rd) && !is_register_sp(rn));

  const auto rdi = register_index(rd);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  emit((uint32_t(is_64bit) << 31) | (uint32_t(op) << 30) | (uint32_t(0b011010100) << 21) |
       (uint32_t(rmi) << 16) | (uint32_t(condition) << 12) | (uint32_t(o2) << 10) |
       (uint32_t(rni) << 5) | (uint32_t(rdi) << 0));

  return {};
}

Status Assembler::encode_mem_imm_unscaled(Reg rt,
                                          Reg rn,
                                          int64_t imm,
                                          uint32_t size,
                                          uint32_t opc) {
  A64_ASM_CHECK(Non64bitAddressForbidden, is_register_64bit(rn));
  A64_ASM_CHECK(ZrOperandForbidden, !is_register_zr(rn));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rt));
  A64_ASM_CHECK(SImmTooLarge, fits_within_bits_signed(imm, 9));

  const auto rti = register_index(rt);
  const auto rni = register_index(rn);

  emit((uint32_t(size) << 30) | (uint32_t(0b111000) << 24) | (uint32_t(opc) << 22) |
       ((uint32_t(imm) & 0b111'111'111) << 12) | (uint32_t(rni) << 5) | (uint32_t(rti) << 0));

  return {};
}

Status Assembler::encode_mem_imm_unsigned_offset(Reg rt,
                                                 Reg rn,
                                                 uint64_t imm,
                                                 uint32_t size,
                                                 uint32_t opc) {
  A64_ASM_CHECK(Non64bitAddressForbidden, is_register_64bit(rn));
  A64_ASM_CHECK(ZrOperandForbidden, !is_register_zr(rn));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rt));
  A64_ASM_CHECK(UImmTooLarge, fits_within_bits_unsigned(imm, 12));

  const auto rti = register_index(rt);
  const auto rni = register_index(rn);

  emit((uint32_t(size) << 30) | (uint32_t(0b111001) << 24) | (uint32_t(opc) << 22) |
       ((uint32_t(imm) & 0b111'111'111'111) << 10) | (uint32_t(rni) << 5) | (uint32_t(rti) << 0));

  return {};
}

Status Assembler::encode_mem_imm_writeback(Reg rt,
                                           Reg rn,
                                           int64_t imm,
                                           uint32_t size,
                                           uint32_t opc,
                                           bool post_index) {
  A64_ASM_CHECK(Non64bitAddressForbidden, is_register_64bit(rn));
  A64_ASM_CHECK(ZrOperandForbidden, !is_register_zr(rn));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rt));
  A64_ASM_CHECK(SImmTooLarge, fits_within_bits_signed(imm, 9));

  const auto rti = register_index(rt);
  const auto rni = register_index(rn);

  const auto op2 = post_index ? 0b01 : 0b11;

  emit((uint32_t(size) << 30) | (uint32_t(0b111000) << 24) | (uint32_t(opc) << 22) |
       ((uint32_t(imm) & 0b111'111'111) << 12) | (uint32_t(op2) << 10) | (uint32_t(rni) << 5) |
       (uint32_t(rti) << 0));

  return {};
}

Status Assembler::encode_mem_imm(Reg rt,
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

Status Assembler::encode_mem_reg(Reg rt,
                                 Reg rn,
                                 Reg rm,
                                 Scale scale,
                                 Extend extend,
                                 uint32_t size,
                                 uint32_t opc) {
  A64_ASM_CHECK(Non64bitAddressForbidden, is_register_64bit(rn));
  A64_ASM_CHECK(ZrOperandForbidden, !is_register_zr(rn));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rt) && !is_register_sp(rn));

  const auto rti = register_index(rt);
  const auto rni = register_index(rn);
  const auto rmi = register_index(rm);

  const auto option = uint32_t(extend);
  const auto s = scale == Scale::DataSize ? 1 : 0;

  emit((uint32_t(size) << 30) | (uint32_t(0b111000) << 24) | (uint32_t(opc) << 22) |
       (uint32_t(0b1) << 21) | (uint32_t(rmi) << 16) | (uint32_t(option) << 13) |
       (uint32_t(s) << 12) | (uint32_t(0b1) << 11) | (uint32_t(rni) << 5) | (uint32_t(rti) << 0));

  return {};
}

Status Assembler::encode_mem_label(Reg rt, Label label, uint32_t opc) {
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rt));

  const auto rti = register_index(rt);

  emit_fixup(label, Fixup::Type::Bcond_Cb_Ldr);
  emit((uint32_t(opc) << 30) | (uint32_t(0b011000) << 24) | (uint32_t(rti) << 0));

  return {};
}

Status Assembler::encode_mem_pair(Reg rt1,
                                  Reg rt2,
                                  Reg rn,
                                  int64_t imm,
                                  Writeback writeback,
                                  uint32_t opc,
                                  uint32_t l) {
  A64_ASM_CHECK(Non64bitAddressForbidden, is_register_64bit(rn));
  A64_ASM_CHECK(ZrOperandForbidden, !is_register_zr(rn));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rt1) && !is_register_sp(rt2));
  A64_ASM_CHECK(RegistersMismatched, is_register_64bit(rt1) == is_register_64bit(rt2));

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
  A64_ASM_CHECK(MemoryOffsetUnaligned, (scaled_imm << scale) == imm);
  A64_ASM_CHECK(SImmTooLarge, fits_within_bits_signed(scaled_imm, 7));

  emit((uint32_t(opc) << 30) | (uint32_t(0b10100) << 25) | (uint32_t(writeback_c) << 23) |
       (uint32_t(l) << 22) | ((uint32_t(scaled_imm) & 0b1111111) << 15) | (uint32_t(rt2i) << 10) |
       (uint32_t(rni) << 5) | (uint32_t(rt1i) << 0));

  return {};
}

Status Assembler::encode_cb(Reg rt, Label label, uint32_t op) {
  const auto is_64bit = is_register_64bit(rt);

  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rt));

  const auto rti = register_index(rt);

  emit_fixup(label, Fixup::Type::Bcond_Cb_Ldr);
  emit((uint32_t(is_64bit) << 31) | (uint32_t(0b011010) << 25) | (uint32_t(op) << 24) |
       ((uint32_t(rti) << 0)));

  return {};
}

Status Assembler::encode_tb(Reg rt, uint64_t bit, Label label, uint32_t op) {
  const auto is_64bit = is_register_64bit(rt);

  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rt));
  A64_ASM_CHECK(UImmTooLarge, bit < (is_64bit ? 64 : 32));

  const auto rti = register_index(rt);

  emit_fixup(label, Fixup::Type::Tb);
  emit((uint32_t(bit >= 32) << 31) | (uint32_t(0b011011) << 25) | (uint32_t(op) << 24) |
       (uint32_t(bit & 0b11111) << 19) | ((uint32_t(rti) << 0)));

  return {};
}

Status Assembler::encode_b_imm(Label label, bool op) {
  emit_fixup(label, Fixup::Type::B);
  emit((uint32_t(op) << 31) | (uint32_t(0b00101) << 26));

  return {};
}

Status Assembler::encode_br_indirect(Reg rn, uint32_t op) {
  A64_ASM_CHECK(Non64bitOperandForbidden, is_register_64bit(rn));
  A64_ASM_CHECK(SpOperandForbidden, !is_register_sp(rn));

  const auto rni = register_index(rn);

  emit((uint32_t(0b1101011000011111000000) << 10) | (uint32_t(op) << 21) | (uint32_t(rni) << 5));

  return {};
}

void Assembler::assert_instruction_encoded(const char* instruction_name, Status status) {
  if (!status) {
    const auto description = status_code_description(status.code());

#ifdef A64_ASM_HAS_FORMATTED_ASSERT
    A64_ASM_ASSERT(false, "encoding `{}` has failed: {}", instruction_name, description);
#else
    A64_ASM_ASSERT(false, description);
#endif
  }
}

Status Assembler::try_add(Reg rd, Reg rn, uint64_t imm) {
  return encode_add_sub_imm(rd, rn, imm, false, false);
}
Status Assembler::try_adds(Reg rd, Reg rn, uint64_t imm) {
  return encode_add_sub_imm(rd, rn, imm, false, true);
}
Status Assembler::try_sub(Reg rd, Reg rn, uint64_t imm) {
  return encode_add_sub_imm(rd, rn, imm, true, false);
}
Status Assembler::try_subs(Reg rd, Reg rn, uint64_t imm) {
  return encode_add_sub_imm(rd, rn, imm, true, true);
}
Status Assembler::try_cmp(Reg rn, uint64_t imm) {
  return try_subs(to_zero(rn), rn, imm);
}
Status Assembler::try_cmn(Reg rn, uint64_t imm) {
  return try_adds(to_zero(rn), rn, imm);
}

Status Assembler::try_and_(Reg rd, Reg rn, uint64_t imm) {
  return encode_bitwise_imm(rd, rn, imm, 0b00);
}
Status Assembler::try_ands(Reg rd, Reg rn, uint64_t imm) {
  return encode_bitwise_imm(rd, rn, imm, 0b11);
}
Status Assembler::try_eor(Reg rd, Reg rn, uint64_t imm) {
  return encode_bitwise_imm(rd, rn, imm, 0b10);
}
Status Assembler::try_orr(Reg rd, Reg rn, uint64_t imm) {
  return encode_bitwise_imm(rd, rn, imm, 0b01);
}
Status Assembler::try_tst(Reg rn, uint64_t imm) {
  return try_ands(to_zero(rn), rn, imm);
}

Status Assembler::try_movz(Reg rd, uint64_t imm, uint64_t shift) {
  return encode_move_wide(rd, imm, shift, 0b10);
}
Status Assembler::try_movk(Reg rd, uint64_t imm, uint64_t shift) {
  return encode_move_wide(rd, imm, shift, 0b11);
}
Status Assembler::try_movn(Reg rd, uint64_t imm, uint64_t shift) {
  return encode_move_wide(rd, imm, shift, 0b00);
}

Status Assembler::try_mov(Reg rd, uint64_t imm) {
  // Try movz.
  {
    const auto value = imm;
    const auto shift = (std::countr_zero(value) / 16) * 16;
    const auto shifted = value >> shift;
    if (fits_within_bits_unsigned(shifted, 16)) {
      return try_movz(rd, shifted, shift);
    }
  }

  // Invert imm and try movn.
  {
    const auto value = ~imm;
    const auto shift = (std::countr_zero(value) / 16) * 16;
    const auto shifted = value >> shift;
    if (fits_within_bits_unsigned(shifted, 16)) {
      return try_movn(rd, shifted, shift);
    }
  }

  // Try using bitmask encoding.
  return try_orr(rd, to_zero(rd), imm);
}

Status Assembler::try_adr(Reg rd, Label label) {
  return encode_adr(rd, label, 0);
}
Status Assembler::try_adrp(Reg rd, Label label) {
  return encode_adr(rd, label, 1);
}

Status Assembler::try_bfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms) {
  return encode_bitfield_move(rd, rn, immr, imms, 0b01);
}
Status Assembler::try_sbfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms) {
  return encode_bitfield_move(rd, rn, immr, imms, 0b00);
}
Status Assembler::try_ubfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms) {
  return encode_bitfield_move(rd, rn, immr, imms, 0b10);
}

Status Assembler::try_bfc(Reg rd, uint64_t lsb, uint64_t width) {
  return try_bfi(rd, to_zero(rd), lsb, width);
}
Status Assembler::try_bfi(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto immr = positive_modulo<uint32_t>(-int32_t(lsb), is_register_64bit(rd) ? 64 : 32);
  return try_bfm(rd, rn, immr, width - 1);
}
Status Assembler::try_bfxil(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  return try_bfm(rd, rn, lsb, lsb + width - 1);
}
Status Assembler::try_sbfiz(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto immr = positive_modulo<uint32_t>(-int32_t(lsb), is_register_64bit(rd) ? 64 : 32);
  return try_sbfm(rd, rn, immr, width - 1);
}
Status Assembler::try_sbfx(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  return try_sbfm(rd, rn, lsb, lsb + width - 1);
}
Status Assembler::try_ubfiz(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto immr = positive_modulo<uint32_t>(-int32_t(lsb), is_register_64bit(rd) ? 64 : 32);
  return try_ubfm(rd, rn, immr, width - 1);
}
Status Assembler::try_ubfx(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  return try_ubfm(rd, rn, lsb, lsb + width - 1);
}

Status Assembler::try_extr(Reg rd, Reg rn, Reg rm, uint64_t lsb) {
  return encode_extr(rd, rn, rm, lsb);
}

Status Assembler::try_asr(Reg rd, Reg rn, uint64_t shift) {
  return try_sbfm(rd, rn, shift, is_register_64bit(rd) ? 63 : 31);
}
Status Assembler::try_lsl(Reg rd, Reg rn, uint64_t shift) {
  const auto immr = positive_modulo<uint32_t>(-int32_t(shift), is_register_64bit(rd) ? 64 : 32);
  return try_ubfm(rd, rn, immr, (is_register_64bit(rd) ? 63 : 31) - shift);
}
Status Assembler::try_lsr(Reg rd, Reg rn, uint64_t shift) {
  return try_ubfm(rd, rn, shift, is_register_64bit(rd) ? 63 : 31);
}
Status Assembler::try_ror(Reg rd, Reg rn, uint64_t shift) {
  return try_extr(rd, rn, rn, shift);
}

Status Assembler::try_sxtb(Reg rd, Reg rn) {
  return try_sbfm(rd, rn, 0, 7);
}
Status Assembler::try_sxth(Reg rd, Reg rn) {
  return try_sbfm(rd, rn, 0, 15);
}
Status Assembler::try_sxtw(Reg rd, Reg rn) {
  return try_sbfm(rd, rn, 0, 31);
}
Status Assembler::try_uxtb(Reg rd, Reg rn) {
  return try_ubfm(rd, rn, 0, 7);
}
Status Assembler::try_uxth(Reg rd, Reg rn) {
  return try_ubfm(rd, rn, 0, 15);
}

Status Assembler::try_add(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_add_sub_shifted(rd, rn, rm, shift_amount, shift, false, false);
}
Status Assembler::try_adds(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_add_sub_shifted(rd, rn, rm, shift_amount, shift, false, true);
}
Status Assembler::try_sub(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_add_sub_shifted(rd, rn, rm, shift_amount, shift, true, false);
}
Status Assembler::try_subs(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_add_sub_shifted(rd, rn, rm, shift_amount, shift, true, true);
}
Status Assembler::try_cmp(Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return try_subs(to_zero(rn), rn, rm, shift_amount, shift);
}
Status Assembler::try_cmn(Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return try_adds(to_zero(rn), rn, rm, shift_amount, shift);
}
Status Assembler::try_neg(Reg rd, Reg rm, uint64_t shift_amount, Shift shift) {
  return try_sub(rd, to_zero(rm), rm, shift_amount, shift);
}
Status Assembler::try_negs(Reg rd, Reg rm, uint64_t shift_amount, Shift shift) {
  return try_subs(rd, to_zero(rm), rm, shift_amount, shift);
}

Status Assembler::try_and_(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b00, false);
}
Status Assembler::try_ands(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b11, false);
}
Status Assembler::try_bic(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b00, true);
}
Status Assembler::try_bics(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b11, true);
}
Status Assembler::try_eor(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b10, false);
}
Status Assembler::try_eon(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b10, true);
}
Status Assembler::try_orr(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b01, false);
}
Status Assembler::try_orn(Reg rd, Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return encode_bitwise_shifted(rd, rn, rm, shift_amount, shift, 0b01, true);
}
Status Assembler::try_mvn(Reg rd, Reg rm, uint64_t shift_amount, Shift shift) {
  return try_orn(rd, to_zero(rm), rm, shift_amount, shift);
}
Status Assembler::try_tst(Reg rn, Reg rm, uint64_t shift_amount, Shift shift) {
  return try_ands(to_zero(rn), rn, rm, shift_amount, shift);
}
Status Assembler::try_mov(Reg rd, Reg rn) {
  if (is_register_sp(rd) || is_register_sp(rn)) {
    return try_add(rd, rn, 0);
  } else {
    return try_orr(rd, to_zero(rd), rn);
  }
}

Status Assembler::try_asr(Reg rd, Reg rn, Reg rm) {
  return encode_shift_reg(rd, rn, rm, 0b10);
}
Status Assembler::try_lsl(Reg rd, Reg rn, Reg rm) {
  return encode_shift_reg(rd, rn, rm, 0b00);
}
Status Assembler::try_lsr(Reg rd, Reg rn, Reg rm) {
  return encode_shift_reg(rd, rn, rm, 0b01);
}
Status Assembler::try_ror(Reg rd, Reg rn, Reg rm) {
  return encode_shift_reg(rd, rn, rm, 0b11);
}

Status Assembler::try_madd(Reg rd, Reg rn, Reg rm, Reg ra) {
  return encode_mul(rd, rn, rm, ra, 0);
}
Status Assembler::try_msub(Reg rd, Reg rn, Reg rm, Reg ra) {
  return encode_mul(rd, rn, rm, ra, 1);
}
Status Assembler::try_mneg(Reg rd, Reg rn, Reg rm) {
  return try_msub(rd, rn, rm, to_zero(rm));
}
Status Assembler::try_mul(Reg rd, Reg rn, Reg rm) {
  return try_madd(rd, rn, rm, to_zero(rm));
}

Status Assembler::try_sdiv(Reg rd, Reg rn, Reg rm) {
  return encode_div(rd, rn, rm, 1);
}
Status Assembler::try_udiv(Reg rd, Reg rn, Reg rm) {
  return encode_div(rd, rn, rm, 0);
}

Status Assembler::try_cls(Reg rd, Reg rn) {
  return encode_bit_scan(rd, rn, 1);
}
Status Assembler::try_clz(Reg rd, Reg rn) {
  return encode_bit_scan(rd, rn, 0);
}

Status Assembler::try_csel(Reg rd, Reg rn, Reg rm, Condition condition) {
  return encode_cond_select(rd, rn, rm, condition, 0, 0);
}
Status Assembler::try_csinc(Reg rd, Reg rn, Reg rm, Condition condition) {
  return encode_cond_select(rd, rn, rm, condition, 0, 1);
}
Status Assembler::try_cset(Reg rd, Condition condition) {
  return try_csinc(rd, to_zero(rd), to_zero(rd), condition);
}

Status Assembler::try_ldr(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_imm(rt, rn, imm, writeback, is_register_64bit(rt) ? 0b11 : 0b10, 0b01);
}
Status Assembler::try_ldrh(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_imm(rt, rn, imm, writeback, 0b01, 0b01);
}
Status Assembler::try_ldrb(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_imm(rt, rn, imm, writeback, 0b00, 0b01);
}
Status Assembler::try_ldrsw(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  A64_ASM_CHECK(Non64bitOperandForbidden, is_register_64bit(rt));
  return encode_mem_imm(rt, rn, imm, writeback, 0b10, 0b10);
}
Status Assembler::try_ldrsh(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_imm(rt, rn, imm, writeback, 0b01, is_register_64bit(rt) ? 0b10 : 0b11);
}
Status Assembler::try_ldrsb(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_imm(rt, rn, imm, writeback, 0b00, is_register_64bit(rt) ? 0b10 : 0b11);
}

Status Assembler::try_str(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_imm(rt, rn, imm, writeback, is_register_64bit(rt) ? 0b11 : 0b10, 0b00);
}
Status Assembler::try_strh(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_imm(rt, rn, imm, writeback, 0b01, 0b00);
}
Status Assembler::try_strb(Reg rt, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_imm(rt, rn, imm, writeback, 0b00, 0b00);
}

Status Assembler::try_ldr(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  return encode_mem_reg(rt, rn, rm, scale, extend, is_register_64bit(rt) ? 0b11 : 0b10, 0b01);
}
Status Assembler::try_ldrh(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  return encode_mem_reg(rt, rn, rm, scale, extend, 0b01, 0b01);
}
Status Assembler::try_ldrb(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  return encode_mem_reg(rt, rn, rm, scale, extend, 0b00, 0b01);
}
Status Assembler::try_ldrsw(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  A64_ASM_CHECK(Non64bitOperandForbidden, is_register_64bit(rt));
  return encode_mem_reg(rt, rn, rm, scale, extend, 0b10, 0b10);
}
Status Assembler::try_ldrsh(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  return encode_mem_reg(rt, rn, rm, scale, extend, 0b01, is_register_64bit(rt) ? 0b10 : 0b11);
}
Status Assembler::try_ldrsb(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  return encode_mem_reg(rt, rn, rm, scale, extend, 0b00, is_register_64bit(rt) ? 0b10 : 0b11);
}

Status Assembler::try_str(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  return encode_mem_reg(rt, rn, rm, scale, extend, is_register_64bit(rt) ? 0b11 : 0b10, 0b00);
}
Status Assembler::try_strh(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  return encode_mem_reg(rt, rn, rm, scale, extend, 0b01, 0b00);
}
Status Assembler::try_strb(Reg rt, Reg rn, Reg rm, Scale scale, Extend extend) {
  return encode_mem_reg(rt, rn, rm, scale, extend, 0b00, 0b00);
}

Status Assembler::try_ldr(Reg rt, Label label) {
  return encode_mem_label(rt, label, is_register_64bit(rt) ? 0b01 : 0b00);
}
Status Assembler::try_ldrsw(Reg rt, Label label) {
  A64_ASM_CHECK(Non64bitOperandForbidden, is_register_64bit(rt));
  return encode_mem_label(rt, label, 0b10);
}

Status Assembler::try_ldp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_pair(rt1, rt2, rn, imm, writeback, is_register_64bit(rt1) ? 0b10 : 0b00, 1);
}
Status Assembler::try_ldpsw(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback) {
  A64_ASM_CHECK(Non64bitOperandForbidden, is_register_64bit(rt1));
  return encode_mem_pair(rt1, rt2, rn, imm, writeback, 0b01, 1);
}
Status Assembler::try_stp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback) {
  return encode_mem_pair(rt1, rt2, rn, imm, writeback, is_register_64bit(rt1) ? 0b10 : 0b00, 0);
}

Status Assembler::try_b(Condition condition, Label label) {
  emit_fixup(label, Fixup::Type::Bcond_Cb_Ldr);
  emit((uint32_t(0b01010100) << 24) | (uint32_t(condition) << 0));
  return {};
}

Status Assembler::try_cbz(Reg rt, Label label) {
  return encode_cb(rt, label, 0);
}
Status Assembler::try_cbnz(Reg rt, Label label) {
  return encode_cb(rt, label, 1);
}
Status Assembler::try_tbz(Reg rt, uint64_t bit, Label label) {
  return encode_tb(rt, bit, label, 0);
}
Status Assembler::try_tbnz(Reg rt, uint64_t bit, Label label) {
  return encode_tb(rt, bit, label, 1);
}

Status Assembler::try_b(Label label) {
  return encode_b_imm(label, false);
}

Status Assembler::try_bl(Label label) {
  return encode_b_imm(label, true);
}

Status Assembler::try_blr(Reg rn) {
  return encode_br_indirect(rn, 0b01);
}

Status Assembler::try_br(Reg rn) {
  return encode_br_indirect(rn, 0b00);
}

Status Assembler::try_ret(Reg rn) {
  return encode_br_indirect(rn, 0b10);
}

Status Assembler::try_svc(uint16_t imm) {
  emit((uint32_t(0b11010100000) << 21) | (uint32_t(imm) << 5) | (uint32_t(1) << 0));
  return {};
}
Status Assembler::try_brk(uint16_t imm) {
  emit((uint32_t(0b11010100001) << 21) | (uint32_t(imm) << 5));
  return {};
}

Label Assembler::allocate_label() {
  const auto index = labels.size();
  labels.emplace_back(std::numeric_limits<uint64_t>::max());
  return Label{index};
}

void Assembler::insert_label(Label label) {
  A64_ASM_ASSERT(labels[label.index] == std::numeric_limits<uint64_t>::max(),
                 "label was already inserted into the instruction stream");
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
    A64_ASM_ASSERT(target != std::numeric_limits<uint64_t>::max(),
                   "fixup label was not inserted into the instruction stream");

    uint32_t size{};
    uint32_t shift{};

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
        uint64_t current = fixup.location;
        uint64_t target_adjusted = fixup.label;

        // Remove bottom 12 bits for adrp.
        if (fixup.type == Fixup::Type::Adrp) {
          current &= ~uint64_t(0xfff);
          target_adjusted &= ~uint64_t(0xfff);
        }

        const auto delta = int64_t(target_adjusted) - int64_t(current);
        const auto delta2 = fixup.type == Fixup::Type::Adrp ? (delta >> 12) : delta;

        A64_ASM_ASSERT(fits_within_bits_signed(delta2, 21),
                       "cannot process fixup: adr/adrp delta doesn't fit in the imm field");

        const auto delta_masked = uint64_t(delta2 & ((uint32_t(1) << 21) - 1));

        instructions[fixup.location] |= (delta_masked & 0b11) << 29;
        instructions[fixup.location] |= (delta_masked >> 2) << 5;
        skip = true;

        break;
      }

      default: {
        A64_ASM_ASSERT(false, "unknown fixup type");
      }
    }

    const auto delta = int64_t(target) - int64_t(fixup.location);

    if (!skip) {
      A64_ASM_ASSERT(fits_within_bits_signed(delta, size),
                     "cannot process fixup: delta doesn't fit in the imm field");
      instructions[fixup.location] |= uint64_t(delta & ((uint32_t(1) << size) - 1)) << shift;
    }
  }

  fixups.clear();
}

std::span<const uint32_t> Assembler::assembled_instructions() const {
  return instructions;
}