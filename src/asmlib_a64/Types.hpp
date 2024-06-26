#pragma once
#include <cstdint>

namespace asmlib::a64 {

enum class Register {
  X0,
  X1,
  X2,
  X3,
  X4,
  X5,
  X6,
  X7,
  X8,
  X9,
  X10,
  X11,
  X12,
  X13,
  X14,
  X15,
  X16,
  X17,
  X18,
  X19,
  X20,
  X21,
  X22,
  X23,
  X24,
  X25,
  X26,
  X27,
  X28,
  X29,
  X30,
  Xzr,
  Sp,

  W0,
  W1,
  W2,
  W3,
  W4,
  W5,
  W6,
  W7,
  W8,
  W9,
  W10,
  W11,
  W12,
  W13,
  W14,
  W15,
  W16,
  W17,
  W18,
  W19,
  W20,
  W21,
  W22,
  W23,
  W24,
  W25,
  W26,
  W27,
  W28,
  W29,
  W30,
  Wzr,
  Wsp,
};

enum class Shift {
  Lsl,
  Lsr,
  Asr,
  Ror,
};

enum class Condition {
  Equal,
  NotEqual,
  CarrySet,
  CarryClear,
  Minus,
  Plus,
  Overflow,
  NoOverflow,
  UnsignedGreater,
  UnsignedLessEqual,
  GreaterEqual,
  Less,
  Greater,
  LessEqual,
  Always,

  Zero = Equal,
  NotZero = NotEqual,

  UnsignedGreaterEqual = CarrySet,
  UnsignedLess = CarryClear,
};

enum class Writeback {
  None,
  Pre,
  Post,
};

enum class Extend {
  Uxtw = 0b010,
  Lsl = 0b011,
  Sxtw = 0b110,
  Sxtx = 0b111,
};

enum class Scale {
  None,
  DataSize,
};

inline Register cast_to_32bit(Register reg) {
  if (uint32_t(reg) >= uint32_t(Register::X0) && uint32_t(reg) <= uint32_t(Register::Sp)) {
    return Register(uint32_t(reg) - uint32_t(Register::X0) + uint32_t(Register::W0));
  }
  return reg;
}

inline Register cast_to_64bit(Register reg) {
  if (uint32_t(reg) >= uint32_t(Register::W0) && uint32_t(reg) <= uint32_t(Register::Wsp)) {
    return Register(uint32_t(reg) - uint32_t(Register::W0) + uint32_t(Register::X0));
  }
  return reg;
}

inline Condition invert_condition(Condition condition) {
  return Condition(uint32_t(condition) ^ 1);
}

}  // namespace asmlib::a64