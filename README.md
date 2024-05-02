# AArch64 assembler library in C++20

```cpp
using a64::Register;

a64::Assembler as;

as.clz(Register::X1, Register::X2);
as.mul(Register::W4, Register::W7, Register::Wzr);

const auto label = as.insert_label();

as.sub(Register::X2, Register::X2, 2);
as.cbnz(Register::X2, label);

as.str(Register::X3, Register::X5, 16);
as.str(Register::X8, Register::X5, 16, a64::Writeback::Post);

for (const auto inst : as.assembled_instructions()) {
    const auto reversed = (((inst >> 24) & 0xff) << 0) | (((inst >> 16) & 0xff) << 8) |
                          (((inst >> 8) & 0xff) << 16) | (((inst >> 0) & 0xff) << 24);
    fmt::println("{:08x}", reversed);
}
```

```hexdump
0x0000000000000000:  41 10 C0 DA    clz  x1, x2
0x0000000000000004:  E4 7C 1F 1B    mul  w4, w7, wzr
0x0000000000000008:  42 08 00 D1    sub  x2, x2, #2
0x000000000000000c:  E2 FF FF B5    cbnz x2, #8
0x0000000000000010:  A3 08 00 F9    str  x3, [x5, #0x10]
0x0000000000000014:  A8 04 01 F8    str  x8, [x5], #0x10
```
