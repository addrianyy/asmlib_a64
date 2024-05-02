[[nodiscard]] Status try_add(Register rd, Register rn, uint64_t imm);
[[nodiscard]] Status try_adds(Register rd, Register rn, uint64_t imm);
[[nodiscard]] Status try_sub(Register rd, Register rn, uint64_t imm);
[[nodiscard]] Status try_subs(Register rd, Register rn, uint64_t imm);
[[nodiscard]] Status try_cmp(Register rn, uint64_t imm);
[[nodiscard]] Status try_cmn(Register rn, uint64_t imm);
[[nodiscard]] Status try_and_(Register rd, Register rn, uint64_t imm);
[[nodiscard]] Status try_ands(Register rd, Register rn, uint64_t imm);
[[nodiscard]] Status try_eor(Register rd, Register rn, uint64_t imm);
[[nodiscard]] Status try_orr(Register rd, Register rn, uint64_t imm);
[[nodiscard]] Status try_tst(Register rn, uint64_t imm);
[[nodiscard]] Status try_movz(Register rd, uint64_t imm, uint64_t shift = 0);
[[nodiscard]] Status try_movk(Register rd, uint64_t imm, uint64_t shift = 0);
[[nodiscard]] Status try_movn(Register rd, uint64_t imm, uint64_t shift = 0);
[[nodiscard]] Status try_mov(Register rd, uint64_t imm);
[[nodiscard]] Status try_adr(Register rd, Label label);
[[nodiscard]] Status try_adrp(Register rd, Label label);
[[nodiscard]] Status try_bfm(Register rd, Register rn, uint64_t immr, uint64_t imms);
[[nodiscard]] Status try_sbfm(Register rd, Register rn, uint64_t immr, uint64_t imms);
[[nodiscard]] Status try_ubfm(Register rd, Register rn, uint64_t immr, uint64_t imms);
[[nodiscard]] Status try_bfc(Register rd, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_bfi(Register rd, Register rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_bfxil(Register rd, Register rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_sbfiz(Register rd, Register rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_sbfx(Register rd, Register rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_ubfiz(Register rd, Register rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_ubfx(Register rd, Register rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_extr(Register rd, Register rn, Register rm, uint64_t lsb);
[[nodiscard]] Status try_asr(Register rd, Register rn, uint64_t shift);
[[nodiscard]] Status try_lsl(Register rd, Register rn, uint64_t shift);
[[nodiscard]] Status try_lsr(Register rd, Register rn, uint64_t shift);
[[nodiscard]] Status try_ror(Register rd, Register rn, uint64_t shift);
[[nodiscard]] Status try_sxtb(Register rd, Register rn);
[[nodiscard]] Status try_sxth(Register rd, Register rn);
[[nodiscard]] Status try_sxtw(Register rd, Register rn);
[[nodiscard]] Status try_uxtb(Register rd, Register rn);
[[nodiscard]] Status try_uxth(Register rd, Register rn);
[[nodiscard]] Status try_add(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_adds(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_sub(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_subs(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_cmp(Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_cmn(Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_neg(Register rd, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_negs(Register rd, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_and_(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_ands(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_bic(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_bics(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_eor(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_eon(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_orr(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_orn(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_mvn(Register rd, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_tst(Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_mov(Register rd, Register rn);
[[nodiscard]] Status try_asr(Register rd, Register rn, Register rm);
[[nodiscard]] Status try_lsl(Register rd, Register rn, Register rm);
[[nodiscard]] Status try_lsr(Register rd, Register rn, Register rm);
[[nodiscard]] Status try_ror(Register rd, Register rn, Register rm);
[[nodiscard]] Status try_madd(Register rd, Register rn, Register rm, Register ra);
[[nodiscard]] Status try_msub(Register rd, Register rn, Register rm, Register ra);
[[nodiscard]] Status try_mneg(Register rd, Register rn, Register rm);
[[nodiscard]] Status try_mul(Register rd, Register rn, Register rm);
[[nodiscard]] Status try_sdiv(Register rd, Register rn, Register rm);
[[nodiscard]] Status try_udiv(Register rd, Register rn, Register rm);
[[nodiscard]] Status try_cls(Register rd, Register rn);
[[nodiscard]] Status try_clz(Register rd, Register rn);
[[nodiscard]] Status try_csel(Register rd, Register rn, Register rm, Condition condition);
[[nodiscard]] Status try_csinc(Register rd, Register rn, Register rm, Condition condition);
[[nodiscard]] Status try_cset(Register rd, Condition condition);
[[nodiscard]] Status try_ldr(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrh(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrb(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrsw(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrsh(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrsb(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_str(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_strh(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_strb(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldr(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrh(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrb(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrsw(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrsh(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrsb(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_str(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_strh(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_strb(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldr(Register rt, Label label);
[[nodiscard]] Status try_ldrsw(Register rt, Label label);
[[nodiscard]] Status try_ldp(Register rt1, Register rt2, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldpsw(Register rt1, Register rt2, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldar(Register rt, Register rn);
[[nodiscard]] Status try_ldarb(Register rt, Register rn);
[[nodiscard]] Status try_ldarh(Register rt, Register rn);
[[nodiscard]] Status try_stlr(Register rt, Register rn);
[[nodiscard]] Status try_stlrb(Register rt, Register rn);
[[nodiscard]] Status try_stlrh(Register rt, Register rn);
[[nodiscard]] Status try_stp(Register rt1, Register rt2, Register rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_b(Condition condition, Label label);
[[nodiscard]] Status try_cbz(Register rt, Label label);
[[nodiscard]] Status try_cbnz(Register rt, Label label);
[[nodiscard]] Status try_tbz(Register rt, uint64_t bit, Label label);
[[nodiscard]] Status try_tbnz(Register rt, uint64_t bit, Label label);
[[nodiscard]] Status try_b(Label label);
[[nodiscard]] Status try_bl(Label label);
[[nodiscard]] Status try_blr(Register rn);
[[nodiscard]] Status try_br(Register rn);
[[nodiscard]] Status try_ret(Register rn = Register::X30);
[[nodiscard]] Status try_svc(uint16_t imm);
[[nodiscard]] Status try_brk(uint16_t imm);
[[nodiscard]] Status try_macro_mov(Register rd, int64_t imm);


void add(Register rd, Register rn, uint64_t imm) {
  const auto status = try_add(rd, rn, imm);
  assert_instruction_encoded("add", status);
}
void adds(Register rd, Register rn, uint64_t imm) {
  const auto status = try_adds(rd, rn, imm);
  assert_instruction_encoded("adds", status);
}
void sub(Register rd, Register rn, uint64_t imm) {
  const auto status = try_sub(rd, rn, imm);
  assert_instruction_encoded("sub", status);
}
void subs(Register rd, Register rn, uint64_t imm) {
  const auto status = try_subs(rd, rn, imm);
  assert_instruction_encoded("subs", status);
}
void cmp(Register rn, uint64_t imm) {
  const auto status = try_cmp(rn, imm);
  assert_instruction_encoded("cmp", status);
}
void cmn(Register rn, uint64_t imm) {
  const auto status = try_cmn(rn, imm);
  assert_instruction_encoded("cmn", status);
}
void and_(Register rd, Register rn, uint64_t imm) {
  const auto status = try_and_(rd, rn, imm);
  assert_instruction_encoded("and_", status);
}
void ands(Register rd, Register rn, uint64_t imm) {
  const auto status = try_ands(rd, rn, imm);
  assert_instruction_encoded("ands", status);
}
void eor(Register rd, Register rn, uint64_t imm) {
  const auto status = try_eor(rd, rn, imm);
  assert_instruction_encoded("eor", status);
}
void orr(Register rd, Register rn, uint64_t imm) {
  const auto status = try_orr(rd, rn, imm);
  assert_instruction_encoded("orr", status);
}
void tst(Register rn, uint64_t imm) {
  const auto status = try_tst(rn, imm);
  assert_instruction_encoded("tst", status);
}
void movz(Register rd, uint64_t imm, uint64_t shift = 0) {
  const auto status = try_movz(rd, imm, shift);
  assert_instruction_encoded("movz", status);
}
void movk(Register rd, uint64_t imm, uint64_t shift = 0) {
  const auto status = try_movk(rd, imm, shift);
  assert_instruction_encoded("movk", status);
}
void movn(Register rd, uint64_t imm, uint64_t shift = 0) {
  const auto status = try_movn(rd, imm, shift);
  assert_instruction_encoded("movn", status);
}
void mov(Register rd, uint64_t imm) {
  const auto status = try_mov(rd, imm);
  assert_instruction_encoded("mov", status);
}
void adr(Register rd, Label label) {
  const auto status = try_adr(rd, label);
  assert_instruction_encoded("adr", status);
}
void adrp(Register rd, Label label) {
  const auto status = try_adrp(rd, label);
  assert_instruction_encoded("adrp", status);
}
void bfm(Register rd, Register rn, uint64_t immr, uint64_t imms) {
  const auto status = try_bfm(rd, rn, immr, imms);
  assert_instruction_encoded("bfm", status);
}
void sbfm(Register rd, Register rn, uint64_t immr, uint64_t imms) {
  const auto status = try_sbfm(rd, rn, immr, imms);
  assert_instruction_encoded("sbfm", status);
}
void ubfm(Register rd, Register rn, uint64_t immr, uint64_t imms) {
  const auto status = try_ubfm(rd, rn, immr, imms);
  assert_instruction_encoded("ubfm", status);
}
void bfc(Register rd, uint64_t lsb, uint64_t width) {
  const auto status = try_bfc(rd, lsb, width);
  assert_instruction_encoded("bfc", status);
}
void bfi(Register rd, Register rn, uint64_t lsb, uint64_t width) {
  const auto status = try_bfi(rd, rn, lsb, width);
  assert_instruction_encoded("bfi", status);
}
void bfxil(Register rd, Register rn, uint64_t lsb, uint64_t width) {
  const auto status = try_bfxil(rd, rn, lsb, width);
  assert_instruction_encoded("bfxil", status);
}
void sbfiz(Register rd, Register rn, uint64_t lsb, uint64_t width) {
  const auto status = try_sbfiz(rd, rn, lsb, width);
  assert_instruction_encoded("sbfiz", status);
}
void sbfx(Register rd, Register rn, uint64_t lsb, uint64_t width) {
  const auto status = try_sbfx(rd, rn, lsb, width);
  assert_instruction_encoded("sbfx", status);
}
void ubfiz(Register rd, Register rn, uint64_t lsb, uint64_t width) {
  const auto status = try_ubfiz(rd, rn, lsb, width);
  assert_instruction_encoded("ubfiz", status);
}
void ubfx(Register rd, Register rn, uint64_t lsb, uint64_t width) {
  const auto status = try_ubfx(rd, rn, lsb, width);
  assert_instruction_encoded("ubfx", status);
}
void extr(Register rd, Register rn, Register rm, uint64_t lsb) {
  const auto status = try_extr(rd, rn, rm, lsb);
  assert_instruction_encoded("extr", status);
}
void asr(Register rd, Register rn, uint64_t shift) {
  const auto status = try_asr(rd, rn, shift);
  assert_instruction_encoded("asr", status);
}
void lsl(Register rd, Register rn, uint64_t shift) {
  const auto status = try_lsl(rd, rn, shift);
  assert_instruction_encoded("lsl", status);
}
void lsr(Register rd, Register rn, uint64_t shift) {
  const auto status = try_lsr(rd, rn, shift);
  assert_instruction_encoded("lsr", status);
}
void ror(Register rd, Register rn, uint64_t shift) {
  const auto status = try_ror(rd, rn, shift);
  assert_instruction_encoded("ror", status);
}
void sxtb(Register rd, Register rn) {
  const auto status = try_sxtb(rd, rn);
  assert_instruction_encoded("sxtb", status);
}
void sxth(Register rd, Register rn) {
  const auto status = try_sxth(rd, rn);
  assert_instruction_encoded("sxth", status);
}
void sxtw(Register rd, Register rn) {
  const auto status = try_sxtw(rd, rn);
  assert_instruction_encoded("sxtw", status);
}
void uxtb(Register rd, Register rn) {
  const auto status = try_uxtb(rd, rn);
  assert_instruction_encoded("uxtb", status);
}
void uxth(Register rd, Register rn) {
  const auto status = try_uxth(rd, rn);
  assert_instruction_encoded("uxth", status);
}
void add(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_add(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("add", status);
}
void adds(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_adds(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("adds", status);
}
void sub(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_sub(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("sub", status);
}
void subs(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_subs(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("subs", status);
}
void cmp(Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_cmp(rn, rm, shift_amount, shift);
  assert_instruction_encoded("cmp", status);
}
void cmn(Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_cmn(rn, rm, shift_amount, shift);
  assert_instruction_encoded("cmn", status);
}
void neg(Register rd, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_neg(rd, rm, shift_amount, shift);
  assert_instruction_encoded("neg", status);
}
void negs(Register rd, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_negs(rd, rm, shift_amount, shift);
  assert_instruction_encoded("negs", status);
}
void and_(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_and_(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("and_", status);
}
void ands(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_ands(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("ands", status);
}
void bic(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_bic(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("bic", status);
}
void bics(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_bics(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("bics", status);
}
void eor(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_eor(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("eor", status);
}
void eon(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_eon(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("eon", status);
}
void orr(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_orr(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("orr", status);
}
void orn(Register rd, Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_orn(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("orn", status);
}
void mvn(Register rd, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_mvn(rd, rm, shift_amount, shift);
  assert_instruction_encoded("mvn", status);
}
void tst(Register rn, Register rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_tst(rn, rm, shift_amount, shift);
  assert_instruction_encoded("tst", status);
}
void mov(Register rd, Register rn) {
  const auto status = try_mov(rd, rn);
  assert_instruction_encoded("mov", status);
}
void asr(Register rd, Register rn, Register rm) {
  const auto status = try_asr(rd, rn, rm);
  assert_instruction_encoded("asr", status);
}
void lsl(Register rd, Register rn, Register rm) {
  const auto status = try_lsl(rd, rn, rm);
  assert_instruction_encoded("lsl", status);
}
void lsr(Register rd, Register rn, Register rm) {
  const auto status = try_lsr(rd, rn, rm);
  assert_instruction_encoded("lsr", status);
}
void ror(Register rd, Register rn, Register rm) {
  const auto status = try_ror(rd, rn, rm);
  assert_instruction_encoded("ror", status);
}
void madd(Register rd, Register rn, Register rm, Register ra) {
  const auto status = try_madd(rd, rn, rm, ra);
  assert_instruction_encoded("madd", status);
}
void msub(Register rd, Register rn, Register rm, Register ra) {
  const auto status = try_msub(rd, rn, rm, ra);
  assert_instruction_encoded("msub", status);
}
void mneg(Register rd, Register rn, Register rm) {
  const auto status = try_mneg(rd, rn, rm);
  assert_instruction_encoded("mneg", status);
}
void mul(Register rd, Register rn, Register rm) {
  const auto status = try_mul(rd, rn, rm);
  assert_instruction_encoded("mul", status);
}
void sdiv(Register rd, Register rn, Register rm) {
  const auto status = try_sdiv(rd, rn, rm);
  assert_instruction_encoded("sdiv", status);
}
void udiv(Register rd, Register rn, Register rm) {
  const auto status = try_udiv(rd, rn, rm);
  assert_instruction_encoded("udiv", status);
}
void cls(Register rd, Register rn) {
  const auto status = try_cls(rd, rn);
  assert_instruction_encoded("cls", status);
}
void clz(Register rd, Register rn) {
  const auto status = try_clz(rd, rn);
  assert_instruction_encoded("clz", status);
}
void csel(Register rd, Register rn, Register rm, Condition condition) {
  const auto status = try_csel(rd, rn, rm, condition);
  assert_instruction_encoded("csel", status);
}
void csinc(Register rd, Register rn, Register rm, Condition condition) {
  const auto status = try_csinc(rd, rn, rm, condition);
  assert_instruction_encoded("csinc", status);
}
void cset(Register rd, Condition condition) {
  const auto status = try_cset(rd, condition);
  assert_instruction_encoded("cset", status);
}
void ldr(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldr(rt, rn, imm, writeback);
  assert_instruction_encoded("ldr", status);
}
void ldrh(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrh(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrh", status);
}
void ldrb(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrb(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrb", status);
}
void ldrsw(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrsw(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrsw", status);
}
void ldrsh(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrsh(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrsh", status);
}
void ldrsb(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrsb(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrsb", status);
}
void str(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_str(rt, rn, imm, writeback);
  assert_instruction_encoded("str", status);
}
void strh(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_strh(rt, rn, imm, writeback);
  assert_instruction_encoded("strh", status);
}
void strb(Register rt, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_strb(rt, rn, imm, writeback);
  assert_instruction_encoded("strb", status);
}
void ldr(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldr(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldr", status);
}
void ldrh(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrh(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrh", status);
}
void ldrb(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrb(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrb", status);
}
void ldrsw(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrsw(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrsw", status);
}
void ldrsh(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrsh(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrsh", status);
}
void ldrsb(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrsb(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrsb", status);
}
void str(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_str(rt, rn, rm, scale, extend);
  assert_instruction_encoded("str", status);
}
void strh(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_strh(rt, rn, rm, scale, extend);
  assert_instruction_encoded("strh", status);
}
void strb(Register rt, Register rn, Register rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_strb(rt, rn, rm, scale, extend);
  assert_instruction_encoded("strb", status);
}
void ldr(Register rt, Label label) {
  const auto status = try_ldr(rt, label);
  assert_instruction_encoded("ldr", status);
}
void ldrsw(Register rt, Label label) {
  const auto status = try_ldrsw(rt, label);
  assert_instruction_encoded("ldrsw", status);
}
void ldp(Register rt1, Register rt2, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldp(rt1, rt2, rn, imm, writeback);
  assert_instruction_encoded("ldp", status);
}
void ldpsw(Register rt1, Register rt2, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldpsw(rt1, rt2, rn, imm, writeback);
  assert_instruction_encoded("ldpsw", status);
}
void ldar(Register rt, Register rn) {
  const auto status = try_ldar(rt, rn);
  assert_instruction_encoded("ldar", status);
}
void ldarb(Register rt, Register rn) {
  const auto status = try_ldarb(rt, rn);
  assert_instruction_encoded("ldarb", status);
}
void ldarh(Register rt, Register rn) {
  const auto status = try_ldarh(rt, rn);
  assert_instruction_encoded("ldarh", status);
}
void stlr(Register rt, Register rn) {
  const auto status = try_stlr(rt, rn);
  assert_instruction_encoded("stlr", status);
}
void stlrb(Register rt, Register rn) {
  const auto status = try_stlrb(rt, rn);
  assert_instruction_encoded("stlrb", status);
}
void stlrh(Register rt, Register rn) {
  const auto status = try_stlrh(rt, rn);
  assert_instruction_encoded("stlrh", status);
}
void stp(Register rt1, Register rt2, Register rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_stp(rt1, rt2, rn, imm, writeback);
  assert_instruction_encoded("stp", status);
}
void b(Condition condition, Label label) {
  const auto status = try_b(condition, label);
  assert_instruction_encoded("b", status);
}
void cbz(Register rt, Label label) {
  const auto status = try_cbz(rt, label);
  assert_instruction_encoded("cbz", status);
}
void cbnz(Register rt, Label label) {
  const auto status = try_cbnz(rt, label);
  assert_instruction_encoded("cbnz", status);
}
void tbz(Register rt, uint64_t bit, Label label) {
  const auto status = try_tbz(rt, bit, label);
  assert_instruction_encoded("tbz", status);
}
void tbnz(Register rt, uint64_t bit, Label label) {
  const auto status = try_tbnz(rt, bit, label);
  assert_instruction_encoded("tbnz", status);
}
void b(Label label) {
  const auto status = try_b(label);
  assert_instruction_encoded("b", status);
}
void bl(Label label) {
  const auto status = try_bl(label);
  assert_instruction_encoded("bl", status);
}
void blr(Register rn) {
  const auto status = try_blr(rn);
  assert_instruction_encoded("blr", status);
}
void br(Register rn) {
  const auto status = try_br(rn);
  assert_instruction_encoded("br", status);
}
void ret(Register rn = Register::X30) {
  const auto status = try_ret(rn);
  assert_instruction_encoded("ret", status);
}
void svc(uint16_t imm) {
  const auto status = try_svc(imm);
  assert_instruction_encoded("svc", status);
}
void brk(uint16_t imm) {
  const auto status = try_brk(imm);
  assert_instruction_encoded("brk", status);
}
void macro_mov(Register rd, int64_t imm) {
  const auto status = try_macro_mov(rd, imm);
  assert_instruction_encoded("macro_mov", status);
}
