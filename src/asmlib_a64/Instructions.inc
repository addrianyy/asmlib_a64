[[nodiscard]] Status try_add(Reg rd, Reg rn, uint64_t imm);
[[nodiscard]] Status try_adds(Reg rd, Reg rn, uint64_t imm);
[[nodiscard]] Status try_sub(Reg rd, Reg rn, uint64_t imm);
[[nodiscard]] Status try_subs(Reg rd, Reg rn, uint64_t imm);
[[nodiscard]] Status try_cmp(Reg rn, uint64_t imm);
[[nodiscard]] Status try_cmn(Reg rn, uint64_t imm);
[[nodiscard]] Status try_and_(Reg rd, Reg rn, uint64_t imm);
[[nodiscard]] Status try_ands(Reg rd, Reg rn, uint64_t imm);
[[nodiscard]] Status try_eor(Reg rd, Reg rn, uint64_t imm);
[[nodiscard]] Status try_orr(Reg rd, Reg rn, uint64_t imm);
[[nodiscard]] Status try_tst(Reg rn, uint64_t imm);
[[nodiscard]] Status try_movz(Reg rd, uint64_t imm, uint64_t shift = 0);
[[nodiscard]] Status try_movk(Reg rd, uint64_t imm, uint64_t shift = 0);
[[nodiscard]] Status try_movn(Reg rd, uint64_t imm, uint64_t shift = 0);
[[nodiscard]] Status try_mov(Reg rd, uint64_t imm);
[[nodiscard]] Status try_adr(Reg rd, Label label);
[[nodiscard]] Status try_adrp(Reg rd, Label label);
[[nodiscard]] Status try_bfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms);
[[nodiscard]] Status try_sbfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms);
[[nodiscard]] Status try_ubfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms);
[[nodiscard]] Status try_bfc(Reg rd, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_bfi(Reg rd, Reg rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_bfxil(Reg rd, Reg rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_sbfiz(Reg rd, Reg rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_sbfx(Reg rd, Reg rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_ubfiz(Reg rd, Reg rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_ubfx(Reg rd, Reg rn, uint64_t lsb, uint64_t width);
[[nodiscard]] Status try_extr(Reg rd, Reg rn, Reg rm, uint64_t lsb);
[[nodiscard]] Status try_asr(Reg rd, Reg rn, uint64_t shift);
[[nodiscard]] Status try_lsl(Reg rd, Reg rn, uint64_t shift);
[[nodiscard]] Status try_lsr(Reg rd, Reg rn, uint64_t shift);
[[nodiscard]] Status try_ror(Reg rd, Reg rn, uint64_t shift);
[[nodiscard]] Status try_sxtb(Reg rd, Reg rn);
[[nodiscard]] Status try_sxth(Reg rd, Reg rn);
[[nodiscard]] Status try_sxtw(Reg rd, Reg rn);
[[nodiscard]] Status try_uxtb(Reg rd, Reg rn);
[[nodiscard]] Status try_uxth(Reg rd, Reg rn);
[[nodiscard]] Status try_add(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_adds(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_sub(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_subs(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_cmp(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_cmn(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_neg(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_negs(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_and_(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_ands(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_bic(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_bics(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_eor(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_eon(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_orr(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_orn(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_mvn(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_tst(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl);
[[nodiscard]] Status try_mov(Reg rd, Reg rn);
[[nodiscard]] Status try_asr(Reg rd, Reg rn, Reg rm);
[[nodiscard]] Status try_lsl(Reg rd, Reg rn, Reg rm);
[[nodiscard]] Status try_lsr(Reg rd, Reg rn, Reg rm);
[[nodiscard]] Status try_ror(Reg rd, Reg rn, Reg rm);
[[nodiscard]] Status try_madd(Reg rd, Reg rn, Reg rm, Reg ra);
[[nodiscard]] Status try_msub(Reg rd, Reg rn, Reg rm, Reg ra);
[[nodiscard]] Status try_mneg(Reg rd, Reg rn, Reg rm);
[[nodiscard]] Status try_mul(Reg rd, Reg rn, Reg rm);
[[nodiscard]] Status try_sdiv(Reg rd, Reg rn, Reg rm);
[[nodiscard]] Status try_udiv(Reg rd, Reg rn, Reg rm);
[[nodiscard]] Status try_cls(Reg rd, Reg rn);
[[nodiscard]] Status try_clz(Reg rd, Reg rn);
[[nodiscard]] Status try_csel(Reg rd, Reg rn, Reg rm, Condition condition);
[[nodiscard]] Status try_csinc(Reg rd, Reg rn, Reg rm, Condition condition);
[[nodiscard]] Status try_cset(Reg rd, Condition condition);
[[nodiscard]] Status try_ldr(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrsw(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrsh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldrsb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_str(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_strh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_strb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldr(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrsw(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrsh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldrsb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_str(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_strh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_strb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl);
[[nodiscard]] Status try_ldr(Reg rt, Label label);
[[nodiscard]] Status try_ldrsw(Reg rt, Label label);
[[nodiscard]] Status try_ldp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldpsw(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_ldar(Reg rt, Reg rn);
[[nodiscard]] Status try_ldarb(Reg rt, Reg rn);
[[nodiscard]] Status try_ldarh(Reg rt, Reg rn);
[[nodiscard]] Status try_stlr(Reg rt, Reg rn);
[[nodiscard]] Status try_stlrb(Reg rt, Reg rn);
[[nodiscard]] Status try_stlrh(Reg rt, Reg rn);
[[nodiscard]] Status try_stp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None);
[[nodiscard]] Status try_b(Condition condition, Label label);
[[nodiscard]] Status try_cbz(Reg rt, Label label);
[[nodiscard]] Status try_cbnz(Reg rt, Label label);
[[nodiscard]] Status try_tbz(Reg rt, uint64_t bit, Label label);
[[nodiscard]] Status try_tbnz(Reg rt, uint64_t bit, Label label);
[[nodiscard]] Status try_b(Label label);
[[nodiscard]] Status try_bl(Label label);
[[nodiscard]] Status try_blr(Reg rn);
[[nodiscard]] Status try_br(Reg rn);
[[nodiscard]] Status try_ret(Reg rn);
[[nodiscard]] Status try_svc(uint16_t imm);
[[nodiscard]] Status try_brk(uint16_t imm);


void add(Reg rd, Reg rn, uint64_t imm) {
  const auto status = try_add(rd, rn, imm);
  assert_instruction_encoded("add", status);
}
void adds(Reg rd, Reg rn, uint64_t imm) {
  const auto status = try_adds(rd, rn, imm);
  assert_instruction_encoded("adds", status);
}
void sub(Reg rd, Reg rn, uint64_t imm) {
  const auto status = try_sub(rd, rn, imm);
  assert_instruction_encoded("sub", status);
}
void subs(Reg rd, Reg rn, uint64_t imm) {
  const auto status = try_subs(rd, rn, imm);
  assert_instruction_encoded("subs", status);
}
void cmp(Reg rn, uint64_t imm) {
  const auto status = try_cmp(rn, imm);
  assert_instruction_encoded("cmp", status);
}
void cmn(Reg rn, uint64_t imm) {
  const auto status = try_cmn(rn, imm);
  assert_instruction_encoded("cmn", status);
}
void and_(Reg rd, Reg rn, uint64_t imm) {
  const auto status = try_and_(rd, rn, imm);
  assert_instruction_encoded("and_", status);
}
void ands(Reg rd, Reg rn, uint64_t imm) {
  const auto status = try_ands(rd, rn, imm);
  assert_instruction_encoded("ands", status);
}
void eor(Reg rd, Reg rn, uint64_t imm) {
  const auto status = try_eor(rd, rn, imm);
  assert_instruction_encoded("eor", status);
}
void orr(Reg rd, Reg rn, uint64_t imm) {
  const auto status = try_orr(rd, rn, imm);
  assert_instruction_encoded("orr", status);
}
void tst(Reg rn, uint64_t imm) {
  const auto status = try_tst(rn, imm);
  assert_instruction_encoded("tst", status);
}
void movz(Reg rd, uint64_t imm, uint64_t shift = 0) {
  const auto status = try_movz(rd, imm, shift);
  assert_instruction_encoded("movz", status);
}
void movk(Reg rd, uint64_t imm, uint64_t shift = 0) {
  const auto status = try_movk(rd, imm, shift);
  assert_instruction_encoded("movk", status);
}
void movn(Reg rd, uint64_t imm, uint64_t shift = 0) {
  const auto status = try_movn(rd, imm, shift);
  assert_instruction_encoded("movn", status);
}
void mov(Reg rd, uint64_t imm) {
  const auto status = try_mov(rd, imm);
  assert_instruction_encoded("mov", status);
}
void adr(Reg rd, Label label) {
  const auto status = try_adr(rd, label);
  assert_instruction_encoded("adr", status);
}
void adrp(Reg rd, Label label) {
  const auto status = try_adrp(rd, label);
  assert_instruction_encoded("adrp", status);
}
void bfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms) {
  const auto status = try_bfm(rd, rn, immr, imms);
  assert_instruction_encoded("bfm", status);
}
void sbfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms) {
  const auto status = try_sbfm(rd, rn, immr, imms);
  assert_instruction_encoded("sbfm", status);
}
void ubfm(Reg rd, Reg rn, uint64_t immr, uint64_t imms) {
  const auto status = try_ubfm(rd, rn, immr, imms);
  assert_instruction_encoded("ubfm", status);
}
void bfc(Reg rd, uint64_t lsb, uint64_t width) {
  const auto status = try_bfc(rd, lsb, width);
  assert_instruction_encoded("bfc", status);
}
void bfi(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto status = try_bfi(rd, rn, lsb, width);
  assert_instruction_encoded("bfi", status);
}
void bfxil(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto status = try_bfxil(rd, rn, lsb, width);
  assert_instruction_encoded("bfxil", status);
}
void sbfiz(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto status = try_sbfiz(rd, rn, lsb, width);
  assert_instruction_encoded("sbfiz", status);
}
void sbfx(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto status = try_sbfx(rd, rn, lsb, width);
  assert_instruction_encoded("sbfx", status);
}
void ubfiz(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto status = try_ubfiz(rd, rn, lsb, width);
  assert_instruction_encoded("ubfiz", status);
}
void ubfx(Reg rd, Reg rn, uint64_t lsb, uint64_t width) {
  const auto status = try_ubfx(rd, rn, lsb, width);
  assert_instruction_encoded("ubfx", status);
}
void extr(Reg rd, Reg rn, Reg rm, uint64_t lsb) {
  const auto status = try_extr(rd, rn, rm, lsb);
  assert_instruction_encoded("extr", status);
}
void asr(Reg rd, Reg rn, uint64_t shift) {
  const auto status = try_asr(rd, rn, shift);
  assert_instruction_encoded("asr", status);
}
void lsl(Reg rd, Reg rn, uint64_t shift) {
  const auto status = try_lsl(rd, rn, shift);
  assert_instruction_encoded("lsl", status);
}
void lsr(Reg rd, Reg rn, uint64_t shift) {
  const auto status = try_lsr(rd, rn, shift);
  assert_instruction_encoded("lsr", status);
}
void ror(Reg rd, Reg rn, uint64_t shift) {
  const auto status = try_ror(rd, rn, shift);
  assert_instruction_encoded("ror", status);
}
void sxtb(Reg rd, Reg rn) {
  const auto status = try_sxtb(rd, rn);
  assert_instruction_encoded("sxtb", status);
}
void sxth(Reg rd, Reg rn) {
  const auto status = try_sxth(rd, rn);
  assert_instruction_encoded("sxth", status);
}
void sxtw(Reg rd, Reg rn) {
  const auto status = try_sxtw(rd, rn);
  assert_instruction_encoded("sxtw", status);
}
void uxtb(Reg rd, Reg rn) {
  const auto status = try_uxtb(rd, rn);
  assert_instruction_encoded("uxtb", status);
}
void uxth(Reg rd, Reg rn) {
  const auto status = try_uxth(rd, rn);
  assert_instruction_encoded("uxth", status);
}
void add(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_add(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("add", status);
}
void adds(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_adds(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("adds", status);
}
void sub(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_sub(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("sub", status);
}
void subs(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_subs(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("subs", status);
}
void cmp(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_cmp(rn, rm, shift_amount, shift);
  assert_instruction_encoded("cmp", status);
}
void cmn(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_cmn(rn, rm, shift_amount, shift);
  assert_instruction_encoded("cmn", status);
}
void neg(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_neg(rd, rm, shift_amount, shift);
  assert_instruction_encoded("neg", status);
}
void negs(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_negs(rd, rm, shift_amount, shift);
  assert_instruction_encoded("negs", status);
}
void and_(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_and_(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("and_", status);
}
void ands(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_ands(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("ands", status);
}
void bic(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_bic(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("bic", status);
}
void bics(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_bics(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("bics", status);
}
void eor(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_eor(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("eor", status);
}
void eon(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_eon(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("eon", status);
}
void orr(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_orr(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("orr", status);
}
void orn(Reg rd, Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_orn(rd, rn, rm, shift_amount, shift);
  assert_instruction_encoded("orn", status);
}
void mvn(Reg rd, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_mvn(rd, rm, shift_amount, shift);
  assert_instruction_encoded("mvn", status);
}
void tst(Reg rn, Reg rm, uint64_t shift_amount = 0, Shift shift = Shift::Lsl) {
  const auto status = try_tst(rn, rm, shift_amount, shift);
  assert_instruction_encoded("tst", status);
}
void mov(Reg rd, Reg rn) {
  const auto status = try_mov(rd, rn);
  assert_instruction_encoded("mov", status);
}
void asr(Reg rd, Reg rn, Reg rm) {
  const auto status = try_asr(rd, rn, rm);
  assert_instruction_encoded("asr", status);
}
void lsl(Reg rd, Reg rn, Reg rm) {
  const auto status = try_lsl(rd, rn, rm);
  assert_instruction_encoded("lsl", status);
}
void lsr(Reg rd, Reg rn, Reg rm) {
  const auto status = try_lsr(rd, rn, rm);
  assert_instruction_encoded("lsr", status);
}
void ror(Reg rd, Reg rn, Reg rm) {
  const auto status = try_ror(rd, rn, rm);
  assert_instruction_encoded("ror", status);
}
void madd(Reg rd, Reg rn, Reg rm, Reg ra) {
  const auto status = try_madd(rd, rn, rm, ra);
  assert_instruction_encoded("madd", status);
}
void msub(Reg rd, Reg rn, Reg rm, Reg ra) {
  const auto status = try_msub(rd, rn, rm, ra);
  assert_instruction_encoded("msub", status);
}
void mneg(Reg rd, Reg rn, Reg rm) {
  const auto status = try_mneg(rd, rn, rm);
  assert_instruction_encoded("mneg", status);
}
void mul(Reg rd, Reg rn, Reg rm) {
  const auto status = try_mul(rd, rn, rm);
  assert_instruction_encoded("mul", status);
}
void sdiv(Reg rd, Reg rn, Reg rm) {
  const auto status = try_sdiv(rd, rn, rm);
  assert_instruction_encoded("sdiv", status);
}
void udiv(Reg rd, Reg rn, Reg rm) {
  const auto status = try_udiv(rd, rn, rm);
  assert_instruction_encoded("udiv", status);
}
void cls(Reg rd, Reg rn) {
  const auto status = try_cls(rd, rn);
  assert_instruction_encoded("cls", status);
}
void clz(Reg rd, Reg rn) {
  const auto status = try_clz(rd, rn);
  assert_instruction_encoded("clz", status);
}
void csel(Reg rd, Reg rn, Reg rm, Condition condition) {
  const auto status = try_csel(rd, rn, rm, condition);
  assert_instruction_encoded("csel", status);
}
void csinc(Reg rd, Reg rn, Reg rm, Condition condition) {
  const auto status = try_csinc(rd, rn, rm, condition);
  assert_instruction_encoded("csinc", status);
}
void cset(Reg rd, Condition condition) {
  const auto status = try_cset(rd, condition);
  assert_instruction_encoded("cset", status);
}
void ldr(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldr(rt, rn, imm, writeback);
  assert_instruction_encoded("ldr", status);
}
void ldrh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrh(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrh", status);
}
void ldrb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrb(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrb", status);
}
void ldrsw(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrsw(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrsw", status);
}
void ldrsh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrsh(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrsh", status);
}
void ldrsb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldrsb(rt, rn, imm, writeback);
  assert_instruction_encoded("ldrsb", status);
}
void str(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_str(rt, rn, imm, writeback);
  assert_instruction_encoded("str", status);
}
void strh(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_strh(rt, rn, imm, writeback);
  assert_instruction_encoded("strh", status);
}
void strb(Reg rt, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_strb(rt, rn, imm, writeback);
  assert_instruction_encoded("strb", status);
}
void ldr(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldr(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldr", status);
}
void ldrh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrh(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrh", status);
}
void ldrb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrb(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrb", status);
}
void ldrsw(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrsw(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrsw", status);
}
void ldrsh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrsh(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrsh", status);
}
void ldrsb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_ldrsb(rt, rn, rm, scale, extend);
  assert_instruction_encoded("ldrsb", status);
}
void str(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_str(rt, rn, rm, scale, extend);
  assert_instruction_encoded("str", status);
}
void strh(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_strh(rt, rn, rm, scale, extend);
  assert_instruction_encoded("strh", status);
}
void strb(Reg rt, Reg rn, Reg rm, Scale scale = Scale::None, Extend extend = Extend::Lsl) {
  const auto status = try_strb(rt, rn, rm, scale, extend);
  assert_instruction_encoded("strb", status);
}
void ldr(Reg rt, Label label) {
  const auto status = try_ldr(rt, label);
  assert_instruction_encoded("ldr", status);
}
void ldrsw(Reg rt, Label label) {
  const auto status = try_ldrsw(rt, label);
  assert_instruction_encoded("ldrsw", status);
}
void ldp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldp(rt1, rt2, rn, imm, writeback);
  assert_instruction_encoded("ldp", status);
}
void ldpsw(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_ldpsw(rt1, rt2, rn, imm, writeback);
  assert_instruction_encoded("ldpsw", status);
}
void ldar(Reg rt, Reg rn) {
  const auto status = try_ldar(rt, rn);
  assert_instruction_encoded("ldar", status);
}
void ldarb(Reg rt, Reg rn) {
  const auto status = try_ldarb(rt, rn);
  assert_instruction_encoded("ldarb", status);
}
void ldarh(Reg rt, Reg rn) {
  const auto status = try_ldarh(rt, rn);
  assert_instruction_encoded("ldarh", status);
}
void stlr(Reg rt, Reg rn) {
  const auto status = try_stlr(rt, rn);
  assert_instruction_encoded("stlr", status);
}
void stlrb(Reg rt, Reg rn) {
  const auto status = try_stlrb(rt, rn);
  assert_instruction_encoded("stlrb", status);
}
void stlrh(Reg rt, Reg rn) {
  const auto status = try_stlrh(rt, rn);
  assert_instruction_encoded("stlrh", status);
}
void stp(Reg rt1, Reg rt2, Reg rn, int64_t imm, Writeback writeback = Writeback::None) {
  const auto status = try_stp(rt1, rt2, rn, imm, writeback);
  assert_instruction_encoded("stp", status);
}
void b(Condition condition, Label label) {
  const auto status = try_b(condition, label);
  assert_instruction_encoded("b", status);
}
void cbz(Reg rt, Label label) {
  const auto status = try_cbz(rt, label);
  assert_instruction_encoded("cbz", status);
}
void cbnz(Reg rt, Label label) {
  const auto status = try_cbnz(rt, label);
  assert_instruction_encoded("cbnz", status);
}
void tbz(Reg rt, uint64_t bit, Label label) {
  const auto status = try_tbz(rt, bit, label);
  assert_instruction_encoded("tbz", status);
}
void tbnz(Reg rt, uint64_t bit, Label label) {
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
void blr(Reg rn) {
  const auto status = try_blr(rn);
  assert_instruction_encoded("blr", status);
}
void br(Reg rn) {
  const auto status = try_br(rn);
  assert_instruction_encoded("br", status);
}
void ret(Reg rn) {
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
