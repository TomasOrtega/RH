import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfMemBadPrimes

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.FlatVal

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Establish `hV : Formalism.L2.Pj.FinVol (D.sp.W j)`. Establish `h` using `hT.finVol j hj _ T.good_σ₀`. Rewrite `h` using `[hT.spaceW j hj _ T.good_σ₀]`. Then use the resulting hypothesis. Establish `hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd` using `by rw [hG.lev.1.2.1, hT.pins.2.1.1]`. Use `⟨hG.lev.2, fun σ hσ => ⟨hG.unf σ hσ, ?_, hV, hG.xiAbs σ hσ⟩⟩` and prove the remaining obligations.

Take `⟨th, hr, h1, h2⟩` from `hG.dictU σ hσ`. Conclude with `⟨Y.Kf, th, hr, hM ▸ hG.levelK, h1, h2⟩`.
-/
theorem isComplexData {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) {Y : Deep T.toCore j} {e : ℕ} {o : ℝ}
    (hG : Y.Good e o) : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict := by
  have hV : Formalism.L2.Pj.FinVol (D.sp.W j) := by
    have h := hT.finVol j hj _ T.good_σ₀
    rwa [hT.spaceW j hj _ T.good_σ₀] at h
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hG.lev.1.2.1, hT.pins.2.1.1]
  refine ⟨hG.lev.2, fun σ hσ => ⟨hG.unf σ hσ, ?_, hV, hG.xiAbs σ hσ⟩⟩
  obtain ⟨th, hr, h1, h2⟩ := hG.dictU σ hσ
  exact ⟨Y.Kf, th, hr, hM ▸ hG.levelK, h1, h2⟩

/- English proof (translation)
The claim follows from `|Real.log (D.host.d : ℝ) - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E| ≤ 3 * L.sc.L := by have hL := h.big.2.1 have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast h.f8 have h0 : 0 ≤ Real.log |(discr D.host.E : ℝ)| := by rw [Real.log_abs]; exact Real …`.
-/
theorem abs_log_sub_lrd_le {PP A M : ℝ} (h : HostNum D L PP A M) :
    |Real.log (D.host.d : ℝ) - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E| ≤ 3 * L.sc.L := by
  have hL := h.big.2.1
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast h.f8
  have h0 : 0 ≤ Real.log |(discr D.host.E : ℝ)| := by rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
    rw [rootDiscr_def, Int.cast_abs, Real.log_rpow (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero _))), h.deg]; push_cast; ring
  have h2 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E := by rw [h1]; positivity
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
    rw [h1, div_le_iff₀ (by linarith)]; linarith [h.disc]
  have h4 := Real.log_natCast_nonneg D.host.d
  exact abs_le.2 ⟨by linarith, by linarith [h.logd]⟩

/- English proof (translation)
Establish `hL` using `h.big.2.1`. Establish `hc0 : (LevelStarExponents.condE D : ℝ) ≠ 0`. Use `(GlobalTheory.BadLog.log_level_le P).1` as an intermediate fact. Conclude with `left_ne_zero_of_mul (left_ne_zero_of_mul this)` after adjusting the coercions. Establish `a0 : (D.host.g 0 : ℝ) ≠ 0` using `by exact_mod_cast (D.host.g_prime 0).ne_zero`.

Establish `a1 : (D.host.g 1 : ℝ) ≠ 0` using `by exact_mod_cast (D.host.g_prime 1).ne_zero`. Establish `hc` using `(Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.log_cond_le P).1`. Establish `l15 : Real.log 15 ≤ 14` using `by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]`. Use `push_cast`. Rewrite using `[Real.log_mul (mul_ne_zero hc0 (mul_ne_zero a0 a1)) (by norm_num), Real.log_mul hc0 (mul_ne_zero a0 a1), Real.log_mul a0 a1]`.

Combine the linear relations using `[h.logg 0, h.logg 1]`.
-/
theorem log_level_le (P : ParameterChoice' D L) {PP A M : ℝ} (h : HostNum D L PP A M) :
    Real.log ((LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 : ℕ) : ℝ) ≤ 40 * L.sc.L := by
  have hL := h.big.2.1
  have hc0 : (LevelStarExponents.condE D : ℝ) ≠ 0 := by
    have := (GlobalTheory.BadLog.log_level_le P).1
    exact_mod_cast left_ne_zero_of_mul (left_ne_zero_of_mul this)
  have a0 : (D.host.g 0 : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have a1 : (D.host.g 1 : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  have hc := (Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.log_cond_le P).1
  have l15 : Real.log 15 ≤ 14 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]
  push_cast
  rw [Real.log_mul (mul_ne_zero hc0 (mul_ne_zero a0 a1)) (by norm_num), Real.log_mul hc0 (mul_ne_zero a0 a1),
    Real.log_mul a0 a1]
  linarith [h.logg 0, h.logg 1]

/- English proof (translation)
Introduce `hF`. Use `Closed.imp (Closed.and hF (GlobalTheory.CovTop.Sizes.hostN 0)) ?_` and prove the remaining obligations. Introduce and unpack `eps Fm CH _ ⟨⟨C, -, h1⟩, A, -, h2⟩`. Take `⟨x0, h⟩` from `h1.and h2`. Use `⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩` and prove the remaining obligations.

Take `⟨a, b⟩` from `h x hx hle ι p hp`. Establish `hN` using `b i`. Establish `hD : GlobalTheory.FlatLine.FlatDegree Y.U _ _` using `a i hi Y hY`. Establish `hT` using `p.fw.laws`. Establish `hj : InR (Fm.D x ι) ((i : ℕ) + 1)` using `⟨by omega, hi.le⟩`.

Establish `hpos` using `Inhab.rank_pos _ hT.pins _ hj`. Use `⟨isComplexData hT hj hY.1, (GlobalTheory.LawsDeep.laws_deep _ _ _ Y _ _ hT hj hY.1).good, hD.flatExists, fun τ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hD.c1_eq (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Y.d.Xo₂ Y.d.c₂ hpos).1, hT.pins.1.1]`. Establish `e : ∀ u v : ℝ, -u - v + u = -v` using `fun u v => by ring`. Rewrite using `[e, abs_neg, abs_mul, Nat.abs_cast, mul_comm 3, mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left (abs_log_sub_lrd_le hN) (Nat.cast_nonneg _)`. Conclude with `(GlobalTheory.BadLog.logSum_le_log (GlobalTheory.BadLog.log_level_le (Fm.params x hx ι)).1 fun q hq => GlobalTheory.BadLog.dvd_of_mem_badPrimes hT.pins hY.1 hq).trans (log_level_le (Fm.params x hx ι) hN)`.
-/
theorem flat_val : FlatDeg → Covers fun Fm x _ ι p i Y _ _ => GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧ GlobalTheory.FlatLine.FlatExists Y.U (xiR (Fm.D x ι)) ∧ (∀ τ, |GlobalTheory.FlatLine.c1 Y.U (xiR (Fm.D x ι)) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 3 * (dat p i).q * (Fm.L x ι).sc.L) ∧ GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * (Fm.L x ι).sc.L := by
  intro hF
  refine Closed.imp (Closed.and hF (GlobalTheory.CovTop.Sizes.hostN 0)) ?_
  rintro eps Fm CH _ ⟨⟨C, -, h1⟩, A, -, h2⟩
  obtain ⟨x0, h⟩ := h1.and h2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨a, b⟩ := h x hx hle ι p hp
  have hN := b i
  have hD : GlobalTheory.FlatLine.FlatDegree Y.U _ _ := a i hi Y hY
  have hT := p.fw.laws
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hpos := Inhab.rank_pos _ hT.pins _ hj
  refine ⟨isComplexData hT hj hY.1, (GlobalTheory.LawsDeep.laws_deep _ _ _ Y _ _ hT hj hY.1).good, hD.flatExists, fun τ => ?_, ?_⟩
  · rw [hD.c1_eq (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Y.d.Xo₂ Y.d.c₂ hpos).1, hT.pins.1.1]
    have e : ∀ u v : ℝ, -u - v + u = -v := fun u v => by ring
    rw [e, abs_neg, abs_mul, Nat.abs_cast, mul_comm 3, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_log_sub_lrd_le hN) (Nat.cast_nonneg _)
  · exact (GlobalTheory.BadLog.logSum_le_log (GlobalTheory.BadLog.log_level_le (Fm.params x hx ι)).1
      fun q hq => GlobalTheory.BadLog.dvd_of_mem_badPrimes hT.pins hY.1 hq).trans (log_level_le (Fm.params x hx ι) hN)

end GlobalTheory.CovTop.FlatVal

end
