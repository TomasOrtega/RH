import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RhoZeroNormBounds

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Establish `hl0 : (0 : ℝ≥0) < l` using `Nat.cast_pos.2 hl.out.pos`. Unfold `BK.ρ₀`. Conclude with `NNReal.rpow_pos hl0`.
-/
theorem ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  unfold BK.ρ₀
  exact NNReal.rpow_pos hl0

/- English proof (translation)
Establish `hl0 : (0 : ℝ≥0) < l` using `Nat.cast_pos.2 hl.out.pos`. Establish `he : (bk.Ep.natDegree : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 bk.deg_pos.ne'`. Unfold `BK.ρ₀`. Rewrite using `[← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]`.
-/
theorem ρ₀_pow (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).2.1 y, div_eq_inv_mul]`.
-/
theorem norm_l_mul (bk : BK K) (y : bk.DA bk.ρ₀) : ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖ := by
  rw [(GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).2.1 y, div_eq_inv_mul]

/- English proof (translation)
The claim follows from `norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (bk.ev x)`.
-/
theorem norm_iS_le (bk : BK K) (x : bk.S) : ‖bk.iS x‖ ≤ 1 :=
  norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (bk.ev x)

/- English proof (translation)
Use `haveI := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).1`. Establish `hE : bk.E = bk.Ep.eval₂ PowerSeries.C PowerSeries.X` using `(Polynomial.eval₂_C_X_eq_coe).symm`. Rewrite using `[hE, Polynomial.hom_eval₂, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]`. Establish `hinv : (0 : ℝ) ≤ (l : ℝ)⁻¹` using `by positivity`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hinv fun i hi => ?_` and prove the remaining obligations. Take `⟨d, hd⟩` from `bk.dvd_coeff i (Finset.mem_range.1 hi)`. Establish `e : (bk.iS.comp PowerSeries.C) (bk.Ep.coeff i) * bk.iS PowerSeries.X ^ i = (l : bk.DA bk.ρ₀) * bk.iS (PowerSeries.C d * PowerSeries.X ^ i)`. Rewrite using `[hd, RingHom.comp_apply, map_mul, map_mul, map_mul, map_pow, map_natCast, map_natCast, mul_assoc]`. Rewrite using `[e, norm_l_mul]`.

Conclude with `mul_le_of_le_one_right hinv (norm_iS_le bk _)`. Rewrite using `[bk.monic.coeff_natDegree, map_one, one_mul, ← map_pow]`. Express the relevant statement in the definitionally equal form `‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev (PowerSeries.X ^ bk.Ep.natDegree))‖ ≤ _`. Rewrite using `[map_pow]`. Use `(norm_toDisc_pow_le _ (ρ₀_pos bk)).trans ?_` and prove the remaining obligations.

Rewrite using `[← NNReal.coe_pow, ρ₀_pow, NNReal.coe_inv, NNReal.coe_natCast]`.
-/
theorem norm_iS_E (bk : BK K) : ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ := by
  haveI := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).1
  have hE : bk.E = bk.Ep.eval₂ PowerSeries.C PowerSeries.X := (Polynomial.eval₂_C_X_eq_coe).symm
  rw [hE, Polynomial.hom_eval₂, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
  have hinv : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hinv fun i hi => ?_
    obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    have e : (bk.iS.comp PowerSeries.C) (bk.Ep.coeff i) * bk.iS PowerSeries.X ^ i =
        (l : bk.DA bk.ρ₀) * bk.iS (PowerSeries.C d * PowerSeries.X ^ i) := by
      rw [hd, RingHom.comp_apply, map_mul, map_mul, map_mul, map_pow, map_natCast, map_natCast, mul_assoc]
    rw [e, norm_l_mul]
    exact mul_le_of_le_one_right hinv (norm_iS_le bk _)
  · rw [bk.monic.coeff_natDegree, map_one, one_mul, ← map_pow]
    change ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev (PowerSeries.X ^ bk.Ep.natDegree))‖ ≤ _
    rw [map_pow]
    refine (norm_toDisc_pow_le _ (ρ₀_pos bk)).trans ?_
    rw [← NNReal.coe_pow, ρ₀_pow, NNReal.coe_inv, NNReal.coe_natCast]

/- English proof (translation)
Establish `hmem : a ∈ Ideal.span {bk.ev bk.E}` using `by rw [bk.span_ev]; exact ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hmem`. Rewrite using `[map_mul]`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ‖bk.iA c‖ ≤ 1` using `norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) c`.

Establish `h2 : ‖bk.iA (bk.ev bk.E)‖ ≤ (l : ℝ)⁻¹` using `norm_iS_E bk`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_iA_ker (bk : BK K) (a : Ainf l) (ha : Per.θ l a = 0) : ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ := by
  have hmem : a ∈ Ideal.span {bk.ev bk.E} := by rw [bk.span_ev]; exact ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [map_mul]
  refine (norm_mul_le _ _).trans ?_
  have h1 : ‖bk.iA c‖ ≤ 1 := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) c
  have h2 : ‖bk.iA (bk.ev bk.E)‖ ≤ (l : ℝ)⁻¹ := norm_iS_E bk
  calc ‖bk.iA c‖ * ‖bk.iA (bk.ev bk.E)‖ ≤ 1 * (l : ℝ)⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/- English proof (translation)
Introduce `_ _ _ bk` and use `⟨norm_iS_E bk, norm_l_mul bk, norm_iA_ker bk⟩`.
-/
theorem seed_norms : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ ∧ (∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖) ∧ ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ :=
  fun _ _ _ bk => ⟨norm_iS_E bk, norm_l_mul bk, norm_iA_ker bk⟩

end GlobalTheory.BSP.RhoZeroNormBounds
