import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOnePropertiesStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`. Rewrite using `[Polynomial.coeff_sub, Polynomial.coeff_X_pow]`. Break down `lt_trichotomy i bk.Ep.natDegree with hi | hi | hi` into its components or cases.

Rewrite using `[if_neg hi.ne, sub_zero]`. Conclude with `bk.dvd_coeff i hi`. Rewrite using `[if_pos hi, hi, bk.monic.coeff_natDegree, sub_self]`. Conclude with `dvd_zero _`. Rewrite using `[if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, sub_zero]`.

Conclude with `dvd_zero _`. Take `⟨q, hq⟩` from `h`. Conclude with `⟨q, by rw [← hq]; ring⟩`.
-/
theorem BK.exists_Ep_eq_X_pow_add {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : Polynomial (Wq l bk.a),
      bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
  have h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, sub_zero]; exact bk.dvd_coeff i hi
    · rw [if_pos hi, hi, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, sub_zero]; exact dvd_zero _
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [← hq]; ring⟩

/- English proof (translation)
Introduce `l _ K bk ρ h0 h1 y`. Take `⟨_, _, ⟨hρ0, _, hρe⟩, _⟩` from `GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk`. Establish `hρ : 0 < ρ` using `hρ0.trans_le h0`. Rewrite using `[GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk ρ hρ h1]`. Use `congr 1`.

Establish `hl0 : (0 : ℝ) < l` using `Nat.cast_pos.2 (Fact.out : l.Prime).pos`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨q, hq⟩` from `bk.exists_Ep_eq_X_pow_add`. Establish `hE : bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (q : bk.S)`. Simplify using `only [BK.E]`.

Use `conv_lhs => rw [hq]`. Rewrite using `[Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C, map_natCast]`. Establish `hl' : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ ≤ (l : ℝ)⁻¹` using `gauge_le l (X : bk.S) ρ (by positivity) (Submodule.subset_span ⟨1, 0, 0, by rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], by simp⟩)`. Establish `hX : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) ((X : bk.S) ^ bk.Ep.natDegree)‖ ≤ (ρ : ℝ) ^ bk.Ep.natDegree` using `(norm_ofPre l (X : bk.S) ρ _).symm.trans_le (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) _ hρ)`. Establish `hup : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) bk.E‖ ≤ (ρ : ℝ) ^ bk.Ep.natDegree`.

Rewrite using `[hE, map_add, map_mul, norm_preDisc]`. Use `(gauge_add_le_max l (X : bk.S) ρ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[← norm_preDisc]`. Conclude with `hX`. Rewrite using `[← norm_preDisc]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[NNReal.coe_pow]; exact pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast h0) _`. Conclude with `(norm_ofPre l (X : bk.S) ρ _).trans_le hup`. Take `⟨a, ha1, ha2, -, -⟩` from `GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ h1`. Take `⟨-, -, -, hk⟩` from `GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk`.

Establish `hc : coeff bk.Ep.natDegree bk.E = 1`. Rewrite using `[BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree]`. Establish `h` using `ha2 bk.Ep.natDegree (toDisc l (X : bk.S) ρ bk.E)`. Rewrite `h` using `[ha1, hc, hk 1 isUnit_one, one_mul]`. Conclude with `h`.
-/
theorem BK.norm_toDisc_E_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 →
    ∀ y : bk.DS ρ, ‖toDisc l (X : bk.S) ρ bk.E * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  intro l _ K bk ρ h0 h1 y
  obtain ⟨_, _, ⟨hρ0, _, hρe⟩, _⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hρ : 0 < ρ := hρ0.trans_le h0
  rw [GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk ρ hρ h1]
  congr 1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  apply le_antisymm
  · obtain ⟨q, hq⟩ := bk.exists_Ep_eq_X_pow_add
    have hE : bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (q : bk.S) := by
      simp only [BK.E]
      conv_lhs => rw [hq]
      rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C,
        map_natCast]
    have hl' : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ ≤ (l : ℝ)⁻¹ :=
      gauge_le l (X : bk.S) ρ (by positivity) (Submodule.subset_span ⟨1, 0, 0,
        by rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], by simp⟩)
    have hX : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) ((X : bk.S) ^ bk.Ep.natDegree)‖ ≤
        (ρ : ℝ) ^ bk.Ep.natDegree :=
      (norm_ofPre l (X : bk.S) ρ _).symm.trans_le (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) _ hρ)
    have hup : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) bk.E‖ ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by
      rw [hE, map_add, map_mul, norm_preDisc]
      refine (gauge_add_le_max l (X : bk.S) ρ _ _).trans (max_le ?_ ?_)
      · rw [← norm_preDisc]; exact hX
      · rw [← norm_preDisc]
        calc _ ≤ ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ *
              ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (q : bk.S)‖ := norm_mul_le _ _
          _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hl' (norm_algebraMap_le _) (norm_nonneg _) (by positivity)
          _ = ((bk.ρ₀ ^ bk.Ep.natDegree : ℝ≥0) : ℝ) := by rw [hρe]; simp
          _ ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by
            rw [NNReal.coe_pow]; exact pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast h0) _
    exact (norm_ofPre l (X : bk.S) ρ _).trans_le hup
  · obtain ⟨a, ha1, ha2, -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ h1
    obtain ⟨-, -, -, hk⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk
    have hc : coeff bk.Ep.natDegree bk.E = 1 := by
      rw [BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree]
    have h := ha2 bk.Ep.natDegree (toDisc l (X : bk.S) ρ bk.E)
    rw [ha1, hc, hk 1 isUnit_one, one_mul] at h
    exact h

end GlobalTheory.BSP
