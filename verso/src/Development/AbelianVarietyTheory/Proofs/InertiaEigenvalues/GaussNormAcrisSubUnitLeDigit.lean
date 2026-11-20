import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootUnityEqUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerFurther
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadiusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNormStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

/- English proof (translation)
Establish `hN` using `isGauss_gC_of_le l ρ h0 h1`. Establish `hl : gC l ρ (l : Formalism.Per.Acris l) = ρ` using `(gC_basic_values l ρ h0 h1).2.1`. Establish `hm` using `hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0`. Rewrite `hm` using `[mul_zero, hl]`. Establish `: (1 - ρ) * gC l ρ 0 = 0` using `by linarith`.

Break down `mul_eq_zero.1 this with h' | h'` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h'`.
-/
theorem gC_zero_of_radius (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := (gC_basic_values l ρ h0 h1).2.1
  have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
  rw [mul_zero, hl] at hm
  have : (1 - ρ) * gC l ρ 0 = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · linarith
  · exact h'

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hρ : 0 < ρ` using `(inv_pos.2 hl0).trans_le h0`. Use `set r := -Real.logb l ρ with hr`. Establish `hρr : (l : ℝ) ^ (-r) = ρ`.

Rewrite using `[hr, neg_neg, Real.rpow_logb hl0 hl1.ne' hρ]`. Establish `hr0 : 0 < r`. Use `Real.logb_neg hl1 hρ h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr1 : r ≤ 1`.

Establish `h` using `(Real.logb_le_logb hl1 (inv_pos.2 hl0) hρ).2 h0`. Rewrite `h` using `[Real.logb_inv, Real.logb_self_eq_one hl1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv` using `hn r ⟨hr0, hr1⟩`. Simplify using `only [vr, hρr] at hv`.

Establish `hgx` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ h0 h1`. Establish `hgy` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y hy ρ h0 h1`. Apply `Real.logb_injOn_pos hl1 hgx (Set.mem_Ioi.2 (mul_pos (zpow_pos hρ n) hgy))` to reduce the goal to its premises. Establish `hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ`. Rewrite using `[Real.logb, Real.logb, Real.log_zpow, mul_div_assoc]`.

Rewrite using `[Real.logb_mul (zpow_pos hρ n).ne' hgy.ne', hz]`. Rewrite `hv` using `[hr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gC_eq_zpow_mul_of_vr (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l) (hx : x ≠ 0) (hy : y ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r x - vr l r y = n * r) (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ x = ρ ^ n * gC l ρ y := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  set r := -Real.logb l ρ with hr
  have hρr : (l : ℝ) ^ (-r) = ρ := by
    rw [hr, neg_neg, Real.rpow_logb hl0 hl1.ne' hρ]
  have hr0 : 0 < r := by
    have := Real.logb_neg hl1 hρ h1
    linarith
  have hr1 : r ≤ 1 := by
    have h := (Real.logb_le_logb hl1 (inv_pos.2 hl0) hρ).2 h0
    rw [Real.logb_inv, Real.logb_self_eq_one hl1] at h
    linarith
  have hv := hn r ⟨hr0, hr1⟩
  simp only [vr, hρr] at hv
  have hgx := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ h0 h1
  have hgy := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y hy ρ h0 h1
  apply Real.logb_injOn_pos hl1 hgx (Set.mem_Ioi.2 (mul_pos (zpow_pos hρ n) hgy))
  have hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ := by
    rw [Real.logb, Real.logb, Real.log_zpow, mul_div_assoc]
  rw [Real.logb_mul (zpow_pos hρ n).ne' hgy.ne', hz]
  rw [hr] at hv
  linarith

end GlobalTheory.PMon.Gauss

/- English proof (translation)
Introduce `l _ h s hsh w w' hφh hw' hrat hg`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Take `⟨ζ, o, ρ₀, ho, hζo, hζ0, hρ₀l, hρ₀1, hlt⟩` from `GlobalTheory.T.equal_gaussNorm_teichmuller_cancel l w w' hw' hg`. Establish `hζl : ζ ^ l = ζ` using `GlobalTheory.T.rootCancel_pow_eq_self_acris_gaussNorm l h s hsh w w' ζ o ρ₀ hφh hw' hrat hg ho hζo hζ0 hρ₀l.le hρ₀1 hlt`. Take `⟨c, hcu, hc⟩` from `GlobalTheory.PMon.Gauss.teichmuller_root_unity_eq_unit l ζ hζl hζ0`.

Use `⟨c, hcu, fun ρ h0 h1 => ?_⟩` and prove the remaining obligations. Establish `hρ : 0 < ρ` using `(inv_pos.2 hl0).trans_le h0`. Establish `hN` using `isGauss_gC_of_le l ρ h0 h1`. Distinguish the cases in `hw1 : w - zc l c * w' = 0`. Rewrite using `[hw1, gC_zero_of_radius l h0 h1]`.

Conclude with `mul_nonneg hρ.le (hN.1 w').1`. Establish `hφz : φc l (zc l c) = zc l c`. Rewrite using `[hc, frob_teich, hζl]`. Establish `hrat1 : φc l (w - zc l c * w') * w' = (w - zc l c * w') * φc l w'`. Rewrite using `[map_sub, map_mul, hφz]`.

Take the linear combination `hrat`. Take `⟨n, hn⟩` from `GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hsh (w - zc l c * w') w' hφh hw1 hw' hrat1`. Establish `hmono` using `gC_eq_zpow_mul_of_vr l _ w' hw1 hw' n hn`. Establish `hρ₀ : 0 < ρ₀` using `(inv_pos.2 hl0).trans hρ₀l`. Establish `hn1 : 1 ≤ n`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hle : n ≤ 0` using `by omega`. Establish `e` using `hmono ρ₀ hρ₀l.le hρ₀1`. Rewrite `hlt` using `[← hc]`.

Rewrite `hlt` using `[e]`. Establish `hg0` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l w' hw' ρ₀ hρ₀l.le hρ₀1`. Establish `: (1 : ℝ) ≤ ρ₀ ^ n` using `one_le_zpow_of_nonpos₀ hρ₀ hρ₀1.le hle`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hmono ρ h0 h1]`.

Establish `hle : ρ ^ n ≤ ρ ^ (1 : ℤ)` using `zpow_le_zpow_right_of_le_one₀ hρ h1.le hn1`. Rewrite `hle` using `[zpow_one]`. Conclude with `mul_le_mul_of_nonneg_right hle (hN.1 w').1`.
-/
theorem GlobalTheory.PMon.Gauss.one_digit : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ c : ℤ_[l], IsUnit c ∧ ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (w - zc l c * w') ≤ ρ * gC l ρ w' := by
  intro l _ h s hsh w w' hφh hw' hrat hg
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨ζ, o, ρ₀, ho, hζo, hζ0, hρ₀l, hρ₀1, hlt⟩ := GlobalTheory.T.equal_gaussNorm_teichmuller_cancel l w w' hw' hg
  have hζl : ζ ^ l = ζ := GlobalTheory.T.rootCancel_pow_eq_self_acris_gaussNorm l h s hsh w w' ζ o ρ₀ hφh hw' hrat hg ho hζo hζ0 hρ₀l.le hρ₀1 hlt
  obtain ⟨c, hcu, hc⟩ := GlobalTheory.PMon.Gauss.teichmuller_root_unity_eq_unit l ζ hζl hζ0
  refine ⟨c, hcu, fun ρ h0 h1 => ?_⟩
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  by_cases hw1 : w - zc l c * w' = 0
  · rw [hw1, gC_zero_of_radius l h0 h1]
    exact mul_nonneg hρ.le (hN.1 w').1
  have hφz : φc l (zc l c) = zc l c := by
    rw [hc, frob_teich, hζl]
  have hrat1 : φc l (w - zc l c * w') * w' = (w - zc l c * w') * φc l w' := by
    rw [map_sub, map_mul, hφz]
    linear_combination hrat
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hsh (w - zc l c * w') w' hφh hw1 hw' hrat1
  have hmono := gC_eq_zpow_mul_of_vr l _ w' hw1 hw' n hn
  have hρ₀ : 0 < ρ₀ := (inv_pos.2 hl0).trans hρ₀l
  have hn1 : 1 ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hle : n ≤ 0 := by omega
    have e := hmono ρ₀ hρ₀l.le hρ₀1
    rw [← hc] at hlt
    rw [e] at hlt
    have hg0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l w' hw' ρ₀ hρ₀l.le hρ₀1
    have : (1 : ℝ) ≤ ρ₀ ^ n := one_le_zpow_of_nonpos₀ hρ₀ hρ₀1.le hle
    nlinarith
  rw [hmono ρ h0 h1]
  have hle : ρ ^ n ≤ ρ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hρ h1.le hn1
  rw [zpow_one] at hle
  exact mul_le_mul_of_nonneg_right hle (hN.1 w').1
