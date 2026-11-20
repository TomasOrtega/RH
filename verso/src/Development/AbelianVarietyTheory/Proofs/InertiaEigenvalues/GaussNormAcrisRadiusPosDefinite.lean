import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEndsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

/- English proof (translation)
Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_interp (a b c : ℝ) (h : b - a ≠ 0) :
    a * ((b - c) / (b - a)) + b * (1 - (b - c) / (b - a)) = c := by
  field_simp
  ring

/- English proof (translation)
Introduce `l _ x hx ρ hρ0 hρ1`. Establish `hN : ∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → IsGauss l r (gC l r)` using `fun r h0 h1 => isGauss_gC_target l r h0 h1`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hi0 : (0 : ℝ) < (l : ℝ)⁻¹` using `by positivity`. Establish `hi1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl`.

Establish `hnn : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → 0 ≤ gC l r x` using `fun r h0 h1 => ((hN r h0 h1).1 x).1`. Establish `h0 : gC l (l : ℝ)⁻¹ x ≠ 0` using `GlobalTheory.MemLoc.gauss_ne_zero l (fun r => gC l r) hN x hx`. Break down `hρ0.eq_or_lt with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `lt_of_le_of_ne (hnn _ le_rfl hi1) h0.symm`.

Assume the negation of the conclusion as `hneg`. Establish `hz : gC l ρ x = 0` using `le_antisymm (not_lt.1 hneg) (hnn ρ hρ0 hρ1)`. Take `⟨r₁, c, k, hr₁, -, hc, hmon⟩` from `GlobalTheory.MemLoc.gauss_slope l (fun r => gC l r) hN x h0`. Take `⟨ρ', h1', h2'⟩` from `exists_between (lt_min hr₁ h)`. Establish `hρ'0 : 0 < ρ'` using `hi0.trans h1'`.

Establish `hρ'r : ρ' < r₁` using `h2'.trans_le (min_le_left _ _)`. Establish `hρ'ρ : ρ' < ρ` using `h2'.trans_le (min_le_right _ _)`. Establish `hρpos : 0 < ρ` using `hi0.trans h`. Establish `hpos : 0 < gC l ρ' x`. Establish `e : gC l ρ' x = c * ρ' ^ k` using `hmon ρ' h1' hρ'r`.

Rewrite using `[e]`. Conclude with `mul_pos hc (zpow_pos hρ'0 k)`. Establish `hL1 : Real.log (l : ℝ)⁻¹ < Real.log ρ'` using `Real.log_lt_log hi0 h1'`. Establish `hL2 : Real.log ρ' < Real.log ρ` using `Real.log_lt_log hρ'0 hρ'ρ`. Establish `hd : 0 < Real.log ρ - Real.log (l : ℝ)⁻¹` using `by linarith`.

Establish `ht0 : 0 ≤ (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)` using `div_nonneg (by linarith) hd.le`. Establish `ht1 : (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) < 1` using `(div_lt_one hd).2 (by linarith)`. Establish `he : (l : ℝ)⁻¹ ^ ((Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) * ρ ^ (1 - (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) = ρ'`. Rewrite using `[Real.rpow_def_of_pos hi0, Real.rpow_def_of_pos hρpos, ← Real.exp_add, log_interp _ _ _ hd.ne', Real.exp_log hρ'0]`. Establish `hcv` using `GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x (l : ℝ)⁻¹ ρ _ le_rfl h.le hρ1 ht0 ht1.le`.

Rewrite `hcv` using `[he, hz, Real.zero_rpow (sub_pos.2 ht1).ne', mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gC_pos_of_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ →
    ρ < 1 → 0 < gC l ρ x := by
  intro l _ x hx ρ hρ0 hρ1
  have hN : ∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → IsGauss l r (gC l r) :=
    fun r h0 h1 => isGauss_gC_target l r h0 h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hnn : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → 0 ≤ gC l r x := fun r h0 h1 => ((hN r h0 h1).1 x).1
  have h0 : gC l (l : ℝ)⁻¹ x ≠ 0 := GlobalTheory.MemLoc.gauss_ne_zero l (fun r => gC l r) hN x hx
  rcases hρ0.eq_or_lt with h | h
  · subst h
    exact lt_of_le_of_ne (hnn _ le_rfl hi1) h0.symm
  by_contra hneg
  have hz : gC l ρ x = 0 := le_antisymm (not_lt.1 hneg) (hnn ρ hρ0 hρ1)
  obtain ⟨r₁, c, k, hr₁, -, hc, hmon⟩ := GlobalTheory.MemLoc.gauss_slope l (fun r => gC l r) hN x h0
  obtain ⟨ρ', h1', h2'⟩ := exists_between (lt_min hr₁ h)
  have hρ'0 : 0 < ρ' := hi0.trans h1'
  have hρ'r : ρ' < r₁ := h2'.trans_le (min_le_left _ _)
  have hρ'ρ : ρ' < ρ := h2'.trans_le (min_le_right _ _)
  have hρpos : 0 < ρ := hi0.trans h
  have hpos : 0 < gC l ρ' x := by
    have e : gC l ρ' x = c * ρ' ^ k := hmon ρ' h1' hρ'r
    rw [e]
    exact mul_pos hc (zpow_pos hρ'0 k)
  have hL1 : Real.log (l : ℝ)⁻¹ < Real.log ρ' := Real.log_lt_log hi0 h1'
  have hL2 : Real.log ρ' < Real.log ρ := Real.log_lt_log hρ'0 hρ'ρ
  have hd : 0 < Real.log ρ - Real.log (l : ℝ)⁻¹ := by linarith
  have ht0 : 0 ≤ (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) :=
    div_nonneg (by linarith) hd.le
  have ht1 : (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) < 1 :=
    (div_lt_one hd).2 (by linarith)
  have he : (l : ℝ)⁻¹ ^ ((Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) *
      ρ ^ (1 - (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) = ρ' := by
    rw [Real.rpow_def_of_pos hi0, Real.rpow_def_of_pos hρpos, ← Real.exp_add,
      log_interp _ _ _ hd.ne', Real.exp_log hρ'0]
  have hcv := GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x (l : ℝ)⁻¹ ρ _ le_rfl h.le hρ1 ht0 ht1.le
  rw [he, hz, Real.zero_rpow (sub_pos.2 ht1).ne', mul_zero] at hcv
  linarith

/- English proof (translation)
The claim follows from `gC_pos_of_ne_zero`.
-/
theorem gC_pos_target : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 →
    0 < gC l ρ x :=
  gC_pos_of_ne_zero

end GlobalTheory.PMon.Gauss

end
