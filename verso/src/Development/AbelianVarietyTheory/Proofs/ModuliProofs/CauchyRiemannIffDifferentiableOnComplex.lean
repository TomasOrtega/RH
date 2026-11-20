import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

/- English proof (translation)
Use extensionality with `j`. Distinguish the cases in `hj : j = a`. Substitute `hj` using the available equality. Apply the tactic sequence `apply Complex.ext <;> simp`. Simplify using `[hj]`.
-/
private lemma pi_single_eq_re_smul_add_im_smul {g : ℕ} (a : Fin g) (w : ℂ) :
    (Pi.single a w : Fin g → ℂ) =
      (w.re : ℝ) • (Pi.single a 1 : Fin g → ℂ) + (w.im : ℝ) • (I • (Pi.single a 1 : Fin g → ℂ)) := by
  ext j
  by_cases hj : j = a
  · subst hj
    apply Complex.ext <;> simp
  · simp [hj]

/- English proof (translation)
Establish `hI : ∀ a, L (I • (Pi.single a 1 : Fin g → ℂ)) = I * L (Pi.single a 1)`. Introduce `a`. Take the linear combination `(-I) * h a + L (I • (Pi.single a 1 : Fin g → ℂ)) * I_sq`. Establish `hline : ∀ a (w : ℂ), L (Pi.single a w : Fin g → ℂ) = w * L (Pi.single a 1)`. Introduce `a w`.

Rewrite using `[pi_single_eq_re_smul_add_im_smul a w, map_add, map_smul, map_smul, hI a]`. Use `conv_rhs => rw [← Complex.re_add_im w]`. Simplify using `only [Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∀ u : Fin g → ℂ, L u = ∑ a, u a * L (Pi.single a 1)`.

Introduce `u`. Use `conv_lhs => rw [← Finset.univ_sum_single u]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl (fun a _ => hline a (u a))`. Rewrite using `[hsum, hsum v, smul_eq_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_I_smul_of_cauchyRiemann {g : ℕ} (L : (Fin g → ℂ) →L[ℝ] ℂ)
    (h : ∀ a, L (Pi.single a 1 : Fin g → ℂ) + I * L (I • (Pi.single a 1 : Fin g → ℂ)) = 0)
    (c : ℂ) (v : Fin g → ℂ) : L (c • v) = c • L v := by

  have hI : ∀ a, L (I • (Pi.single a 1 : Fin g → ℂ)) = I * L (Pi.single a 1) := by
    intro a
    linear_combination (-I) * h a + L (I • (Pi.single a 1 : Fin g → ℂ)) * I_sq
  have hline : ∀ a (w : ℂ), L (Pi.single a w : Fin g → ℂ) = w * L (Pi.single a 1) := by
    intro a w
    rw [pi_single_eq_re_smul_add_im_smul a w, map_add, map_smul, map_smul, hI a]
    conv_rhs => rw [← Complex.re_add_im w]
    simp only [Complex.real_smul]
    ring
  have hsum : ∀ u : Fin g → ℂ, L u = ∑ a, u a * L (Pi.single a 1) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => hline a (u a))
  rw [hsum, hsum v, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `g U f hU`. Use `⟨fun hR => ⟨fun hCR => ?_, fun hC => ?_⟩, fun hC => ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `hzR : DifferentiableAt ℝ f z` using `hR.differentiableAt (hU.mem_nhds hz)`. Use `set L := fderiv ℝ f z with hL`.

Establish `hlin : ∀ (c : ℂ) (v : Fin g → ℂ), L (c • v) = c • L v` using `map_I_smul_of_cauchyRiemann L (fun a => hCR a z hz)`. Set `L' : (Fin g → ℂ) →L[ℂ] ℂ` to `{ toFun := L map_add' := L.map_add map_smul' := hlin cont := L.continuous }`. Establish `hres : L'.restrictScalars ℝ = L`. Use extensionality with `v`. Both sides reduce to the same expression.

Conclude with `(hasFDerivAt_of_restrictScalars ℝ hzR.hasFDerivAt hres).differentiableAt.differentiableWithinAt`. Introduce `a z hz`. Establish `hzC : DifferentiableAt ℂ f z` using `hC.differentiableAt (hU.mem_nhds hz)`. Rewrite using `[hzC.fderiv_restrictScalars ℝ]`. Simplify using `only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]`.

Rewrite using `[← mul_assoc, I_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, fun v => SCV.differentiableOn_fderiv_apply hU hC v⟩` and prove the remaining obligations. Conclude with `(SCV.contDiffOn_of_differentiableOn hU hC ∞).restrict_scalars ℝ`.
-/
theorem cauchyRiemann_iff_differentiableOn_complex :
    ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  intro g U f hU
  refine ⟨fun hR => ⟨fun hCR => ?_, fun hC => ?_⟩, fun hC => ?_⟩
  ·
    intro z hz
    have hzR : DifferentiableAt ℝ f z := hR.differentiableAt (hU.mem_nhds hz)
    set L := fderiv ℝ f z with hL
    have hlin : ∀ (c : ℂ) (v : Fin g → ℂ), L (c • v) = c • L v :=
      map_I_smul_of_cauchyRiemann L (fun a => hCR a z hz)
    let L' : (Fin g → ℂ) →L[ℂ] ℂ :=
      { toFun := L
        map_add' := L.map_add
        map_smul' := hlin
        cont := L.continuous }
    have hres : L'.restrictScalars ℝ = L := by
      ext v; rfl
    exact (hasFDerivAt_of_restrictScalars ℝ hzR.hasFDerivAt hres).differentiableAt.differentiableWithinAt
  · intro a z hz
    have hzC : DifferentiableAt ℂ f z := hC.differentiableAt (hU.mem_nhds hz)
    rw [hzC.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    rw [← mul_assoc, I_mul_I]
    ring
  · refine ⟨?_, fun v => SCV.differentiableOn_fderiv_apply hU hC v⟩
    exact (SCV.contDiffOn_of_differentiableOn hU hC ∞).restrict_scalars ℝ

end GlobalTheory
