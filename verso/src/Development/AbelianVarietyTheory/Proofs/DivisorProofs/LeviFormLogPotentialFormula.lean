import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.LeviLogChain

variable {e : ℕ}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem levi_add_of {f g : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (w : Fin e → ℂ) :
    levi (fun x => f x + g x) z w = levi f z w + levi g z w := by
  have h1 : fderiv ℝ (fun x => f x + g x) =ᶠ[𝓝 z] fun x => fderiv ℝ f x + fderiv ℝ g x := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with x hx hy
    exact fderiv_fun_add (hx.differentiableAt (by norm_num)) (hy.differentiableAt (by norm_num))
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold levi
  rw [h1.fderiv_eq, fderiv_fun_add hf' hg']
  simp only [ContinuousLinearMap.add_apply]
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem levi_const_mul_of {f : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (w : Fin e → ℂ) : levi (fun x => c * f x) z w = c * levi f z w := by
  have h1 : fderiv ℝ (fun x => c * f x) =ᶠ[𝓝 z] fun x => c • fderiv ℝ f x := by
    filter_upwards [hf.eventually (by simp)] with x hx
    exact fderiv_const_mul (hx.differentiableAt (by norm_num)) c
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold levi
  rw [h1.fderiv_eq, fderiv_fun_const_smul hf']
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem levi_sum_of {m : ℕ} (f : Fin m → (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) z) (w : Fin e → ℂ) (s : Finset (Fin m)) :
    ContDiffAt ℝ 2 (fun x => ∑ i ∈ s, f i x) z ∧
      levi (fun x => ∑ i ∈ s, f i x) z w = ∑ i ∈ s, levi (f i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi]; exact contDiffAt_const
  | insert b s hb ih =>
    have he : (fun x => ∑ i ∈ insert b s, f i x) = fun x => f b x + ∑ i ∈ s, f i x := by
      funext x; rw [Finset.sum_insert hb]
    rw [he, Finset.sum_insert hb]
    exact ⟨(hf b).add ih.1, by rw [levi_add_of (hf b) ih.1 w, ih.2]⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_log {r : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (hr : ContDiffAt ℝ 2 r z) (hz : 0 < r z)
    (w : Fin e → ℂ) :
    levi (fun x => Real.log (r x)) z w = levi r z w / r z -
      ((fderiv ℝ r z w ^ 2 + fderiv ℝ r z (Complex.I • w) ^ 2) / 4) / r z ^ 2 := by
  have hz0 : r z ≠ 0 := hz.ne'
  have hr' : HasFDerivAt (fderiv ℝ r) (fderiv ℝ (fderiv ℝ r) z) z :=
    ((hr.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hinv : HasFDerivAt (fun x => (r x)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(r z ^ 2)⁻¹)).comp (fderiv ℝ r z)) z :=
    (hasFDerivAt_inv hz0).comp z ((hr.differentiableAt (by norm_num)).hasFDerivAt)
  have hev : fderiv ℝ (fun x => Real.log (r x)) =ᶠ[𝓝 z] fun x => (r x)⁻¹ • fderiv ℝ r x := by
    filter_upwards [hr.eventually (by simp), hr.continuousAt.eventually_ne hz0] with y hy hy0
    have d1 := (hy.differentiableAt (by norm_num)).hasFDerivAt
    rw [(d1.log hy0).fderiv]
  have hD := ((hinv.smul hr').congr_of_eventuallyEq hev).fderiv
  unfold levi
  rw [hD]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_poincare_chain : ∀ {e m : ℕ} (k : (Fin e → ℂ) → ℝ) (r : Fin m → (Fin e → ℂ) → ℝ) (c : ℝ)
    (z w : Fin e → ℂ), ContDiffAt ℝ 2 k z → (∀ i, ContDiffAt ℝ 2 (r i) z) → (∀ i, 0 < r i z) →
    2 / Real.pi * levi (fun y => k y + -(c / 2) * ∑ i, Real.log (r i y)) z w =
      2 / Real.pi * levi k z w + c * ∑ i, (1 / Real.pi * ((fderiv ℝ (r i) z w ^ 2 +
        fderiv ℝ (r i) z (Complex.I • w) ^ 2) / 4) / r i z ^ 2 - 1 / Real.pi * levi (r i) z w / r i z) := by
  intro e m k r c z w hk hr hpos
  have hlog : ∀ i, ContDiffAt ℝ 2 (fun y => Real.log (r i y)) z :=
    fun i => (hr i).log (hpos i).ne'
  have hS := levi_sum_of (fun i y => Real.log (r i y)) hlog w Finset.univ
  rw [levi_add_of hk (contDiffAt_const.mul hS.1) w, levi_const_mul_of _ hS.1 w, hS.2]
  simp only [levi_log (hr _) (hpos _) w]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.LeviLogChain

end
