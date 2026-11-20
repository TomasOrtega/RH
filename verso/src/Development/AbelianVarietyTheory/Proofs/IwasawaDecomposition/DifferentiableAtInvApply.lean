import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtDet

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.Mem.GaussPhase

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.DifferentiableDet.differentiableAt_det`. Consider the case `exact _root_.GlobalTheory.DifferentiableDet.differentiableAt_det`. Consider the case `(apply _root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.DifferentiableDet.differentiableAt_det ..)`.
-/
theorem differentiableAt_det (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t := by
  first
  | exact @_root_.GlobalTheory.DifferentiableDet.differentiableAt_det
  | exact _root_.GlobalTheory.DifferentiableDet.differentiableAt_det
  | (apply _root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DifferentiableDet.differentiableAt_det ..)

/- English proof (translation)
Establish `hadj : DifferentiableAt ℝ (fun s => (M s).adjugate i j) t`. Use `differentiableAt_det (fun s => (M s).updateRow j (Pi.single i 1)) t (by` as an intermediate fact. Introduce `a b`. Distinguish the cases in `h : a = j`. Simplify using `only [updateRow_apply, h, if_true]`.

Conclude with `differentiableAt_const _`. Simplify using `only [updateRow_apply, h, if_false]`. Conclude with `hM a b)`. Simplify `this` using `only [adjugate_apply]`. Use `((differentiableAt_det M t hM).fun_inv hne).mul hadj` as an intermediate fact.

Use `this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `[Matrix.inv_def, Ring.inverse_eq_inv']`.
-/
theorem differentiableAt_inv_apply (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) (hne : (M t).det ≠ 0) (i j : σ) :
    DifferentiableAt ℝ (fun s => (M s)⁻¹ i j) t := by
  have hadj : DifferentiableAt ℝ (fun s => (M s).adjugate i j) t := by
    have := differentiableAt_det (fun s => (M s).updateRow j (Pi.single i 1)) t (by
      intro a b
      by_cases h : a = j
      · simp only [updateRow_apply, h, if_true]
        exact differentiableAt_const _
      · simp only [updateRow_apply, h, if_false]
        exact hM a b)
    simpa only [adjugate_apply] using this
  have := ((differentiableAt_det M t hM).fun_inv hne).mul hadj
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

omit [DecidableEq σ] in
/- English proof (translation)
Simplify using `only [dotProduct]`. Conclude with `HasDerivAt.fun_sum fun k _ => (hasDerivAt_pi.mp h k).const_mul _`.
-/
theorem hasDerivAt_dot (x : σ → ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ} (h : HasDerivAt w w' t) :
    HasDerivAt (fun s => x ⬝ᵥ w s) (x ⬝ᵥ w') t := by
  simp only [dotProduct]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pi.mp h k).const_mul _

omit [DecidableEq σ] in
/- English proof (translation)
The claim follows from `hasDerivAt_pi.mpr fun i => hasDerivAt_dot (S i) h`.
-/
theorem hasDerivAt_mulVec (S : Matrix σ σ ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ}
    (h : HasDerivAt w w' t) : HasDerivAt (fun s => S *ᵥ w s) (S *ᵥ w') t :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_dot (S i) h

omit [DecidableEq σ] in
/- English proof (translation)
Rewrite using `[dotProduct_mulVec, ← mulVec_transpose, hS]`.
-/
theorem dot_symm {S : Matrix σ σ ℂ} (hS : Sᵀ = S) (a b : σ → ℂ) :
    (S *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (S *ᵥ b) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS]

/- English proof (translation)
Introduce `w u`. Establish `hof : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t` using `Complex.ofRealCLM.hasDerivAt`. Use `set M : ℝ → Matrix σ σ ℂ := fun s => 1 - ((s : ℂ) ^ 2) • (T * S) with hMdef`. Establish `hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t`. Introduce `i j`.

Simplify using `only [hMdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `(differentiableAt_const _).fun_sub ((hof.differentiableAt.fun_pow 2).mul_const _)`. Establish `hne : (M t).det ≠ 0` using `hu.ne_zero`. Establish `hev : ∀ᶠ s in nhds t, (M s).det ≠ 0` using `(differentiableAt_det M t hM).continuousAt.eventually_ne hne`. Establish `hwd : DifferentiableAt ℝ w t`.

Use `differentiableAt_pi.mpr fun i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `DifferentiableAt ℝ (fun s => ∑ k, (M s)⁻¹ i k * (y k + (s : ℂ) * (T *ᵥ x) k)) t`. Conclude with `DifferentiableAt.fun_sum fun k _ => (differentiableAt_inv_apply M t hM hne i k).fun_mul ((differentiableAt_const _).fun_add (hof.differentiableAt.mul_const _))`. Take `⟨w', hw⟩ : ∃ w', HasDerivAt w w' t` from `⟨_, hwd.hasDerivAt⟩`. Establish `hU : HasDerivAt u ((t : ℂ) • S *ᵥ w' + S *ᵥ w t) t`.

Use `(hof.fun_smul (hasDerivAt_mulVec S hw)).const_add x` as an intermediate fact. Simplify `this` using `only [one_smul]`. Use `set u' := (t : ℂ) • S *ᵥ w' + S *ᵥ w t with hu'`. Establish `hkey : ∀ s, (M s).det ≠ 0 → w s = y + (s : ℂ) • T *ᵥ u s`. Introduce `s hs`.

Establish `h1 : M s *ᵥ w s = y + (s : ℂ) • T *ᵥ x`. Express the relevant statement in the definitionally equal form `M s *ᵥ ((M s)⁻¹ *ᵥ _) = _`. Rewrite using `[mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs), one_mulVec]`. Simplify using `only [hMdef, sub_mulVec, one_mulVec, smul_mulVec] at h1`. Simplify using `only [u, mulVec_add, mulVec_smul, mulVec_mulVec, smul_add, smul_smul]`.

Rewrite using `[← add_assoc, ← h1, pow_two, sub_add_cancel]`. Establish `hw2 : HasDerivAt w ((t : ℂ) • T *ᵥ u' + T *ᵥ u t) t`. Use `(hof.fun_smul (hasDerivAt_mulVec T hU)).const_add y` as an intermediate fact. Simplify using `only [one_smul] at this`. Use `this.congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hev] with s hs using hkey s hs`. Establish `hw' : w' = (t : ℂ) • T *ᵥ u' + T *ᵥ u t` using `hw.unique hw2`. Establish `hx : x = u t - (t : ℂ) • S *ᵥ w t` using `by simp [u]`. Establish `hy : y = w t - (t : ℂ) • T *ᵥ u t` using `by rw [eq_sub_iff_add_eq]; exact (hkey t hne).symm`. Establish `hmain` using `(hof.div_const 2).fun_mul ((hasDerivAt_dot x hw).fun_add (hasDerivAt_dot y hU))`.

Use `hmain.congr_deriv ?_` and prove the remaining obligations. Establish `e1 : x ⬝ᵥ w t = u t ⬝ᵥ w t - t * (w t ⬝ᵥ S *ᵥ w t)` using `by conv_lhs => rw [hx]`. Rewrite using `[sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]`. Establish `e2 : y ⬝ᵥ u t = u t ⬝ᵥ w t - t * (u t ⬝ᵥ T *ᵥ u t)` using `by conv_lhs => rw [hy]`. Rewrite using `[sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul, dotProduct_comm]`.

Establish `e3 : x ⬝ᵥ w' = u t ⬝ᵥ w' - t * (w t ⬝ᵥ S *ᵥ w')` using `by conv_lhs => rw [hx]`. Rewrite using `[sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]`. Establish `e4 : y ⬝ᵥ u' = w t ⬝ᵥ u' - t * (u t ⬝ᵥ T *ᵥ u')` using `by conv_lhs => rw [hy]`. Rewrite using `[sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul]`. Establish `e5 : w t ⬝ᵥ u' = t * (w t ⬝ᵥ S *ᵥ w') + w t ⬝ᵥ S *ᵥ w t`.

Rewrite using `[hu', dotProduct_add, dotProduct_smul, smul_eq_mul]`. Establish `e6 : u t ⬝ᵥ w' = t * (u t ⬝ᵥ T *ᵥ u') + u t ⬝ᵥ T *ᵥ u t` using `by conv_lhs => rw [hw']`. Rewrite using `[dotProduct_add, dotProduct_smul, smul_eq_mul]`. Rewrite using `[e1, e2, e3, e4, e5, e6]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_phase (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ)
    (x y : σ → ℂ) (t : ℝ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hu : IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det) :
    let w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x)
    let u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s
    HasDerivAt (fun s : ℝ => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s)) (u t ⬝ᵥ w t) t := by
  intro w u
  have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  set M : ℝ → Matrix σ σ ℂ := fun s => 1 - ((s : ℂ) ^ 2) • (T * S) with hMdef
  have hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t := by
    intro i j
    simp only [hMdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (differentiableAt_const _).fun_sub ((hof.differentiableAt.fun_pow 2).mul_const _)
  have hne : (M t).det ≠ 0 := hu.ne_zero
  have hev : ∀ᶠ s in nhds t, (M s).det ≠ 0 :=
    (differentiableAt_det M t hM).continuousAt.eventually_ne hne
  have hwd : DifferentiableAt ℝ w t := by
    refine differentiableAt_pi.mpr fun i => ?_
    change DifferentiableAt ℝ (fun s => ∑ k, (M s)⁻¹ i k * (y k + (s : ℂ) * (T *ᵥ x) k)) t
    exact DifferentiableAt.fun_sum fun k _ =>
      (differentiableAt_inv_apply M t hM hne i k).fun_mul
        ((differentiableAt_const _).fun_add (hof.differentiableAt.mul_const _))
  obtain ⟨w', hw⟩ : ∃ w', HasDerivAt w w' t := ⟨_, hwd.hasDerivAt⟩
  have hU : HasDerivAt u ((t : ℂ) • S *ᵥ w' + S *ᵥ w t) t := by
    have := (hof.fun_smul (hasDerivAt_mulVec S hw)).const_add x
    simpa only [one_smul] using this
  set u' := (t : ℂ) • S *ᵥ w' + S *ᵥ w t with hu'
  have hkey : ∀ s, (M s).det ≠ 0 → w s = y + (s : ℂ) • T *ᵥ u s := by
    intro s hs
    have h1 : M s *ᵥ w s = y + (s : ℂ) • T *ᵥ x := by
      change M s *ᵥ ((M s)⁻¹ *ᵥ _) = _
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs), one_mulVec]
    simp only [hMdef, sub_mulVec, one_mulVec, smul_mulVec] at h1
    simp only [u, mulVec_add, mulVec_smul, mulVec_mulVec, smul_add, smul_smul]
    rw [← add_assoc, ← h1, pow_two, sub_add_cancel]
  have hw2 : HasDerivAt w ((t : ℂ) • T *ᵥ u' + T *ᵥ u t) t := by
    have := (hof.fun_smul (hasDerivAt_mulVec T hU)).const_add y
    simp only [one_smul] at this
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs using hkey s hs
  have hw' : w' = (t : ℂ) • T *ᵥ u' + T *ᵥ u t := hw.unique hw2
  have hx : x = u t - (t : ℂ) • S *ᵥ w t := by simp [u]
  have hy : y = w t - (t : ℂ) • T *ᵥ u t := by rw [eq_sub_iff_add_eq]; exact (hkey t hne).symm
  have hmain := (hof.div_const 2).fun_mul ((hasDerivAt_dot x hw).fun_add (hasDerivAt_dot y hU))
  refine hmain.congr_deriv ?_
  have e1 : x ⬝ᵥ w t = u t ⬝ᵥ w t - t * (w t ⬝ᵥ S *ᵥ w t) := by
    conv_lhs => rw [hx]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]
  have e2 : y ⬝ᵥ u t = u t ⬝ᵥ w t - t * (u t ⬝ᵥ T *ᵥ u t) := by
    conv_lhs => rw [hy]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul, dotProduct_comm]
  have e3 : x ⬝ᵥ w' = u t ⬝ᵥ w' - t * (w t ⬝ᵥ S *ᵥ w') := by
    conv_lhs => rw [hx]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]
  have e4 : y ⬝ᵥ u' = w t ⬝ᵥ u' - t * (u t ⬝ᵥ T *ᵥ u') := by
    conv_lhs => rw [hy]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul]
  have e5 : w t ⬝ᵥ u' = t * (w t ⬝ᵥ S *ᵥ w') + w t ⬝ᵥ S *ᵥ w t := by
    rw [hu', dotProduct_add, dotProduct_smul, smul_eq_mul]
  have e6 : u t ⬝ᵥ w' = t * (u t ⬝ᵥ T *ᵥ u') + u t ⬝ᵥ T *ᵥ u t := by
    conv_lhs => rw [hw']
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [e1, e2, e3, e4, e5, e6]
  ring

end GlobalTheory.Mem.GaussPhase
