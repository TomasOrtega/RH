import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxe

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Establish `h1 : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i)` using `contDiff_pi.mp contDiff_id i`. Conclude with `contDiff_pi.mp h1 j`.
-/
theorem contDiff_entry (i : ι) (j : κ) : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i j) := by
  have h1 : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i) := contDiff_pi.mp contDiff_id i
  exact contDiff_pi.mp h1 j

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Conclude with `contDiffOn_pi.mp (contDiffOn_pi.mp h i) j`. Introduce `h`. Conclude with `contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => h i j`.
-/
theorem contDiffOn_matrix_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (f : E → Matrix ι κ ℂ) : ContDiffOn ℝ ∞ f s ↔ ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s := by
  constructor
  · intro h i j
    exact contDiffOn_pi.mp (contDiffOn_pi.mp h i) j
  · intro h
    exact contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => h i j

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Conclude with `contDiff_pi.mp (contDiff_pi.mp h i) j`. Introduce `h`. Conclude with `contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => h i j`.
-/
theorem contDiff_matrix_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → Matrix ι κ ℂ) : ContDiff ℝ ∞ f ↔ ∀ i j, ContDiff ℝ ∞ (fun x => f x i j) := by
  constructor
  · intro h i j
    exact contDiff_pi.mp (contDiff_pi.mp h i) j
  · intro h
    exact contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => h i j

/- English proof (translation)
Establish `e : (fun x : Matrix ι ι ℂ => x.det) = fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i`. Use function extensionality and compare the values at `x`. Conclude with `Matrix.det_apply' x`. Rewrite using `[e]`. Apply the tactic sequence `refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_entry _ _)`.
-/
theorem contDiff_det : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have e : (fun x : Matrix ι ι ℂ => x.det) =
      fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i := by
    funext x; exact Matrix.det_apply' x
  rw [e]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_entry _ _)

/- English proof (translation)
Rewrite using `[contDiff_matrix_iff]`. Introduce `i j`. Simplify using `only [Matrix.adjugate_apply]`. Use `contDiff_det.comp ?_` and prove the remaining obligations. Rewrite using `[contDiff_matrix_iff]`.

Introduce `a b`. Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`. Conclude with `contDiff_const`. Apply the tactic sequence `exact contDiff_entry a b`.
-/
theorem contDiff_adjugate : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => x.adjugate) := by
  rw [contDiff_matrix_iff]
  intro i j
  simp only [Matrix.adjugate_apply]
  refine contDiff_det.comp ?_
  rw [contDiff_matrix_iff]
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry a b

/- English proof (translation)
The claim follows from `isOpen_ne_fun (contDiff_det (ι := ι)).continuous continuous_const`.
-/
theorem isOpen_det_ne : IsOpen {x : Matrix ι ι ℂ | x.det ≠ 0} :=
  isOpen_ne_fun (contDiff_det (ι := ι)).continuous continuous_const

/- English proof (translation)
Establish `h : ∀ x ∈ {x : Matrix ι ι ℂ | x.det ≠ 0}, x⁻¹ = (x.det)⁻¹ • x.adjugate` using `fun x _ => by`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Use `ContDiffOn.congr ?_ h` and prove the remaining obligations. Rewrite using `[contDiffOn_matrix_iff]`. Introduce `i j`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Conclude with `(contDiff_det.contDiffOn.inv fun x hx => hx).mul (contDiff_matrix_iff _ |>.mp contDiff_adjugate i j).contDiffOn`.
-/
theorem contDiffOn_inv : ContDiffOn ℝ ∞ (fun x : Matrix ι ι ℂ => x⁻¹) {x | x.det ≠ 0} := by
  have h : ∀ x ∈ {x : Matrix ι ι ℂ | x.det ≠ 0}, x⁻¹ = (x.det)⁻¹ • x.adjugate := fun x _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContDiffOn.congr ?_ h
  rw [contDiffOn_matrix_iff]
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (contDiff_det.contDiffOn.inv fun x hx => hx).mul (contDiff_matrix_iff _ |>.mp contDiff_adjugate i j).contDiffOn

def entL (a : ι) (k : κ) : Matrix ι κ ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap { toFun := fun x => x a k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem entL_apply (a : ι) (k : κ) (x : Matrix ι κ ℂ) : entL a k x = x a k := rfl

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1` using `(contDiffOn_inv.contDiffAt (isOpen_det_ne.mem_nhds (by simp))).differentiableAt (by simp)`. Establish `hL` using `hd.hasFDerivAt`. Use `set L := fderiv ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 with hLdef`. It suffices to establish `hLe : L = -ContinuousLinearMap.id ℝ (Matrix ι ι ℂ) by rwa [hLe] at hL`. Establish `hev : ∀ a b : ι, (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b) =ᶠ[nhds 1] fun _ => (1 : Matrix ι ι ℂ) a b`.

Introduce `a b`. Use `filter_upwards [isOpen_det_ne.mem_nhds (show (1 : Matrix ι ι ℂ).det ≠ 0 by simp)] with x hx`. Rewrite using `[Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.mpr hx)]`. Establish `hent : ∀ a b : ι, HasFDerivAt (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b) (∑ k, ((1 : Matrix ι ι ℂ) a k • (entL k b).comp L + ((1 : Matrix ι ι ℂ)⁻¹ k b) • entL a k)) 1`. Introduce `a b`.

Simplify using `only [Matrix.mul_apply]`. Use `HasFDerivAt.fun_sum (u := Finset.univ) (A := fun k (x : Matrix ι ι ℂ) => x a k * x⁻¹ k b) fun k _ => ?_` and prove the remaining obligations. Establish `h1 : HasFDerivAt (fun x : Matrix ι ι ℂ => x a k) (entL a k) 1` using `(entL a k).hasFDerivAt`. Establish `h2 : HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹ k b) ((entL k b).comp L) 1` using `(entL k b).hasFDerivAt.comp 1 hL`. Conclude with `h1.mul h2`.

Use extensionality with `X i j`. Establish `h0` using `(hent i j).unique ((hasFDerivAt_const ((1 : Matrix ι ι ℂ) i j) (1 : Matrix ι ι ℂ)).congr_of_eventuallyEq (hev i j))`. Establish `h0X` using `congrArg (fun T : Matrix ι ι ℂ →L[ℝ] ℂ => T X) h0`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, entL_apply, smul_eq_mul, inv_one, ContinuousLinearMap.zero_apply, Finset.sum_add_distrib] at h0X`. Simplify using `only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] at h0X`.

Simplify using `only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Matrix.neg_apply]`. Take the linear combination `h0X`.
-/
theorem hasFDerivAt_inv_one :
    HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹) (-ContinuousLinearMap.id ℝ (Matrix ι ι ℂ)) 1 := by
  have hd : DifferentiableAt ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 :=
    (contDiffOn_inv.contDiffAt (isOpen_det_ne.mem_nhds (by simp))).differentiableAt (by simp)
  have hL := hd.hasFDerivAt
  set L := fderiv ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 with hLdef
  suffices hLe : L = -ContinuousLinearMap.id ℝ (Matrix ι ι ℂ) by rwa [hLe] at hL
  have hev : ∀ a b : ι, (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b) =ᶠ[nhds 1] fun _ => (1 : Matrix ι ι ℂ) a b := by
    intro a b
    filter_upwards [isOpen_det_ne.mem_nhds (show (1 : Matrix ι ι ℂ).det ≠ 0 by simp)] with x hx
    rw [Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.mpr hx)]
  have hent : ∀ a b : ι, HasFDerivAt (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b)
      (∑ k, ((1 : Matrix ι ι ℂ) a k • (entL k b).comp L + ((1 : Matrix ι ι ℂ)⁻¹ k b) • entL a k)) 1 := by
    intro a b
    simp only [Matrix.mul_apply]
    refine HasFDerivAt.fun_sum (u := Finset.univ) (A := fun k (x : Matrix ι ι ℂ) => x a k * x⁻¹ k b) fun k _ => ?_
    have h1 : HasFDerivAt (fun x : Matrix ι ι ℂ => x a k) (entL a k) 1 := (entL a k).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹ k b) ((entL k b).comp L) 1 := (entL k b).hasFDerivAt.comp 1 hL
    exact h1.mul h2
  ext X i j
  have h0 := (hent i j).unique ((hasFDerivAt_const ((1 : Matrix ι ι ℂ) i j) (1 : Matrix ι ι ℂ)).congr_of_eventuallyEq (hev i j))
  have h0X := congrArg (fun T : Matrix ι ι ℂ →L[ℝ] ℂ => T X) h0
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, entL_apply, smul_eq_mul, inv_one,
    ContinuousLinearMap.zero_apply, Finset.sum_add_distrib] at h0X
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq'] at h0X
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Matrix.neg_apply]
  linear_combination h0X

end PositivityTheory.RgBcC.Cxe
