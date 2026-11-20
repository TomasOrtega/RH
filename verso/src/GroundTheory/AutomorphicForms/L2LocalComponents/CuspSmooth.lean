import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.TensorProductTheorem.CentralCuspSplit
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite

open MeasureTheory Filter Topology

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm Reduction RightCosetSpace UnitaryAdmissible

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def cuspVecL : cuspForms K n →ₗ[ℂ] CuspL2 μ := cuspToL2 μ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toLp_cuspVecL (φ : cuspForms K n) :
    toLp μ (cuspVecL μ φ) = ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) := rfl

/- English proof (translation)
Use `⟨φ.2.1.continuous.comp continuous_subtype_val, fun γ hγ y => ?_, ?_⟩` and prove the remaining obligations. Take `⟨γ', hγ'⟩` from `Subgroup.mem_subgroupOf.1 hγ`. Express the relevant statement in the definitionally equal form `(φ : AdelicGLn.AdelicGL K n → ℂ) ((γ : AdelicGLn.AdelicGL K n) * y) = _`. Rewrite using `[← hγ']`. Conclude with `φ.2.1.isLeftInvariant γ' _`.

Use `filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq (coeFn_cuspToL2 μ φ)] with y hy`. Conclude with `hy.trans (cuspQuot_mk _ y)`.
-/
theorem isContRep_cuspToL2 (φ : cuspForms K n) :
    IsContRep μ (toLp μ (cuspVecL μ φ))
      (fun y => (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) := by
  refine ⟨φ.2.1.continuous.comp continuous_subtype_val, fun γ hγ y => ?_, ?_⟩
  · obtain ⟨γ', hγ'⟩ := Subgroup.mem_subgroupOf.1 hγ
    change (φ : AdelicGLn.AdelicGL K n → ℂ) ((γ : AdelicGLn.AdelicGL K n) * y) = _
    rw [← hγ']
    exact φ.2.1.isLeftInvariant γ' _
  · filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq (coeFn_cuspToL2 μ φ)] with y hy
    exact hy.trans (cuspQuot_mk _ y)

variable {μ} in

/- English proof (translation)
The claim follows from `toLp_injective μ (Lp.ext (hv.ae_eq_quotFun.trans hw.ae_eq_quotFun.symm))`.
-/
theorem eq_of_isContRep {v w : CuspL2 μ} {F : normOneGL K n → ℂ} (hv : IsContRep μ (toLp μ v) F)
    (hw : IsContRep μ (toLp μ w) F) : v = w :=
  toLp_injective μ (Lp.ext (hv.ae_eq_quotFun.trans hw.ae_eq_quotFun.symm))

/- English proof (translation)
Establish `e : infEmb K n a = (retractOne (infEmb K n a) : AdelicGLn.AdelicGL K n) * centralSection K n (detModule K n (infEmb K n a))`. Rewrite using `[coe_retractOne, inv_mul_cancel_right]`. Rewrite using `[e, ← mul_assoc, apply_mul_centralSection_of_mem hφ, retract_infEmb]`.
-/
theorem apply_mul_infEmb_of_mem {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n)
    (y : AdelicGLn.AdelicGL K n) (a : archGroup K n) :
    (φ : AdelicGLn.AdelicGL K n → ℂ) (y * infEmb K n a) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (y * (archP K n a : AdelicGLn.AdelicGL K n)) := by
  have e : infEmb K n a = (retractOne (infEmb K n a) : AdelicGLn.AdelicGL K n) *
      centralSection K n (detModule K n (infEmb K n a)) := by
    rw [coe_retractOne, inv_mul_cancel_right]
  rw [e, ← mul_assoc, apply_mul_centralSection_of_mem hφ, retract_infEmb]

/- English proof (translation)
Take `⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩` from `exists_archCartanData K n`. Take `⟨P, hP, hPd, hPφ⟩` from `exists_aeval_uActionCusp_laplacianU_eq_zero φ b ε B hε horth hsymm hinv hK`. Take `⟨κ, hκs, hκc, -, hκ⟩` from `(isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian ν b P hP hPd Filter.univ_mem`. Use `⟨κ, ⟨hκs, hκc⟩, fun g => ?_⟩` and prove the remaining obligations. Establish `h` using `hκ (sliceL g ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩) (aeval_laplacian_sliceL_eq_zero b P hPφ g) 1`.

Establish `e1 : ∀ x, ((sliceL g ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩ : (isExpLieAlgebra K n).smoothFuns (F` using `ℂ)) : archGroup K n → ℂ) x = (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n x) := fun x => rfl`. Simplify using `only [e1, one_mul, map_one, mul_one] at h`. Conclude with `h`.
-/
theorem exists_kernel_cuspForm (φ : cuspForms K n) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] :
    ∃ κ : archGroup K n → ℂ, (isExpLieAlgebra K n).IsTestFunction κ ∧
      ∀ g : AdelicGLn.AdelicGL K n, (φ : AdelicGLn.AdelicGL K n → ℂ) g =
        ∫ a, (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n a) * κ a ∂ν := by
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  obtain ⟨P, hP, hPd, hPφ⟩ := exists_aeval_uActionCusp_laplacianU_eq_zero φ b ε B hε horth hsymm hinv hK
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian ν b P
    hP hPd Filter.univ_mem
  refine ⟨κ, ⟨hκs, hκc⟩, fun g => ?_⟩
  have h := hκ (sliceL g ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩)
    (aeval_laplacian_sliceL_eq_zero b P hPφ g) 1
  have e1 : ∀ x, ((sliceL g ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩ :
      (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) x =
        (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n x) := fun x => rfl
  simp only [e1, one_mul, map_one, mul_one] at h
  exact h

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_norm_le_of_mem_centralCuspForms hφ`. Establish `h1` using `isContRep_integrated_archRepT μ ν (isContRep_cuspToL2 μ φ) (C := C) (fun y => hC _) (hκ.continuous _) hκ.2`. Establish `hf : (fun y : normOneGL K n => ∫ a, κ a * (fun y : normOneGL K n => (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) (y * archP K n a) ∂ν) = fun y : normOneGL K n => (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)`. Use function extensionality and compare the values at `y`. Rewrite using `[hconv (y : AdelicGLn.AdelicGL K n)]`.

Use `integral_congr_ae (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Use `show κ a * (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * (archP K n a : _)) = _`. Rewrite using `[← apply_mul_infEmb_of_mem hφ, mul_comm]`. Rewrite `h1` using `[hf]`. Conclude with `eq_of_isContRep h1 (isContRep_cuspToL2 μ φ)`.
-/
theorem integrated_cuspToL2 {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n)
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {κ : archGroup K n → ℂ}
    (hκ : (isExpLieAlgebra K n).IsTestFunction κ)
    (hconv : ∀ g : AdelicGLn.AdelicGL K n, (φ : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ a, (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n a) * κ a ∂ν) :
    (archRepT μ).integrated ν κ (cuspVecL μ φ) = cuspVecL μ φ := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_centralCuspForms hφ
  have h1 := isContRep_integrated_archRepT μ ν (isContRep_cuspToL2 μ φ) (C := C) (fun y => hC _)
    (hκ.continuous _) hκ.2
  have hf : (fun y : normOneGL K n => ∫ a, κ a * (fun y : normOneGL K n =>
      (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) (y * archP K n a) ∂ν) =
      fun y : normOneGL K n => (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n) := by
    funext y
    rw [hconv (y : AdelicGLn.AdelicGL K n)]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show κ a * (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * (archP K n a : _)) = _
    rw [← apply_mul_infEmb_of_mem hφ, mul_comm]
  rw [hf] at h1
  exact eq_of_isContRep h1 (isContRep_cuspToL2 μ φ)

/- English proof (translation)
Take `⟨κ, hκ, hconv⟩` from `exists_kernel_cuspForm φ (Measure.haar : Measure (archGroup K n))`. Rewrite using `[← integrated_cuspToL2 μ hφ Measure.haar hκ hconv]`. Conclude with `(isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) Measure.haar hκ _`.
-/
theorem isSmoothVector_cuspToL2 {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) :
    (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) (cuspVecL μ φ) := by
  obtain ⟨κ, hκ, hconv⟩ := exists_kernel_cuspForm φ (Measure.haar : Measure (archGroup K n))
  rw [← integrated_cuspToL2 μ hφ Measure.haar hκ hconv]
  exact (isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) Measure.haar hκ _

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `set ν : Measure (archGroup K n) := Measure.haar`. Take `⟨κ, hκ, hconv⟩` from `exists_kernel_cuspForm φ ν`. Take `⟨γ, hγ, hvec, hfun⟩` from `(isExpLieAlgebra K n).exists_uAction_integrated ν (archRepT μ) u hκ`. Establish `hw` using `integrated_cuspToL2 μ hφ ν hκ hconv`. Establish `e : (⟨cuspVecL μ φ, isSmoothVector_cuspToL2 μ hφ⟩ : (isExpLieAlgebra K n).smoothVectors (archRepT μ)) = ⟨(archRepT μ).integrated ν κ (cuspVecL μ φ), (isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) ν hκ _⟩` using `Subtype.ext hw.symm`.

Rewrite using `[e, hvec]`. Take `⟨C, hC⟩` from `exists_norm_le_of_mem_centralCuspForms hφ`. Establish `h1` using `isContRep_integrated_archRepT μ ν (isContRep_cuspToL2 μ φ) (C := C) (fun y => hC _) (hγ.continuous _) hγ.2`. Use `eq_of_isContRep h1 ?_` and prove the remaining obligations. Establish `h2` using `isContRep_cuspToL2 μ (uActionCusp K n u φ)`.

Establish `hf : (fun y : normOneGL K n => ((uActionCusp K n u φ : cuspForms K n) : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) = fun y : normOneGL K n => ∫ a, γ a * (fun y : normOneGL K n => (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) (y * archP K n a) ∂ν`. Use function extensionality and compare the values at `y`. Use `set Ψ : archGroup K n → ℂ := fun x => (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * infEmb K n x) with hΨ`. Establish `hΨc : Continuous Ψ` using `φ.2.1.continuous.comp (continuous_const.mul continuous_infEmb)`. Establish `es : sliceL (y : AdelicGLn.AdelicGL K n) ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩ = ⟨fun x => ∫ a, Ψ (x * a) * κ a ∂ν, (isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨc hκ⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * infEmb K n x) = _`. Rewrite using `[hconv]`. Use `integral_congr_ae (Eventually.of_forall fun a => ?_)` and prove the remaining obligations.

Simplify using `only [hΨ, map_mul, mul_assoc]`. Rewrite using `[coe_uActionCusp, coe_uAction]`. Use `show ((isExpLieAlgebra K n).rightUAction u (sliceL (y : AdelicGLn.AdelicGL K n) ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩) : archGroup K n → ℂ) 1 = _`. Rewrite using `[es, hfun Ψ hΨc]`. Simplify using `only [one_mul]`.

Use `integral_congr_ae (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Use `show Ψ a * γ a = γ a * (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * (archP K n a : AdelicGLn.AdelicGL K n))`. Simplify using `only [hΨ]`. Rewrite using `[apply_mul_infEmb_of_mem hφ, mul_comm]`. Rewrite `h2` using `[hf]`.

Conclude with `h2`.
-/
theorem uAction_cuspToL2 {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) (u : UEnv K n) :
    ((isExpLieAlgebra K n).uAction (archRepT μ) u
        ⟨cuspVecL μ φ, isSmoothVector_cuspToL2 μ hφ⟩ : CuspL2 μ) =
      cuspVecL μ (uActionCusp K n u φ) := by
  set ν : Measure (archGroup K n) := Measure.haar
  obtain ⟨κ, hκ, hconv⟩ := exists_kernel_cuspForm φ ν
  obtain ⟨γ, hγ, hvec, hfun⟩ := (isExpLieAlgebra K n).exists_uAction_integrated ν (archRepT μ) u hκ
  have hw := integrated_cuspToL2 μ hφ ν hκ hconv
  have e : (⟨cuspVecL μ φ, isSmoothVector_cuspToL2 μ hφ⟩ :
      (isExpLieAlgebra K n).smoothVectors (archRepT μ)) =
      ⟨(archRepT μ).integrated ν κ (cuspVecL μ φ),
        (isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) ν hκ _⟩ := Subtype.ext hw.symm
  rw [e, hvec]
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_centralCuspForms hφ
  have h1 := isContRep_integrated_archRepT μ ν (isContRep_cuspToL2 μ φ) (C := C) (fun y => hC _)
    (hγ.continuous _) hγ.2
  refine eq_of_isContRep h1 ?_
  have h2 := isContRep_cuspToL2 μ (uActionCusp K n u φ)
  have hf : (fun y : normOneGL K n => ((uActionCusp K n u φ : cuspForms K n) :
      AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) =
      fun y : normOneGL K n => ∫ a, γ a * (fun y : normOneGL K n =>
        (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) (y * archP K n a) ∂ν := by
    funext y
    set Ψ : archGroup K n → ℂ := fun x => (φ : AdelicGLn.AdelicGL K n → ℂ)
      ((y : AdelicGLn.AdelicGL K n) * infEmb K n x) with hΨ
    have hΨc : Continuous Ψ :=
      φ.2.1.continuous.comp (continuous_const.mul continuous_infEmb)
    have es : sliceL (y : AdelicGLn.AdelicGL K n) ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩ =
        ⟨fun x => ∫ a, Ψ (x * a) * κ a ∂ν,
          (isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨc hκ⟩ := by
      apply Subtype.ext
      funext x
      show (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * infEmb K n x) = _
      rw [hconv]
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      simp only [hΨ, map_mul, mul_assoc]
    rw [coe_uActionCusp, coe_uAction]
    show ((isExpLieAlgebra K n).rightUAction u (sliceL (y : AdelicGLn.AdelicGL K n)
      ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩) : archGroup K n → ℂ) 1 = _
    rw [es, hfun Ψ hΨc]
    simp only [one_mul]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show Ψ a * γ a = γ a * (φ : AdelicGLn.AdelicGL K n → ℂ)
      ((y : AdelicGLn.AdelicGL K n) * (archP K n a : AdelicGLn.AdelicGL K n))
    simp only [hΨ]
    rw [apply_mul_infEmb_of_mem hφ, mul_comm]
  rw [hf] at h2
  exact h2

/- English proof (translation)
Use `ext1`. Rewrite using `[coe_toOne, coe_retractOne]`.
-/
theorem toOne_eq_retractOne (g : AdelicGLn.AdelicGL K n) : toOne g = retractOne g := by
  ext1
  rw [coe_toOne, coe_retractOne]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Use `cuspFormLp_rightTranslate_eq_rep μ hφ (infEmb K n k) (ψ := (gkModuleCusp K n).σ k φ) rfl` as an intermediate fact. Rewrite `this` using `[toOne_eq_retractOne, retract_infEmb]`. Rewrite using `[archRepT_apply]`. Apply `toLp_injective μ` to reduce the goal to its premises. Rewrite using `[toLp_cuspRepT, toLp_cuspVecL, toLp_cuspVecL, RightCosetSpace.rightRegularRep_apply]`.

Establish `h2` using `congrArg Subtype.val this`. Rewrite `h2` using `[coe_cuspRep_apply]`. Conclude with `h2`.
-/
theorem cuspToL2_sigma (k : archCompact K n) {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) :
    cuspVecL μ ((gkModuleCusp K n).σ k φ) =
      archRepT μ (k : archGroup K n) (cuspVecL μ φ) := by
  have := cuspFormLp_rightTranslate_eq_rep μ hφ (infEmb K n k) (ψ := (gkModuleCusp K n).σ k φ) rfl
  rw [toOne_eq_retractOne, retract_infEmb] at this
  rw [archRepT_apply]
  apply toLp_injective μ
  rw [toLp_cuspRepT, toLp_cuspVecL, toLp_cuspVecL, RightCosetSpace.rightRegularRep_apply]
  have h2 := congrArg Subtype.val this
  rw [coe_cuspRep_apply] at h2
  exact h2

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Use `cuspFormLp_rightTranslate_eq_rep μ hφ (finEmb K n h) (ψ := finRepCusp K n h φ) rfl` as an intermediate fact. Rewrite `this` using `[toOne_eq_retractOne]`. Apply `toLp_injective μ` to reduce the goal to its premises. Rewrite using `[toLp_cuspRepT, toLp_cuspVecL, toLp_cuspVecL, RightCosetSpace.rightRegularRep_apply]`. Establish `h2` using `congrArg Subtype.val this`.

Rewrite `h2` using `[coe_cuspRep_apply]`. Conclude with `h2`.
-/
theorem cuspToL2_finRepCusp (h : AdelicGLn.FiniteAdelicGL K n) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) :
    cuspVecL μ (finRepCusp K n h φ) =
      cuspRepT μ (retractOne (finEmb K n h)) (cuspVecL μ φ) := by
  have := cuspFormLp_rightTranslate_eq_rep μ hφ (finEmb K n h) (ψ := finRepCusp K n h φ) rfl
  rw [toOne_eq_retractOne] at this
  apply toLp_injective μ
  rw [toLp_cuspRepT, toLp_cuspVecL, toLp_cuspVecL, RightCosetSpace.rightRegularRep_apply]
  have h2 := congrArg Subtype.val this
  rw [coe_cuspRep_apply] at h2
  exact h2

end CuspidalSpectrum

end

end GroundTheory.Automorphic
