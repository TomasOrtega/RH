import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.SplTApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField Topology
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] : R ⊗[F] E ≃ₗ[R] (Fin d → R) :=
  (Algebra.TensorProduct.basis R b).equivFun

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => funext i`. Simplify using the standard rewrite rules. Consider the case `tmul a e`. Use function extensionality and compare the values at `i`.

Simplify using `[crd, tensMap, Algebra.TensorProduct.basis_repr_tmul, map_mul, AlgHom.commutes]`. Consider the case `add x y hx hy`. Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun hx i`. Establish `h2` using `congrFun hy i`.

Simplify using `only [map_add, Pi.add_apply] at h1 h2 ⊢`. Rewrite using `[h1, h2]`.
-/
theorem crd_tensMap {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (x : R ⊗[F] E) : crd b R' (tensMap φ x) = fun i => φ (crd b R x i) := by
  induction x using TensorProduct.induction_on with
  | zero => funext i; simp
  | tmul a e =>
    funext i
    simp [crd, tensMap, Algebra.TensorProduct.basis_repr_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    funext i
    have h1 := congrFun hx i
    have h2 := congrFun hy i
    simp only [map_add, Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2]

variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def crdH : R ⊗[F] E ≃ₜ (Fin d → R) where
  toEquiv := (crd b R).toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (crd b R).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (crd b R).symm.toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem crdH_apply (x : R ⊗[F] E) : crdH b R x = crd b R x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem crdH_symm_apply (c : Fin d → R) : (crdH b R).symm c = (crd b R).symm c := rfl

/- English proof (translation)
Establish `h : (tensMap (E` using `E) φ : R ⊗[F] E → R' ⊗[F] E) = (crdH (Module.finBasis F E) R').symm ∘ (fun c i => φ (c i)) ∘ crdH (Module.finBasis F E) R := by`. Use function extensionality and compare the values at `x`. Apply `(crdH (Module.finBasis F E) R').injective` to reduce the goal to its premises. Simplify using `only [Function.comp_apply, Homeomorph.apply_symm_apply, crdH_apply]`. Conclude with `crd_tensMap (Module.finBasis F E) φ x`.

Rewrite using `[h]`. Conclude with `(crdH (Module.finBasis F E) R').symm.continuous.comp ((continuous_pi fun i => hφ.comp (continuous_apply i)).comp (crdH (Module.finBasis F E) R).continuous)`.
-/
theorem continuous_tensMap {R' : Type} [CommRing R'] [Algebra F R'] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) :
    Continuous (tensMap (E := E) φ) := by
  have h : (tensMap (E := E) φ : R ⊗[F] E → R' ⊗[F] E) =
      (crdH (Module.finBasis F E) R').symm ∘ (fun c i => φ (c i)) ∘ crdH (Module.finBasis F E) R := by
    funext x
    apply (crdH (Module.finBasis F E) R').injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply, crdH_apply]
    exact crd_tensMap (Module.finBasis F E) φ x
  rw [h]
  exact (crdH (Module.finBasis F E) R').symm.continuous.comp
    ((continuous_pi fun i => hφ.comp (continuous_apply i)).comp (crdH (Module.finBasis F E) R).continuous)

end Coord

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

/- English proof (translation)
The claim follows from `continuous_fst`.
-/
theorem continuous_fstA : Continuous (fstA F) := continuous_fst

/- English proof (translation)
The claim follows from `continuous_snd`.
-/
theorem continuous_sndA : Continuous (sndA F) := continuous_snd

def splInv (y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E)) : AF F ⊗[F] E :=
  (crd (Module.finBasis F E) (AF F)).symm
    (fun i => ((crd (Module.finBasis F E) (Ainf F) y.1 i, crd (Module.finBasis F E) (Af F) y.2 i) : AF F))

/- English proof (translation)
Rewrite using `[splT_apply, crd_tensMap, crd_tensMap]`. Both sides reduce to the same expression.
-/
theorem crd_AF (x : AF F ⊗[F] E) (i : Fin (Module.finrank F E)) :
    crd (Module.finBasis F E) (AF F) x i =
      ((crd (Module.finBasis F E) (Ainf F) (splT x).1 i, crd (Module.finBasis F E) (Af F) (splT x).2 i) : AF F) := by
  rw [splT_apply, crd_tensMap, crd_tensMap]
  rfl

/- English proof (translation)
The claim follows from `LinearEquiv.apply_symm_apply _ _`.
-/
theorem crd_splInv (y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E)) :
    crd (Module.finBasis F E) (AF F) (splInv y) =
      fun i => ((crd (Module.finBasis F E) (Ainf F) y.1 i, crd (Module.finBasis F E) (Af F) y.2 i) : AF F) :=
  LinearEquiv.apply_symm_apply _ _

/- English proof (translation)
Take `⟨y₁, y₂⟩` from `y`. Rewrite using `[splT_apply]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Apply `(crd (Module.finBasis F E) (Ainf F)).injective` to reduce the goal to its premises. Rewrite using `[crd_tensMap, crd_splInv]`.

Both sides reduce to the same expression. Apply `(crd (Module.finBasis F E) (Af F)).injective` to reduce the goal to its premises. Rewrite using `[crd_tensMap, crd_splInv]`. Both sides reduce to the same expression.
-/
theorem splT_splInv (y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E)) : splT (splInv y) = y := by
  obtain ⟨y₁, y₂⟩ := y
  rw [splT_apply]
  refine Prod.ext ?_ ?_
  · apply (crd (Module.finBasis F E) (Ainf F)).injective
    rw [crd_tensMap, crd_splInv]
    rfl
  · apply (crd (Module.finBasis F E) (Af F)).injective
    rw [crd_tensMap, crd_splInv]
    rfl

/- English proof (translation)
Apply `(crd (Module.finBasis F E) (AF F)).injective` to reduce the goal to its premises. Rewrite using `[crd_splInv]`. Use function extensionality and compare the values at `i`. Conclude with `(crd_AF x i).symm`.
-/
theorem splInv_splT (x : AF F ⊗[F] E) : splInv (splT x) = x := by
  apply (crd (Module.finBasis F E) (AF F)).injective
  rw [crd_splInv]
  funext i
  exact (crd_AF x i).symm

def splR : AF F ⊗[F] E ≃+* (Ainf F ⊗[F] E) × (Af F ⊗[F] E) where
  toFun := splT
  invFun := splInv
  left_inv := splInv_splT
  right_inv := splT_splInv
  map_mul' := map_mul splT
  map_add' := map_add splT

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splR_apply (x : AF F ⊗[F] E) : splR x = splT x := rfl

/- English proof (translation)
The claim follows from `splR.bijective`.
-/
theorem splT_bijective : Function.Bijective (splT (F := F) (E := E)) := splR.bijective

/- English proof (translation)
Use `show Continuous fun x => (tensMap (E := E) (fstA F) x, tensMap (E := E) (sndA F) x)`. Conclude with `(continuous_tensMap (AF F) _ continuous_fstA).prodMk (continuous_tensMap (AF F) _ continuous_sndA)`.
-/
theorem continuous_splT : Continuous (splT (F := F) (E := E)) := by
  show Continuous fun x => (tensMap (E := E) (fstA F) x, tensMap (E := E) (sndA F) x)
  exact (continuous_tensMap (AF F) _ continuous_fstA).prodMk
    (continuous_tensMap (AF F) _ continuous_sndA)

/- English proof (translation)
Establish `h : (splInv (F` using `F) (E := E)) = (crdH (Module.finBasis F E) (AF F)).symm ∘ (fun y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E) => fun i => ((crdH (Module.finBasis F E) (Ainf F) y.1 i, crdH (Module.finBasis F E) (Af F) y.2 i) : AF F)) := by`. Use function extensionality and compare the values at `y`. Both sides reduce to the same expression. Rewrite using `[h]`. Use `(crdH (Module.finBasis F E) (AF F)).symm.continuous.comp (continuous_pi fun i => ?_)` and prove the remaining obligations.

Conclude with `((continuous_apply i).comp ((crdH _ (Ainf F)).continuous.comp continuous_fst)).prodMk ((continuous_apply i).comp ((crdH _ (Af F)).continuous.comp continuous_snd))`.
-/
theorem continuous_splInv : Continuous (splInv (F := F) (E := E)) := by
  have h : (splInv (F := F) (E := E)) = (crdH (Module.finBasis F E) (AF F)).symm ∘
      (fun y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E) => fun i =>
        ((crdH (Module.finBasis F E) (Ainf F) y.1 i, crdH (Module.finBasis F E) (Af F) y.2 i) : AF F)) := by
    funext y
    rfl
  rw [h]
  refine (crdH (Module.finBasis F E) (AF F)).symm.continuous.comp (continuous_pi fun i => ?_)
  exact ((continuous_apply i).comp ((crdH _ (Ainf F)).continuous.comp continuous_fst)).prodMk
    ((continuous_apply i).comp ((crdH _ (Af F)).continuous.comp continuous_snd))

def splH : AF F ⊗[F] E ≃ₜ (Ainf F ⊗[F] E) × (Af F ⊗[F] E) where
  toEquiv := splR.toEquiv
  continuous_toFun := continuous_splT
  continuous_invFun := continuous_splInv

end Split

end PI.UnitaryGroupMassFormula.MeasWCore
