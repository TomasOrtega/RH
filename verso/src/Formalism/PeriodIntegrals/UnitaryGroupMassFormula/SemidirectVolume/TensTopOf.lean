import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

noncomputable section

namespace PI.VolSemiDirect.W.Lc

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def AFTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)

/- English proof (translation)
The claim follows from `Module.Finite.of_restrictScalars_finite ℚ F E`.
-/
theorem finite_nf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Module.Finite F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

def sigL {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) : R ⊗[F] E →ₗ[R] R ⊗[F] E where
  toFun := sigR R σ
  map_add' := fun x y => map_add _ x y
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, TensorProduct.smul_tmul']
    | add x y hx hy => simp_all [smul_add]

/- English proof (translation)
Introduce `F E _ _ _ _ _`. Take `⟨hlc, hsc, ht2⟩` from `h F`. Use `finite_nf F E` as an intermediate fact. Set `R` to `AF F`. Establish `: IsModuleTopology R (R ⊗[F] E)` using `⟨rfl⟩`.

Set `b` to `Module.finBasis F E`. Set `bR` to `Algebra.TensorProduct.basis R b`. Set `e : (R ⊗[F] E) ≃ₗ[R] (Fin (Module.finrank F E) → R)` to `bR.equivFun`. Establish `htr : IsTopologicalRing (R ⊗[F] E)` using `IsModuleTopology.isTopologicalRing R (R ⊗[F] E)`. Establish `c1 : Continuous e.toLinearMap` using `IsModuleTopology.continuous_of_linearMap (R := R) _`.

Establish `c2 : Continuous e.symm.toLinearMap` using `IsModuleTopology.continuous_of_linearMap (R := R) _`. Set `hm : (R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R)` to `{ toEquiv := e.toEquiv, continuous_toFun := by simpa using c1, continuous_invFun := by simpa using c2 }`. Use `⟨htr, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hm.isEmbedding.t2Space`. Conclude with `hm.isClosedEmbedding.locallyCompactSpace`.

Conclude with `hm.isEmbedding.secondCountableTopology`.
-/
theorem tensTop_of (h : AFTop) : TensTop := by
  intro F E _ _ _ _ _
  obtain ⟨hlc, hsc, ht2⟩ := h F
  have := finite_nf F E
  let R := AF F
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let bR := Algebra.TensorProduct.basis R b
  let e : (R ⊗[F] E) ≃ₗ[R] (Fin (Module.finrank F E) → R) := bR.equivFun
  have htr : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  have c2 : Continuous e.symm.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  let hm : (R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R) :=
    { toEquiv := e.toEquiv, continuous_toFun := by simpa using c1, continuous_invFun := by simpa using c2 }
  refine ⟨htr, ?_, ?_, ?_⟩
  · exact hm.isEmbedding.t2Space
  · exact hm.isClosedEmbedding.locallyCompactSpace
  · exact hm.isEmbedding.secondCountableTopology

end PI.VolSemiDirect.W.Lc
