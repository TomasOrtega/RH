import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisBrat

open scoped TensorProduct NumberField.AdeleRing
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ χ c _ _ _ _`. Use `⟨fun y => ?_, fun e x h => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(algebraMap F (AF F) y) ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] (algebraMap F E y)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Take `⟨g, hg⟩` from `(Algebra.linearMap F E).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F E))`.

Establish `g1 : g 1 = 1`. Use `LinearMap.congr_fun hg (1 : F)` as an intermediate fact. Simplify using `using this`. Establish `h' : (1 : AF F) ⊗ₜ[F] e = x ⊗ₜ[F] (1 : E)` using `h`. Establish `h2` using `congrArg (fun t => TensorProduct.rid F (AF F) (LinearMap.lTensor (AF F) g t)) h'`.

Simplify using `only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at h2`. Use `⟨g e, ?_⟩` and prove the remaining obligations. Rewrite using `[← h2, Algebra.algebraMap_eq_smul_one]`.
-/
theorem brat : BRat := by
  intro F E _ _ _ _ _ σ χ c _ _ _ _
  refine ⟨fun y => ?_, fun e x h => ?_⟩
  · change (algebraMap F (AF F) y) ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] (algebraMap F E y)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · obtain ⟨g, hg⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F E))
    have g1 : g 1 = 1 := by
      have := LinearMap.congr_fun hg (1 : F)
      simpa using this
    have h' : (1 : AF F) ⊗ₜ[F] e = x ⊗ₜ[F] (1 : E) := h
    have h2 := congrArg (fun t => TensorProduct.rid F (AF F) (LinearMap.lTensor (AF F) g t)) h'
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at h2
    refine ⟨g e, ?_⟩
    rw [← h2, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CompanionTheory.EisBrat
