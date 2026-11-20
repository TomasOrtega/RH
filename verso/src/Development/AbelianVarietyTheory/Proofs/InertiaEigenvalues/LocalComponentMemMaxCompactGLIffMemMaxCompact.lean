import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocInteg

/- English proof (translation)
Proceed by induction on `hz using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨y, rfl⟩ | ⟨a, ha, rfl⟩` into its components or cases. Rewrite using `[F.left]`. Conclude with `GlobalTheory.AdeleBaseChange.algebraMap_int_mem y w`.

Establish `h` using `GlobalTheory.UnramDict.kappa_tmul F 1 a`. Rewrite `h` using `[map_one, one_mul]`. Express the relevant statement in the definitionally equal form `F.κ.toRingHom _ w ∈ _`. Rewrite using `[h]`. Conclude with `GlobalTheory.AdeleBaseChange.adMap_int ha w`.

Consider the case `one => rw [map_one]`. Conclude with `one_mem _`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [map_neg]`. Conclude with `neg_mem ha`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
theorem kappa_mem_int {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (F : FinIso L n)
    (w : HeightOneSpectrum (𝓞 L)) {z : AL L} (hz : z ∈ ALint L) : F.κ z w ∈ w.adicCompletionIntegers L := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨a, ha, rfl⟩
    · rw [F.left]
      exact GlobalTheory.AdeleBaseChange.algebraMap_int_mem y w
    · have h := GlobalTheory.UnramDict.kappa_tmul F 1 a
      rw [map_one, one_mul] at h
      change F.κ.toRingHom _ w ∈ _
      rw [h]
      exact GlobalTheory.AdeleBaseChange.adMap_int ha w
  | one => rw [map_one]; exact one_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/- English proof (translation)
Introduce `L _ _ _ n F w y hy`. Prove the components needed by the constructor for the conclusion. Introduce `hK i j`. Conclude with `GlobalTheory.UnramDict.mem_ALint F _ fun u => by`. Rewrite using `[← F.loc]`.

Conclude with `GlobalTheory.UnramDict.cLoc_entry_mem hy hK u i j`. Introduce `hyU`. Use `GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[F.loc]`. Conclude with `kappa_mem_int F w (hyU i j)`.

Rewrite using `[← map_inv, ← map_inv, F.loc]`. Conclude with `kappa_mem_int F w ((inv_mem hyU : y⁻¹ ∈ Umax L n) i j)`.
-/
theorem cLoc_mem_KGL_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (w : HeightOneSpectrum (𝓞 L)) (y : GAf L n), F.j y ∈ locU n w → (cLoc w (F.j y) ∈ GlobalTheory.LFun.KGL w n ↔ y ∈ Umax L n) := by
  intro L _ _ _ n F w y hy
  constructor
  · intro hK i j
    exact GlobalTheory.UnramDict.mem_ALint F _ fun u => by
      rw [← F.loc]
      exact GlobalTheory.UnramDict.cLoc_entry_mem hy hK u i j
  · intro hyU
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [F.loc]
      exact kappa_mem_int F w (hyU i j)
    · rw [← map_inv, ← map_inv, F.loc]
      exact kappa_mem_int F w ((inv_mem hyU : y⁻¹ ∈ Umax L n) i j)

end GlobalTheory.LocInteg

end
