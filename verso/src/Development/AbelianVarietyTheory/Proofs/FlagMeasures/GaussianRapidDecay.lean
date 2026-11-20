import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisRest
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussDecay

/- English proof (translation)
Take `⟨hF, hE, h2, -⟩` from `h`. Unfold `GlobalTheory.Mem.Vol.IsCMFam`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Prove the components needed by the constructor for the conclusion. Establish `key : ∀ v, (InfinitePlace.mk (φ v)).comap (algebraMap F E) = v`.

Introduce `v`. Rewrite using `[InfinitePlace.comap_mk, show (φ v).comp (algebraMap F E) = v.embedding from RingHom.ext (hφ v), InfinitePlace.mk_embedding]`. Introduce `v w hvw`. Rewrite using `[← key v, ← key w]`. Conclude with `congrArg (fun x : InfinitePlace E => x.comap (algebraMap F E)) hvw`.

Establish `a1` using `IsTotallyComplex.finrank E`. Establish `a2` using `IsTotallyReal.finrank F`. Establish `a3` using `Module.finrank_mul_finrank ℚ F E`. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, IsTotallyComplex.nrRealPlaces_eq_zero E]`. Rewrite `a3` using `[h2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem isCMFam_of_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : GlobalTheory.Mem.Vol.IsCMFam φ := by
  obtain ⟨hF, hE, h2, -⟩ := h
  unfold GlobalTheory.Mem.Vol.IsCMFam
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · have key : ∀ v, (InfinitePlace.mk (φ v)).comap (algebraMap F E) = v := by
      intro v
      rw [InfinitePlace.comap_mk, show (φ v).comp (algebraMap F E) = v.embedding from RingHom.ext (hφ v),
        InfinitePlace.mk_embedding]
    intro v w hvw
    rw [← key v, ← key w]
    exact congrArg (fun x : InfinitePlace E => x.comap (algebraMap F E)) hvw
  · have a1 := IsTotallyComplex.finrank E
    have a2 := IsTotallyReal.finrank F
    have a3 := Module.finrank_mul_finrank ℚ F E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [h2] at a3
    omega

end GlobalTheory.GaussDecay
