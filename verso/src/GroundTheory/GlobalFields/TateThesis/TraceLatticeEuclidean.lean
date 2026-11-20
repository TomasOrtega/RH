import Mathlib
import GroundTheory.GlobalFields.TateThesis.TraceDualLattice
import GroundTheory.GlobalFields.TateThesis.LatticePoissonBasic

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K I) (mixedToEuclidean K).symm.toLinearMap

abbrev euclideanConjIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K I) (mixedToEuclideanConj K).symm.toLinearMap

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : euclidean.mixedSpace K) :
    u ∈ euclideanIdealLattice K I ↔ (mixedToEuclidean K).symm u ∈ idealLattice K I := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_euclideanConjIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : euclidean.mixedSpace K) :
    u ∈ euclideanConjIdealLattice K I ↔ (mixedToEuclideanConj K).symm u ∈ idealLattice K I :=
  Iff.rfl

/- English proof (translation)
Establish `: MeasurePreserving (mixedToEuclidean K).toHomeomorph.toMeasurableEquiv (selfDualMeasure K) volume` using `measurePreserving_mixedToEuclidean K`. Conclude with `this.symm`.
-/
theorem measurePreserving_mixedToEuclidean_symm :
    MeasurePreserving (mixedToEuclidean K).symm volume (selfDualMeasure K) := by
  have : MeasurePreserving (mixedToEuclidean K).toHomeomorph.toMeasurableEquiv
      (selfDualMeasure K) volume := measurePreserving_mixedToEuclidean K
  exact this.symm

/- English proof (translation)
Rewrite using `[ZLattice.covolume_comap (idealLattice K I) (selfDualMeasure K) volume (measurePreserving_mixedToEuclidean_symm K), covolume_idealLattice_selfDualMeasure]`.
-/
theorem covolume_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclideanIdealLattice K I) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)| := by
  rw [ZLattice.covolume_comap (idealLattice K I) (selfDualMeasure K) volume
    (measurePreserving_mixedToEuclidean_symm K), covolume_idealLattice_selfDualMeasure]

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[mem_dualLattice, mem_euclideanConjIdealLattice, mem_idealLattice_traceDualIdeal_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Take `⟨k, hk⟩` from `h (mixedToEuclidean K x) (by`.

Rewrite using `[mem_euclideanIdealLattice, ContinuousLinearEquiv.symm_apply_apply]`. Conclude with `hx)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[mixedTraceForm_comm, mixedTraceForm_eq_inner, ContinuousLinearEquiv.apply_symm_apply, real_inner_comm]`. Conclude with `hk`.

Introduce `h ℓ hℓ`. Take `⟨k, hk⟩` from `h ((mixedToEuclidean K).symm ℓ) hℓ`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, mixedTraceForm_comm, mixedTraceForm_eq_inner, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply, real_inner_comm]`.
-/
theorem dualLattice_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclideanIdealLattice K I) =
      euclideanConjIdealLattice K (traceDualIdeal K I) := by
  ext μ
  rw [mem_dualLattice, mem_euclideanConjIdealLattice, mem_idealLattice_traceDualIdeal_iff]
  constructor
  · intro h x hx
    obtain ⟨k, hk⟩ := h (mixedToEuclidean K x) (by
      rw [mem_euclideanIdealLattice, ContinuousLinearEquiv.symm_apply_apply]
      exact hx)
    refine ⟨k, ?_⟩
    rw [mixedTraceForm_comm, mixedTraceForm_eq_inner, ContinuousLinearEquiv.apply_symm_apply,
      real_inner_comm]
    exact hk
  · intro h ℓ hℓ
    obtain ⟨k, hk⟩ := h ((mixedToEuclidean K).symm ℓ) hℓ
    refine ⟨k, ?_⟩
    rw [← hk, mixedTraceForm_comm, mixedTraceForm_eq_inner, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, real_inner_comm]

/- English proof (translation)
Rewrite using `[real_inner_comm, ← mixedTraceForm_eq_inner, mixedTraceForm_comm]`.
-/
theorem inner_mixedToEuclideanConj_mixedToEuclidean (β a : mixedSpace K) :
    ⟪mixedToEuclideanConj K β, mixedToEuclidean K a⟫ = mixedTraceForm K β a := by
  rw [real_inner_comm, ← mixedTraceForm_eq_inner, mixedTraceForm_comm]

end

end GroundTheory.Global
