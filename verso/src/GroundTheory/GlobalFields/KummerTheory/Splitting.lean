import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain NumberField Module
open scoped TensorProduct

section Algebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hf e`. Establish `h0 : ∏ i, (y - algebraMap F (ι → F) (y i)) = 0`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.prod_apply]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ j) (by simp)`.

Establish `h1 : ∏ i, (f y - algebraMap F E (y i)) = 0`. Simplify `congrArg f h0` using `[map_prod, map_sub, AlgHom.commutes]`. Take `⟨i, -, hi⟩` from `Finset.prod_eq_zero_iff.mp h1`. Conclude with `⟨y i, (sub_eq_zero.mp hi).symm⟩`.
-/
theorem mem_range_algebraMap_of_surjective_pi {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) (e : E) :
    e ∈ Set.range (algebraMap F E) := by
  obtain ⟨y, rfl⟩ := hf e
  have h0 : ∏ i, (y - algebraMap F (ι → F) (y i)) = 0 := by
    funext j
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  have h1 : ∏ i, (f y - algebraMap F E (y i)) = 0 := by
    simpa [map_prod, map_sub, AlgHom.commutes] using congrArg f h0
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h1
  exact ⟨y i, (sub_eq_zero.mp hi).symm⟩

/- English proof (translation)
Rewrite using `[← Subalgebra.bot_eq_top_iff_finrank_eq_one]`. Conclude with `eq_top_iff.2 fun e _ ↦ Algebra.mem_bot.2 (mem_range_algebraMap_of_surjective_pi f hf e)`.
-/
theorem finrank_eq_one_of_surjective_pi {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) : finrank F E = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  exact eq_top_iff.2 fun e _ ↦ Algebra.mem_bot.2 (mem_range_algebraMap_of_surjective_pi f hf e)

def algEquivOfFinrankEqOne (h : finrank F E = 1) : F ≃ₐ[F] E :=
  AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i`. Take `⟨n, ⟨e⟩⟩` from `Algebra.IsFiniteSplit.nonempty_algEquiv_fun F (∀ i, E i)`. Use `finrank_eq_one_of_surjective_pi ((Pi.evalAlgHom F E i).comp e.symm.toAlgHom) ?_` and prove the remaining obligations. Conclude with `(Function.surjective_eval i).comp e.symm.surjective`.

Introduce `h`. Conclude with `.of_algEquiv (AlgEquiv.piCongrRight fun i ↦ algEquivOfFinrankEqOne (h i))`.
-/
theorem isFiniteSplit_pi_iff {ι : Type*} [Finite ι] {E : ι → Type*} [∀ i, Field (E i)]
    [∀ i, Algebra F (E i)] :
    Algebra.IsFiniteSplit F (∀ i, E i) ↔ ∀ i, finrank F (E i) = 1 := by
  constructor
  · intro h i
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun F (∀ i, E i)
    refine finrank_eq_one_of_surjective_pi ((Pi.evalAlgHom F E i).comp e.symm.toAlgHom) ?_
    exact (Function.surjective_eval i).comp e.symm.surjective
  · intro h
    exact .of_algEquiv (AlgEquiv.piCongrRight fun i ↦ algEquivOfFinrankEqOne (h i))

end Algebra

section Finite

open SemiLocal

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

def SplitsCompletely (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
    w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1

variable {L} (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h w`. Take `⟨h1, h2⟩` from `h w.1 w.2`. Rewrite using `[finrank_eq_ramificationIdx_mul_inertiaDeg L v w.1, h1, h2]`. Introduce `h w hw`.

Use `h ⟨w, hw⟩` as an intermediate fact. Rewrite `this` using `[finrank_eq_ramificationIdx_mul_inertiaDeg L v w]`. Conclude with `mul_eq_one.mp this`.
-/
theorem splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  constructor
  · intro h w
    obtain ⟨h1, h2⟩ := h w.1 w.2
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w.1, h1, h2]
  · intro h w hw
    have := h ⟨w, hw⟩
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w] at this
    exact mul_eq_one.mp this

/- English proof (translation)
Rewrite using `[splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]`. Conclude with `⟨fun h ↦ .of_algEquiv (tensorEquiv L v).symm, fun h ↦ .of_algEquiv (tensorEquiv L v)⟩`.
-/
theorem splitsCompletely_iff_isFiniteSplit :
    SplitsCompletely L v ↔
      Algebra.IsFiniteSplit (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) := by
  rw [splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]
  exact ⟨fun h ↦ .of_algEquiv (tensorEquiv L v).symm, fun h ↦ .of_algEquiv (tensorEquiv L v)⟩

variable (L) in

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Use `sum_finrank_eq L v` as an intermediate fact. Rewrite `this` using `[Finset.univ_eq_empty, Finset.sum_empty]`. Conclude with `(Module.finrank_pos (R := K) (M := L)).ne this`.
-/
theorem nonempty_placesOver : Nonempty (PlacesOver L v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_eq L v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

/- English proof (translation)
Take `⟨σ, hσ⟩` from `MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'`. Conclude with `(galEquiv v σ w.1 w'.1 (congrArg Subtype.val hσ.symm)).toLinearEquiv.finrank_eq`.
-/
theorem finrank_eq_of_isGalois [IsGalois K L] (w w' : PlacesOver L v) :
    finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      finrank (v.adicCompletion K) (w'.1.adicCompletion L) := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'
  exact (galEquiv v σ w.1 w'.1 (congrArg Subtype.val hσ.symm)).toLinearEquiv.finrank_eq

/- English proof (translation)
Rewrite using `[splitsCompletely_iff_forall_finrank]`. Use `⟨fun h ↦ ?_, fun ⟨w, hw⟩ w' ↦ (finrank_eq_of_isGalois v w w').symm.trans hw⟩` and prove the remaining obligations. Take `⟨w⟩` from `nonempty_placesOver L v`. Conclude with `⟨w, h w⟩`.
-/
theorem splitsCompletely_iff_exists_finrank [IsGalois K L] :
    SplitsCompletely L v ↔
      ∃ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  rw [splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun ⟨w, hw⟩ w' ↦ (finrank_eq_of_isGalois v w w').symm.trans hw⟩
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact ⟨w, h w⟩

end Finite

end GroundTheory.Global
