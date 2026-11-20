import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped nonZeroDivisors TensorProduct

namespace GlobalTheory.LocIdealMeas

open GlobalTheory.LocIdeal

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hx0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `h (FractionalIdeal.eq_zero_iff.2 hc)`. Establish `key : ∀ z ∈ intLoc F E v, (1 : Fv F v) ⊗ₜ[F] x * z ∈ locId v 𝔞` using `fun z hz => by`. Use `intLoc_induction (p := fun z => (1 : Fv F v) ⊗ₜ[F] x * z ∈ locId v 𝔞) (fun a ha o => ?_) ?_ ?_ ?_ hz` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `tmul_mem_locId ha ?_` and prove the remaining obligations.

Use `(𝔞 : Submodule (𝓞 E) E).smul_mem o (show x ∈ (𝔞 : Submodule (𝓞 E) E) from hx)` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def, mul_comm]`. Conclude with `this`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`.

Introduce `a b ha hb`. Rewrite using `[mul_add]`. Conclude with `add_mem ha hb`. Introduce `a ha`. Rewrite using `[mul_neg]`.

Conclude with `neg_mem ha`. Establish `hU : IsOpen ((fun z : Fv F v ⊗[F] E => (1 : Fv F v) ⊗ₜ[F] x⁻¹ * z) ⁻¹' (intLoc F E v : Set _))` using `(isCompact_isOpen_intLoc v).2.preimage (continuous_const_mul _)`. Use `AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (hU.mem_nhds ?_) fun z hz => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : Fv F v) ⊗ₜ[F] x⁻¹ * 0 ∈ intLoc F E v`. Rewrite using `[mul_zero]`.

Conclude with `zero_mem _`. Use `key _ hz` as an intermediate fact. Rewrite `this` using `[← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hx0, ← Algebra.TensorProduct.one_def, one_mul]`. Then use the resulting hypothesis.
-/
theorem isOpen_locId_of_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h : 𝔞 ≠ 0) : IsOpen (locId v 𝔞 : Set (Fv F v ⊗[F] E)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (FractionalIdeal.eq_zero_iff.2 hc)
  have key : ∀ z ∈ intLoc F E v, (1 : Fv F v) ⊗ₜ[F] x * z ∈ locId v 𝔞 := fun z hz => by
    refine intLoc_induction (p := fun z => (1 : Fv F v) ⊗ₜ[F] x * z ∈ locId v 𝔞) (fun a ha o => ?_) ?_ ?_ ?_ hz
    · rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      refine tmul_mem_locId ha ?_
      have := (𝔞 : Submodule (𝓞 E) E).smul_mem o (show x ∈ (𝔞 : Submodule (𝓞 E) E) from hx)
      rw [Algebra.smul_def, mul_comm] at this
      exact this
    · rw [mul_zero]; exact zero_mem _
    · intro a b ha hb
      rw [mul_add]; exact add_mem ha hb
    · intro a ha
      rw [mul_neg]; exact neg_mem ha
  have hU : IsOpen ((fun z : Fv F v ⊗[F] E => (1 : Fv F v) ⊗ₜ[F] x⁻¹ * z) ⁻¹' (intLoc F E v : Set _)) :=
    (isCompact_isOpen_intLoc v).2.preimage (continuous_const_mul _)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (hU.mem_nhds ?_) fun z hz => ?_)
  · change (1 : Fv F v) ⊗ₜ[F] x⁻¹ * 0 ∈ intLoc F E v
    rw [mul_zero]; exact zero_mem _
  · have := key _ hz
    rwa [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hx0,
      ← Algebra.TensorProduct.one_def, one_mul] at this

/- English proof (translation)
Introduce `F E _ _ _ _ _ 𝔞 h`. Use `haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩`. Use `haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F`. Simplify using `only [Set.setOf_forall]`. Use `MeasurableSet.iInter fun v => IsOpen.measurableSet ?_` and prove the remaining obligations.

Conclude with `(isOpen_locId_of_ne_zero v h).preimage (Units.continuous_val.comp (GlobalTheory.Doubling.continuous_unitFin v))`.
-/
theorem measurableSet_locId : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 →
    MeasurableSet {l : (AE F E)ˣ | ∀ v : Pl F, compFin F E v (l : AE F E) ∈ GlobalTheory.LocIdeal.locId v 𝔞} := by
  intro F E _ _ _ _ _ 𝔞 h
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun v => IsOpen.measurableSet ?_
  exact (isOpen_locId_of_ne_zero v h).preimage (Units.continuous_val.comp (GlobalTheory.Doubling.continuous_unitFin v))

end GlobalTheory.LocIdealMeas
