import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaDensityScale

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c' = c := by
  obtain ⟨l, hl, ht⟩ := h
  obtain ⟨l', hl', ht'⟩ := h'
  have e : l = l' := GlobalTheory.OmegaLebUnique.omegaLeb_unique P Q l l' hl hl'
  subst e
  exact tendsto_nhds_unique ht' ht

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal}
    (h : OmegaDensity μ c) (a : NNReal) : OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  obtain ⟨l, hl, ht⟩ := h
  refine ⟨l, hl, ?_⟩
  have h2 := ENNReal.Tendsto.const_mul (a := (a : ENNReal)) ht (Or.inr ENNReal.coe_ne_top)
  refine h2.congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem omegaDensity_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal),
    OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧
      ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) :=
  fun _ _ _ _ h => ⟨fun _ h' => omegaDensity_unique h h', fun a => omegaDensity_smul h a⟩

end GlobalTheory.OmegaDensityScale
