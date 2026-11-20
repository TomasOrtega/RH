import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem series_in_ideal_iff_image :
    ∀ (B Q σ : Type) [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) (f : MvPowerSeries σ Q),
      (In N f ↔ ∃ s : MvPowerSeries σ B, (∀ α, coeff α s ∈ N) ∧ map (algebraMap B Q) s = f) ∧
      ∀ g : MvPowerSeries σ Q, In N f → In N g → ∀ a : B,
        In N (f + algebraMap B Q a • g) ∧ In N (f - g) := by
  intro B Q σ _ _ _ N f
  refine ⟨⟨fun h => ?_, fun ⟨s, hs, hsf⟩ α => ?_⟩, fun g hf hg a => ⟨fun α => ?_, fun α => ?_⟩⟩
  · choose b hbN hb using h
    obtain ⟨s, hs⟩ : ∃ s : MvPowerSeries σ B, ∀ α, coeff α s = b α := ⟨b, fun _ => rfl⟩
    refine ⟨s, fun α => (hs α).symm ▸ hbN α, ?_⟩
    ext α
    rw [coeff_map, hs]
    exact (hb α).symm
  · exact ⟨coeff α s, hs α, by rw [← hsf, coeff_map]⟩
  · obtain ⟨b₁, hb₁N, hb₁⟩ := hf α
    obtain ⟨b₂, hb₂N, hb₂⟩ := hg α
    refine ⟨b₁ + a * b₂, N.add_mem hb₁N (N.mul_mem_left a hb₂N), ?_⟩
    rw [map_add, map_smul, smul_eq_mul, hb₁, hb₂, map_add, map_mul]
  · obtain ⟨b₁, hb₁N, hb₁⟩ := hf α
    obtain ⟨b₂, hb₂N, hb₂⟩ := hg α
    exact ⟨b₁ - b₂, N.sub_mem hb₁N hb₂N, by rw [map_sub, hb₁, hb₂, map_sub]⟩

end GlobalTheory
