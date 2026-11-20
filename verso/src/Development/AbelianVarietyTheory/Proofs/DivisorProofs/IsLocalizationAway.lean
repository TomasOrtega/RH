import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem IsFrame.isLocalization_away {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] {θ : B →+* O} (h : IsFrame p Q θ) : IsLocalization.Away (p : B) Q := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, k, rfl⟩
    simpa [map_pow, map_natCast] using h.unit_p.pow k
  · intro q
    obtain ⟨k, b, hb⟩ := h.denom q
    refine ⟨⟨b, ⟨(p : B) ^ k, k, rfl⟩⟩, ?_⟩
    simp only [map_pow, map_natCast]
    rw [← hb, mul_comm]
  · intro x y hxy
    exact ⟨1, by simpa using h.inj hxy⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem frame_fraction_map : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∃ Θ : Q →+* C, ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b) := by
  intro p _ B O Q _ _ _ _ θ hQ C _ _ hC
  haveI := hQ.isLocalization_away
  refine ⟨IsLocalization.Away.lift (p : B) (g := (algebraMap O C).comp θ) ?_, fun b => ?_⟩
  · simpa [map_natCast] using hC.unit_p
  · exact IsLocalization.Away.lift_eq (p : B) _ b

end GlobalTheory.QLog
