import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PlaceSum.sum_localDeg_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteSetResidueLogBound.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.exists_finite_set_residue_log_bound : ∀ {F : Type} [Field F] [NumberField F] (T : Finset ℕ), (∀ p ∈ T, p.Prime) → ∀ (g : ℕ → ℝ), (∀ p, 0 ≤ g p) →
    (∀ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (resP v : F) ≤ 1) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∈ S ↔ resP v ∈ T) ∧
      ∑ v ∈ S, (-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) * g (resP v) ≤
        (Module.finrank ℚ F : ℝ) * ∑ p ∈ T, g p := by
  first | exact @GlobalTheory.PlaceSum.sum_localDeg_le | exact GlobalTheory.PlaceSum.sum_localDeg_le | (intros; apply GlobalTheory.PlaceSum.sum_localDeg_le <;> assumption)
