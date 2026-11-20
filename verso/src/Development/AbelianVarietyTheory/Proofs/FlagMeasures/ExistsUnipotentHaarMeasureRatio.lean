import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_isRatioN : ∀ (k r : ℕ), ∃ cN : ℝ, IsRatioN k r cN := by
  intro k r
  have h1 : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) 1) :=
    GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top
  have h2 : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (D.muN k r) :=
    ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r (D.muN k r)).2.1).2 (P.nilpotent_measure_is_haar k r)
  obtain ⟨c, c0, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (P.unipotent_radical_closed k r) h1 h2
  exact ⟨c.toReal, ENNReal.toReal_pos c0 c1, by rw [ENNReal.ofReal_toReal c1]; exact e⟩

end GlobalTheory.ThA
