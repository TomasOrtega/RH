import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorRepresentationUnitaryCover
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OscGauss.exists_isOsc` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsOscillatorRepresentationUnitaryCover.lean&line=156#L156)
-/
theorem _root_.GlobalTheory.T.exists_oscillatorRepresentation_unitaryCover : ∀ (P Q : ℕ) (T0 : GrpData P Q) (F : Fock (Ix P Q)), ∃ Om : T0.G →* (F.H →L[ℂ] F.H), IsOsc T0 F Om := by
  first | exact @GlobalTheory.OscGauss.exists_isOsc | exact GlobalTheory.OscGauss.exists_isOsc | (intros; apply GlobalTheory.OscGauss.exists_isOsc <;> assumption)
