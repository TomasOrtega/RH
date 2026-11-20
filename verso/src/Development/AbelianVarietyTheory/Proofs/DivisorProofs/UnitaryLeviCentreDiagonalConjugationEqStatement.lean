import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviCentreDiagonalConjugationEq
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryLeviCentreDiagonalConjugationEq.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq : GlobalTheory.SatakeWeyl.TorusConj := by
  first | exact @GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | exact GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | (intros; apply GlobalTheory.SatakeWeyl.TorusConjProof.torusConj <;> assumption)
