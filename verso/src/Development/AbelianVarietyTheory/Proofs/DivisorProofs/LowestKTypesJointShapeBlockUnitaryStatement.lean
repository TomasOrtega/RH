import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLowestKTypesJointShapeBlockUnitary.lean&line=360#L360)
-/
theorem _root_.GlobalTheory.T.lowest_kTypes_jointShape_block_unitary : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamA' t al be ga de)) ∧ IsParam (lamA al be ga de) ∧ IsParam (lamA' t al be ga de) ∧ (∀ a, (0 < lamA al be ga de a → 0 ≤ shiftNu (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) a) ∧ (lamA al be ga de a < 0 → shiftNu (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) a ≤ 0)) ∧ (∀ c, ((t : ℚ) / 2 < lamA' t al be ga de c → 0 ≤ shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) c) ∧ (lamA' t al be ga de c ≤ (t : ℚ) / 2 → shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) c ≤ 0)) := by
  first | exact @GlobalTheory.LowestTypes.lowest_types | exact GlobalTheory.LowestTypes.lowest_types | (intros; apply GlobalTheory.LowestTypes.lowest_types <;> assumption)
