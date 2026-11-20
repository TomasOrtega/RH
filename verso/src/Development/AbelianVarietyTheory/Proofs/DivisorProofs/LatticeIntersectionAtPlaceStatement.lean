import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntersectionAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeIntersectionAtPlace.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.lattice_intersection_at_place : LatIoAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.latIoAt | exact GlobalTheory.BigOn.Exp.SerBase.latIoAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.latIoAt <;> assumption)
