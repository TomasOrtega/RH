import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FDefiniteUnitaryFinitePointsExistsOpenCompact.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ K : Subgroup (finU E n), IsOpen (K : Set (finU E n)) ∧ IsCompact (K : Set (finU E n)) := by
  first | exact @GlobalTheory.DefU.FinCompact.exists_open_compact | exact GlobalTheory.DefU.FinCompact.exists_open_compact | (intros; apply GlobalTheory.DefU.FinCompact.exists_open_compact <;> assumption)
