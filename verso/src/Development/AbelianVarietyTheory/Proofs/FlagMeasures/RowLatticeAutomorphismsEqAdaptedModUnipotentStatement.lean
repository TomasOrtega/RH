import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeAutomorphismsEqAdaptedModUnipotent
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRowLatticeAutomorphismsEqAdaptedModUnipotent.lean&line=407#L407)
-/
theorem _root_.GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u, ∃ A N : Subgroup (GV D), (A : Set (GV D)) = Aut0 (lf D (X.Fu u)) Λ ∧ (N : Set (GV D)) = NLam Λ (lf D (X.Fu u)) ∧ N ≤ A ∧ (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) ∧ N.relIndex A = Nat.card (autLz D (X.Fu u) Λ) ∧ 0 < Nat.card (autLz D (X.Fu u) Λ) := by
  first | exact @GlobalTheory.AutQuot.autQuot | exact GlobalTheory.AutQuot.autQuot | (intros; apply GlobalTheory.AutQuot.autQuot <;> assumption)
