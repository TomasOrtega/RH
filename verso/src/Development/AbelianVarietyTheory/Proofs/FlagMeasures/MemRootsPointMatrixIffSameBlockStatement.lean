import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlock
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMemRootsPointMatrixIffSameBlock.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.mem_roots_point_matrix_iff_same_block : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n), (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  first | exact @GlobalTheory.roots_ptMat_iff | exact GlobalTheory.roots_ptMat_iff | (intros; apply GlobalTheory.roots_ptMat_iff <;> assumption)
