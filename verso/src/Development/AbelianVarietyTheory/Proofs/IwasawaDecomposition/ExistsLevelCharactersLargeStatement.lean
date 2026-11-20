import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelCharactersLarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.LevelPrime.exists_levCh_gt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLevelCharactersLarge.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_level_characters_large : ∀ (P : PreCh) (N : ℕ), ∃ L : LevCh P, ∀ u, N < L.T u := by
  first | exact @GlobalTheory.Mem.LevelPrime.exists_levCh_gt | exact GlobalTheory.Mem.LevelPrime.exists_levCh_gt | (intros; apply GlobalTheory.Mem.LevelPrime.exists_levCh_gt <;> assumption)
