import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullRankLatticeImageStandardLatticeGL
import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatOrb.matLat_stdLat_isLatV` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFullRankLatticeImageStandardLatticeGL.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.isFullRankLattice_image_standardLattice_GL : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.matLat_stdLat_isLatV | exact GlobalTheory.LatOrb.matLat_stdLat_isLatV | (intros; apply GlobalTheory.LatOrb.matLat_stdLat_isLatV <;> assumption)
