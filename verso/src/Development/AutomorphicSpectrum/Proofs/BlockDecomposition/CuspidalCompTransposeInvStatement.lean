import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCompTransposeInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalCompTransposeInv.lean&line=152#L152)
-/
theorem _root_.GlobalTheory.T.cuspidal_comp_transposeInv : ∀ φ : G3 → ℂ, IsLeftInvariant φ → IsCuspidal φ → IsCuspidal (fun g : G3 => φ (ti g)) := by
  first | exact @GlobalTheory.CompanionTheory.TiCusp.isCuspidal_comp_ti | exact GlobalTheory.CompanionTheory.TiCusp.isCuspidal_comp_ti | (intros; apply GlobalTheory.CompanionTheory.TiCusp.isCuspidal_comp_ti <;> assumption)
