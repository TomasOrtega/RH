import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCompTransposeInv
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
Apply `GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit.whittaker_ti` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerCompTransposeInv.lean&line=206#L206)
-/
theorem _root_.GlobalTheory.T.whittaker_comp_transposeInv : ∀ φ : G3 → ℂ, IsLeftInvariant φ → Continuous φ → ∀ g : G3,
  FourierWhittaker.whittaker (fun g : G3 => φ (ti g)) g = tr (FourierWhittaker.whittaker φ) g := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit.whittaker_ti | exact GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit.whittaker_ti | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit.whittaker_ti <;> assumption)
