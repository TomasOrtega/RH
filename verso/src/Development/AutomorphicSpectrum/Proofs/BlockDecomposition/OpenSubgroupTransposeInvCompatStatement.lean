import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenSubgroupTransposeInvCompat
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOpenSubgroupTransposeInvCompat.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.open_subgroup_transposeInv_compat : ∀ U₀ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3), ∃ U₁ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3),
  ∀ u ∈ U₁, ∃ u' ∈ U₀, ∀ g : G3, ti (g * finEmb ℚ 3 u) = ti g * finEmb ℚ 3 u' := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel.ti_level | exact GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel.ti_level | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel.ti_level <;> assumption)
