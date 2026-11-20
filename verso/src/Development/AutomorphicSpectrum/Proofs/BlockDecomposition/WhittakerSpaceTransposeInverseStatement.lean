import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSpaceTransposeInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchSmoothCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionCompTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenSubgroupTransposeInvCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGL3AdelicDecayStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTransformPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInvPropertiesStatement
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerSpaceTransposeInverse.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.whittaker_space_transpose_inverse : ∀ V : Submodule ℂ (G3 → ℂ), WhA V → WhA (tV V) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV.whA_tV | exact GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV.whA_tV | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV.whA_tV <;> assumption)
