import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainSplitCentreProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFundamentalDomainSplitCentreProduct.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.fundamental_domain_split_centre_product : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure], IsFundamentalDomain (latticeGL E a) ((fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) '' (RightCosetSpace.fundamentalDomain (rationalGLOne E a) ×ˢ Set.Ico (0 : ℝ) 1)) μ := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd | exact GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd <;> assumption)
