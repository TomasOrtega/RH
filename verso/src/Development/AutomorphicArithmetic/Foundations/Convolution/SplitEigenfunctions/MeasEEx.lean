import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Unimod
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

/- English proof (translation)
Introduce `E _ _`. Set `μ : Measure (G1 E)` to `Measure.haar`. Take `⟨D, hD, -, hf⟩` from `GlobalTheory.exists_isFundamentalDomain_subgroup (Gam E)`. Conclude with `⟨⟨μ, D, inferInstance, M.unimod E μ, hD, hf μ⟩⟩`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.measEEx :
    MeasEEx := by
  intro E _ _
  let μ : Measure (G1 E) := Measure.haar
  obtain ⟨D, hD, -, hf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Gam E)
  exact ⟨⟨μ, D, inferInstance, M.unimod E μ, hD, hf μ⟩⟩
