import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.FromGL

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ _ g`. Take `⟨b, hb, k, hk, e⟩` from `Reduction.exists_adelicBorel_mul_maxCompact (K := F) (n := 2) (gl g)`. Take `⟨x, a, k', hk', hg, -, -⟩` from `UpperTheory.ConvolutionTheory.R2.M.fromGL F g b hb k hk e`. Conclude with `⟨x, a, k', hk', hg⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.iwa :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ g : G1 F, ∃ (b : A F) (a : (A F)ˣ), ∃ k ∈ KK F, g = nU b * mD a * k := by
  intro F _ _ _ g
  obtain ⟨b, hb, k, hk, e⟩ := Reduction.exists_adelicBorel_mul_maxCompact (K := F) (n := 2) (gl g)
  obtain ⟨x, a, k', hk', hg, -, -⟩ := UpperTheory.ConvolutionTheory.R2.M.fromGL F g b hb k hk e
  exact ⟨x, a, k', hk', hg⟩
