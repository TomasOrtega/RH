import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFourierJacobiBesselGroupsClosedHaarProduct.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ν : Measure (flagN d)) (𝓝 : Set (flagN d)), GlobalTheory.Per.IsUnitN S d.e ν 𝓝 → (IsClosed (jacGrp d : Set (GA D S)) ∧ ∀ μ : Measure (GA D S₀), μ.IsHaarMeasure → (semiMeas (flagN d) d.emb0 μ ν).IsHaarMeasure) ∧ IsClosed (besGrp d o : Set (GA D S)) ∧ ∀ μ : Measure (GA D A), μ.IsHaarMeasure → (semiMeas (flagN d) (embA d o) μ ν).IsHaarMeasure := by
  first | exact @GlobalTheory.MixPer.jacGrp_besGrp_haar | exact GlobalTheory.MixPer.jacGrp_besGrp_haar | (intros; apply GlobalTheory.MixPer.jacGrp_besGrp_haar <;> assumption)
