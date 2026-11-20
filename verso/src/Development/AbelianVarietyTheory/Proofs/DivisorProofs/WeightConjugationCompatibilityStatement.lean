import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConjugationCompatibility
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedAdelicMetricIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNorms
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeightConjugationCompatibility.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.weight_conjugation_compatibility : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (G : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (w : ∀ σ : 𝓞 F →+* ℂ, CxPts M.p σ → ℝ), (∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))), y'.1 = y.1 ≫ M.j → w _ y' = G σ y) → (∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → G σ' y' = G σ y) → ∀ σ σ' : 𝓞 F →+* ℂ, (Weight.ofFun (w σ)).IsConj (Weight.ofFun (w σ')) := by
  first | exact @GlobalTheory.ModelLiftConj.model_weight_isConj_of_lift | exact GlobalTheory.ModelLiftConj.model_weight_isConj_of_lift | (intros; apply GlobalTheory.ModelLiftConj.model_weight_isConj_of_lift <;> assumption)
