import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaExtensionEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LieSmooth.finsum_sum_log_embOver_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProductFormulaExtensionEmbeddings.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.product_formula_extension_embeddings : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (φ : F →+* K) (a : K), a ≠ 0 → (Function.support fun v : HeightOneSpectrum (𝓞 F) => ∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 a))).Finite ∧ ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 a)) = -∑ σ : K →+* ℂ, Real.log ‖σ a‖ := by
  first | exact @GlobalTheory.LieSmooth.finsum_sum_log_embOver_eq | exact GlobalTheory.LieSmooth.finsum_sum_log_embOver_eq | (intros; apply GlobalTheory.LieSmooth.finsum_sum_log_embOver_eq <;> assumption)
