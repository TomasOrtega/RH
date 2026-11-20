import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicNormLeOneIffValuation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPAdicNormLeOneIffValuation.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.p_adic_norm_le_one_iff_valuation : ∀ {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]), (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) → ∀ a : K, ‖k (io a)‖ ≤ 1 ↔ la.valuation K a ≤ 1 := by
  first | exact @GlobalTheory.PlaceNorm.norm_le_one_iff_valuation_le_one | exact GlobalTheory.PlaceNorm.norm_le_one_iff_valuation_le_one | (intros; apply GlobalTheory.PlaceNorm.norm_le_one_iff_valuation_le_one <;> assumption)
