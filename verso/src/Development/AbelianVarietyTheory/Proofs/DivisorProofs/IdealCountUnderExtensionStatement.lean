import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealCountUnderExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdealCountUnderExtension.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.ideal_count_under_extension : ∀ (E : Type) [Field E] [NumberField E] (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (τ : E →+* k) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → FractionalIdeal.count k' 𝔓 ((𝔞.map (RingOfIntegers.mapRingHom (i.comp τ)) : Ideal (𝓞 k')) : FractionalIdeal (nonZeroDivisors (𝓞 k')) k') = ε * FractionalIdeal.count k 𝔭 ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 k)) : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  first | exact @GlobalTheory.count_map_comp_ideal_eq_mul_of_valuation_pow | exact GlobalTheory.count_map_comp_ideal_eq_mul_of_valuation_pow | (intros; apply GlobalTheory.count_map_comp_ideal_eq_mul_of_valuation_pow <;> assumption)
