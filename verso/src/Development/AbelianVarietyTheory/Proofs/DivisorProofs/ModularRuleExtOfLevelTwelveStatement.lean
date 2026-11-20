import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularRuleExtOfLevelTwelve
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealMult.Rule.eq_of_eq_on_level_twelve` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModularRuleExtOfLevelTwelve.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.modular_rule_ext_of_level_twelve : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k),
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), Nonempty (X.Level 12) →
      ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ) → s = t := by
  first | exact @GlobalTheory.RealMult.Rule.eq_of_eq_on_level_twelve | exact GlobalTheory.RealMult.Rule.eq_of_eq_on_level_twelve | (intros; apply GlobalTheory.RealMult.Rule.eq_of_eq_on_level_twelve <;> assumption)
