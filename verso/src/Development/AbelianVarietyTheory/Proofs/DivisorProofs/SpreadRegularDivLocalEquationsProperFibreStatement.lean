import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadRegularDivLocalEquationsProperFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.spread_regular_div` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpreadRegularDivLocalEquationsProperFibre.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.spread_regular_div_localEquations_proper_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (z : M₁.Z) (G : Ω), G ∈ M₁.O z → (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x') → ∃ (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), z ∈ V.1 ∧ valF M₁.pt V.1 g = G ∧ ∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x' := by
  first | exact @GlobalTheory.Poinc.spread_regular_div | exact GlobalTheory.Poinc.spread_regular_div | (intros; apply GlobalTheory.Poinc.spread_regular_div <;> assumption)
