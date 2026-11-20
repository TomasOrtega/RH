import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfBaseChangeRatioSections
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemRangeOfBaseChangeRatioSections.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.mem_range_of_base_change_ratio_sections : ∀ {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}} (h : X ⟶ Sp K) (U : X.Opens) (f₁ f₂ : Γ(X, U)) (l : L), f₂ ≠ 0 → ((pullback.fst h (spMap ψ)).app U).hom f₁ = ((pullback.fst h (spMap ψ)).app U).hom f₂ * resTop _ (scal (pullback.snd h (spMap ψ)) l) → l ∈ Set.range ψ := by
  first | exact @GlobalTheory.ConstDescent.mem_range_of_pullback_eq | exact GlobalTheory.ConstDescent.mem_range_of_pullback_eq | (intros; apply GlobalTheory.ConstDescent.mem_range_of_pullback_eq <;> assumption)
