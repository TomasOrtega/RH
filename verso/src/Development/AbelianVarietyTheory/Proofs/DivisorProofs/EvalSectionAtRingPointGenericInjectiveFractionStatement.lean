import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFraction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEvalSectionAtRingPointGenericInjectiveFraction.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction : ∀ (K : Type) [Field K] (C : Scheme.{0}) [IsIntegral C] (x : Sp K ⟶ C), IsGen x → ∀ V : C.Opens, (V : Set C).Nonempty → ∃ h : ⊤ ≤ x ⁻¹ᵁ V, Function.Injective (evAt x h) ∧ (IsAffineOpen V → ∀ z : K, ∃ a b : Γ(C, V), b ≠ 0 ∧ z * evAt x h b = evAt x h a) := by
  first | exact @GlobalTheory.Nef.isGen_evAt_frac | exact GlobalTheory.Nef.isGen_evAt_frac | (intros; apply GlobalTheory.Nef.isGen_evAt_frac <;> assumption)
