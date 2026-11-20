import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaValueCont.continuousOn_value` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FContinuousOnThetaFrameValueHolomorphicFamily.lean&line=165#L165)
-/
theorem _root_.GlobalTheory.T.continuousOn_thetaFrameValue_holomorphicFamily : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (y : KeyIn S) (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)) (t : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → (∀ p ∈ B, ∃ x : KeyIn ℂ, KeyPB x y (s p).toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t p = M.det ^ 4 / c ^ 8)) → ContinuousOn t B := by
  first | exact @GlobalTheory.ThetaValueCont.continuousOn_value | exact GlobalTheory.ThetaValueCont.continuousOn_value | (intros; apply GlobalTheory.ThetaValueCont.continuousOn_value <;> assumption)
