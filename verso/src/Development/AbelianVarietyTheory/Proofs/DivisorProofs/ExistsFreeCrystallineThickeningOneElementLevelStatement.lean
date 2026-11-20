import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeCrystallineThickeningOneElementLevel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDForm.exists_isFree_one_qAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFreeCrystallineThickeningOneElementLevel.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.exists_freeCrystallineThickening_oneElement_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (n : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) → ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Unit → F.B), IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  first | exact @GlobalTheory.PDForm.exists_isFree_one_qAt | exact GlobalTheory.PDForm.exists_isFree_one_qAt | (intros; apply GlobalTheory.PDForm.exists_isFree_one_qAt <;> assumption)
