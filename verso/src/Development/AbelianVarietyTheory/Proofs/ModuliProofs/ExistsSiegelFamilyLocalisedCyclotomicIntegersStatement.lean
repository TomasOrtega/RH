import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegers
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FExistsSiegelFamilyLocalisedCyclotomicIntegers.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers : Out.Laws → Out.Laws2 → ∀ (h k p : ℕ) (o : Type) [CommRing o] (ζ : o) (j : o →+* ZP p k), Odd k → 3 ≤ k → p.Prime → Function.Injective j → j ζ = zetaZP p k → (∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y) → Algebra.IsAlgebraic ℤ o → SFam h k ζ → ∃ Ag : SiegelFamily h p k, SRep Ag := by
  first | exact @GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily | exact GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily | (intros; apply GlobalTheory.SiegelFamilyBaseChange.exists_siegelFamily <;> assumption)
