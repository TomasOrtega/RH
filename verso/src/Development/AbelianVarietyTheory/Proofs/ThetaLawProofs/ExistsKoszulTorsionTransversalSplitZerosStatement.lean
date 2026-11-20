import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKoszulTorsionTransversalSplitZeros
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
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
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KeyKa.KoszulEx.exists_kosVal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FExistsKoszulTorsionTransversalSplitZeros.lean&line=380#L380)
-/
theorem _root_.GlobalTheory.T.exists_koszulTorsion_transversal_split_zeros : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → EtZ x s z ch → d = x.P.g.factorial * n ^ x.P.g ∧ ∃ t : Rˣ, KosVal x l s z ch b t := by
  first | exact @GlobalTheory.KeyKa.KoszulEx.exists_kosVal | exact GlobalTheory.KeyKa.KoszulEx.exists_kosVal | (intros; apply GlobalTheory.KeyKa.KoszulEx.exists_kosVal <;> assumption)
