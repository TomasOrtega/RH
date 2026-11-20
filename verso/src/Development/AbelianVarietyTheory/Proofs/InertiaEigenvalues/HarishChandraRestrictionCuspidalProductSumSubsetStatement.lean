import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubset
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.ResCuspProd.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHarishChandraRestrictionCuspidalProductSumSubset.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.harishChandraRestriction_cuspidal_product_sum_subsets : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (a b : ℕ), degL L = a + b → (∀ p ∈ L, IsCusp p.2) → ∀ x y, res a b (hcL L (a + b)) x y = ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ i ∈ I, (L.get i).1 = a), hcL ((I.sort (· ≤ ·)).map L.get) a x * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y := by
  first | exact @GlobalTheory.GLq.ResCuspProd.main | exact GlobalTheory.GLq.ResCuspProd.main | (intros; apply GlobalTheory.GLq.ResCuspProd.main <;> assumption)
