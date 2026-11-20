import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProduct
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBernsteinZelevinskyDerivativeHarishChandraProduct.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.bernsteinZelevinskyDerivative_harishChandraProduct : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n i : ℕ), degL L = n → i ≤ n → (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) → wh ψ (der ψ i (hcL L n)) = (((Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i)).card : ℂ) ∧ wh ψ (hcL L n) = 1 := by
  first | exact @GlobalTheory.GLq.Leibniz.main | exact GlobalTheory.GLq.Leibniz.main | (intros; apply GlobalTheory.GLq.Leibniz.main <;> assumption)
