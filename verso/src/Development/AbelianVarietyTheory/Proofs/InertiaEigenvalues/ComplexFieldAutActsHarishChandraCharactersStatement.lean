import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFieldAutActsHarishChandraCharacters
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FComplexFieldAutActsHarishChandraCharacters.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.complexFieldAut_acts_harishChandra_characters : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  first | exact @GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters | exact GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters | (intros; apply GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters <;> assumption)
