import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallEqDominantIndexStatement
open Polynomial
open Classical

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem card_roots_le_radius_bounds :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ),
      0 < ρ → f.coeff d ≠ 0 →
      ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) →
          d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧
      ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) →
          Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by
  intro K _ _ _ f ρ d hρ hd
  have hf : f ≠ 0 := by
    rintro rfl
    exact hd (by simp)
  obtain ⟨hA, hB⟩ := GlobalTheory.T.card_roots_closedBall_dominant_coeff K f ρ hρ hf
  set e := Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) with he
  refine ⟨fun H => ?_, fun H => ?_⟩
  · by_contra hlt
    push_neg at hlt
    have h1 := hB d hlt
    have h2 := H e
    linarith
  · by_contra hlt
    push_neg at hlt
    have h1 := H e hlt
    have h2 := hA d
    linarith

end GlobalTheory
