import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallEqDominantIndexStatement
open Polynomial
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ _ f ρ d hρ hd`. Establish `hf : f ≠ 0`. Introduce and unpack `rfl`. Conclude with `hd (by simp)`. Take `⟨hA, hB⟩` from `GlobalTheory.T.card_roots_closedBall_dominant_coeff K f ρ hρ hf`.

Use `set e := Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) with he`. Use `⟨fun H => ?_, fun H => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt push_neg at hlt`. Establish `h1` using `hB d hlt`. Establish `h2` using `H e`.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hlt push_neg at hlt`. Establish `h1` using `H e hlt`. Establish `h2` using `hA d`. Combine the linear equalities and inequalities to obtain the conclusion.
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
