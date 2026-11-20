import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

/- English proof (translation)
Introduce `D L j τ hv`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `ht0` using `D.R.t_odd.pos`. Establish `hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ = D.R.k + (j : ℕ)`. Simplify using `only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]`.

Use linear arithmetic over natural numbers and integers. Establish `htt : (parOf L j).t = D.R.t` using `rfl`. Establish `he : (wts L j).e τ = wj D ((j : ℕ) + 1) τ` using `rfl`. Prove the components needed by the constructor for the conclusion. Introduce `a ha1 ha2`.

Rewrite `ha1`, the goal using `[hkc]`. Rewrite `ha2` using `[hkc, htt]`. Take `⟨s, rfl⟩` from `Nat.exists_eq_add_of_le ha1`. Establish `h1` using `hv.2.2.1 s (by omega)`. Establish `h0` using `hv.2.2.1 0 ht0`.

Simplify using `only [add_zero, Nat.cast_zero, sub_zero] at h0`. Establish `hU : ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) = (((wts L j).U (parOf L j) τ (D.R.k + j) - s : ℤ) : ℝ)` using `by push_cast; linarith`. Establish `hU'` using `Int.cast_injective (α := ℝ) hU`. Express the relevant statement in the definitionally equal form `Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ = Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ - _ at hU'`. Unfold `Formalism.CohomologicalDescent.UnitNormBounds.UN at hU'`.

Move the coercions through the operations in `at hU'`. Use linear arithmetic over natural numbers and integers. Establish `hrow : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t - 1 = D.R.k + (j : ℕ) + (D.R.t - 1)`. Rewrite using `[hkc, htt]`. Use linear arithmetic over natural numbers and integers.

Establish `h` using `hv.2.2.1 (D.R.t - 1) (by omega)`. Establish `hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; simp`. Rewrite `h` using `[hts]`. Rewrite using `[Formalism.CohomologicalDescent.ShortWeightBounds.Wts.bot, hrow, htt, he]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem block_centre : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  intro D L j τ hv
  have hk := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ = D.R.k + (j : ℕ) := by
    simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]; omega
  have htt : (parOf L j).t = D.R.t := rfl
  have he : (wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  constructor
  · intro a ha1 ha2
    rw [hkc] at ha1 ⊢
    rw [hkc, htt] at ha2
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha1
    have h1 := hv.2.2.1 s (by omega)
    have h0 := hv.2.2.1 0 ht0
    simp only [add_zero, Nat.cast_zero, sub_zero] at h0
    have hU : ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) = (((wts L j).U (parOf L j) τ (D.R.k + j) - s : ℤ) : ℝ) := by
      push_cast; linarith
    have hU' := Int.cast_injective (α := ℝ) hU
    change Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ = Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ - _ at hU'
    unfold Formalism.CohomologicalDescent.UnitNormBounds.UN at hU'
    push_cast at hU'
    omega
  · have hrow : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t - 1 = D.R.k + (j : ℕ) + (D.R.t - 1) := by
      rw [hkc, htt]; omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts] at h
    rw [Formalism.CohomologicalDescent.ShortWeightBounds.Wts.bot, hrow, htt, he]
    linarith

end GlobalTheory.ExpTie.Lift

end
