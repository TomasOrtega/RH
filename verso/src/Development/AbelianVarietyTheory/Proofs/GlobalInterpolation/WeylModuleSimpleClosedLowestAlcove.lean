import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsRowOperatorStableDualWeylAndGLSubmodulesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HighestWeightVectorMemOfLtStableDualWeylStatement
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

/- English proof (translation)
Introduce `h`. Take `⟨_, h2, h3⟩` from `factNatW N lam`. Use `⟨h3 h, ?_⟩` and prove the remaining obligations. Establish `e0` using `h2 ⟨0, h⟩`. Establish `e1` using `h2 ⟨N - 1, by omega⟩`.

Rewrite `e1` using `[h3 h]`. Distinguish the cases in `hN1 : N = 1`. Substitute `hN1` using the available equality. Establish `: (⟨0, h⟩ : Fin 1) = ⟨1 - 1, by omega⟩` using `rfl`. Rewrite using `[this, h3 h]`.

Use linear arithmetic over natural numbers and integers. Establish `hlt : (⟨0, h⟩ : Fin N) < ⟨N - 1, by omega⟩` using `Fin.mk_lt_mk.mpr (by omega)`. Use `hl _ _ hlt` as an intermediate fact. Simplify using `only at this`. Establish `hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1` using `by omega`.

Move the coercions through the operations in `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem natW_alcove_bound (p : ℕ) (N : ℕ) (lam : DomWeight N)
    (hl : ∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) :
    ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 ∧ lam.natW ⟨0, h⟩ + (N - 1) ≤ p := by
  intro h
  obtain ⟨_, h2, h3⟩ := factNatW N lam
  refine ⟨h3 h, ?_⟩
  have e0 := h2 ⟨0, h⟩
  have e1 := h2 ⟨N - 1, by omega⟩
  rw [h3 h] at e1
  by_cases hN1 : N = 1
  · subst hN1
    have : (⟨0, h⟩ : Fin 1) = ⟨1 - 1, by omega⟩ := rfl
    rw [this, h3 h]
    omega
  · have hlt : (⟨0, h⟩ : Fin N) < ⟨N - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    have := hl _ _ hlt
    simp only at this
    have hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    push_cast at this
    omega

/- English proof (translation)
Introduce `p hp k _ _ N lam hl`. Establish `hN` using `factNatW N lam`. Establish `hne : nablaSq k N lam ≠ ⊥`. Introduce `h`. Establish `hm : hw k le_rfl lam.natW ∈ nablaSq k N lam` using `hwMem k N N le_rfl _ hN.1`.

Rewrite `hm` using `[h, Submodule.mem_bot]`. Conclude with `hwNe k N N le_rfl _ hm`. Use `⟨hne, fun M hM hG => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `key` using `GlobalTheory.T.highestWeightVector_mem_of_lt_stable_dualWeyl p hp k N lam.natW hN.1 (natW_alcove_bound p N lam hl)`. Establish `good` using `GlobalTheory.T.isRowOperatorStable_dualWeyl_and_GLSubmodules k N lam`. Establish `h1` using `(key ⊥ M (good_top_bot k N N).2 (good.2 M hG) (bot_lt_iff_ne_bot.2 hc.1) hM).1`. Establish `h2` using `(key M (nablaSq k N lam) (good.2 M hG) good.1 (lt_of_le_of_ne hM hc.2) le_rfl).2`. Conclude with `h2 h1`.
-/
theorem inducedSimpleLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  intro p hp k _ _ N lam hl
  have hN := factNatW N lam
  have hne : nablaSq k N lam ≠ ⊥ := by
    intro h
    have hm : hw k le_rfl lam.natW ∈ nablaSq k N lam := hwMem k N N le_rfl _ hN.1
    rw [h, Submodule.mem_bot] at hm
    exact hwNe k N N le_rfl _ hm
  refine ⟨hne, fun M hM hG => ?_⟩
  by_contra hc
  push_neg at hc
  have key := GlobalTheory.T.highestWeightVector_mem_of_lt_stable_dualWeyl p hp k N lam.natW hN.1 (natW_alcove_bound p N lam hl)
  have good := GlobalTheory.T.isRowOperatorStable_dualWeyl_and_GLSubmodules k N lam
  have h1 := (key ⊥ M (good_top_bot k N N).2 (good.2 M hG) (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) (good.2 M hG) good.1 (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.Alc
