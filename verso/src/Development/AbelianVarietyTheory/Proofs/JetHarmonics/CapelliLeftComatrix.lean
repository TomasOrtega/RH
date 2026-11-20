import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective

open Formalism.REAL Finset

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ _ m E hE u j l`. Use `set b : Fin (m + 1) → Fin (m + 1) := Fin.cons l (Fin.succAbove j) with hb`. Establish `hexp` using `PI.QmColExpWork.expFirst E id b u`. Establish `hbc : b ∘ Fin.succ = Fin.succAbove j`. Use function extensionality and compare the values at `k`.

Simplify using `[hb]`. Establish `hb0 : b 0 = l` using `by simp [hb]`. Rewrite `hexp` using `[hbc, hb0]`. Establish `hcast : ∀ (k : ℕ) (x : A), (((-1 : ℤ) ^ k : ℤ) : A) * x = ((-1 : ℂ) ^ k) • x`. Introduce `k x`.

Rewrite using `[Algebra.smul_def]`. Use `push_cast`. Simplify using the standard rewrite rules. Establish `hL : ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) = ((-1 : ℂ) ^ (j : ℕ)) • qminor E id b u`. Rewrite using `[hexp, Finset.smul_sum]`.

Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[hcast, smul_smul, ← pow_add, add_comm (j : ℕ) (a : ℕ)]`. Both sides reduce to the same expression. Rewrite using `[hL]`. Distinguish the cases in `hlj : l = j`.

Substitute `hlj` using the available equality. Establish `hbcyc : b = id ∘ PI.QmColExpWork.cyc0 m l`. Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations. Simplify using `[hb, PI.QmColExpWork.cycle_perm_zero]`.

Simplify using `[hb, PI.QmColExpWork.cycle_perm_succ]`. Rewrite using `[if_pos rfl, hbcyc, qSkewCol A (m + 1) (m + 1) E hE id id _ u, PI.QmColExpWork.sign_cycle_perm, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hcast, smul_smul, ← mul_pow]`. Simplify using `[qdet]`. Rewrite using `[if_neg hlj]`. Take `⟨k0, hk0⟩` from `Fin.exists_succAbove_eq hlj`.

Establish `hfix : b ∘ Equiv.swap (0 : Fin (m + 1)) k0.succ = b`. Use function extensionality and compare the values at `k`. Establish `h0 : b 0 = b k0.succ` using `by simp [hb, hk0]`. Simplify using `only [Function.comp, Equiv.swap_apply_def]`. Use `split_ifs with h1 h2`.

Rewrite using `[h1, h0]`. Rewrite using `[h2, h0]`. Both sides reduce to the same expression. Establish `hs` using `qSkewCol A (m + 1) (m + 1) E hE id b (Equiv.swap 0 k0.succ) u`. Rewrite `hs` using `[hfix, Equiv.Perm.sign_swap (Fin.succ_ne_zero k0).symm]`.

Establish `h2 : (2 : ℂ) • qminor E id b u = 0`. Rewrite using `[two_smul]`. Use `nth_rewrite 1 [hs]`. Simplify using the standard rewrite rules. Establish `hz : qminor E id b u = 0`.

Establish `h3` using `congrArg (fun x => (2 : ℂ)⁻¹ • x) h2`. Simplify `h3` using `[smul_smul]`. Rewrite using `[hz, smul_zero]`.
-/
theorem capelli_left_comatrix :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E →
      ∀ (u : ℂ) (j l : Fin (m + 1)),
        ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
            (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
          if l = j then qdet E u else 0 := by
  intro A _ _ m E hE u j l
  set b : Fin (m + 1) → Fin (m + 1) := Fin.cons l (Fin.succAbove j) with hb
  have hexp := PI.QmColExpWork.expFirst E id b u
  have hbc : b ∘ Fin.succ = Fin.succAbove j := by
    funext k; simp [hb]
  have hb0 : b 0 = l := by simp [hb]
  rw [hbc, hb0] at hexp
  have hcast : ∀ (k : ℕ) (x : A), (((-1 : ℤ) ^ k : ℤ) : A) * x = ((-1 : ℂ) ^ k) • x := by
    intro k x
    rw [Algebra.smul_def]
    push_cast
    simp
  have hL : ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
      ((-1 : ℂ) ^ (j : ℕ)) • qminor E id b u := by
    rw [hexp, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcast, smul_smul, ← pow_add, add_comm (j : ℕ) (a : ℕ)]
    rfl
  rw [hL]
  by_cases hlj : l = j
  · subst hlj
    have hbcyc : b = id ∘ PI.QmColExpWork.cyc0 m l := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp [hb, PI.QmColExpWork.cycle_perm_zero]
      · simp [hb, PI.QmColExpWork.cycle_perm_succ]
    rw [if_pos rfl, hbcyc, qSkewCol A (m + 1) (m + 1) E hE id id _ u, PI.QmColExpWork.sign_cycle_perm,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hcast, smul_smul, ← mul_pow]
    simp [qdet]
  · rw [if_neg hlj]
    obtain ⟨k0, hk0⟩ := Fin.exists_succAbove_eq hlj
    have hfix : b ∘ Equiv.swap (0 : Fin (m + 1)) k0.succ = b := by
      funext k
      have h0 : b 0 = b k0.succ := by simp [hb, hk0]
      simp only [Function.comp, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, h0]
      · rw [h2, h0]
      · rfl
    have hs := qSkewCol A (m + 1) (m + 1) E hE id b (Equiv.swap 0 k0.succ) u
    rw [hfix, Equiv.Perm.sign_swap (Fin.succ_ne_zero k0).symm] at hs
    have h2 : (2 : ℂ) • qminor E id b u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hs]
      simp
    have hz : qminor E id b u = 0 := by
      have h3 := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
      simpa [smul_smul] using h3
    rw [hz, smul_zero]

end GlobalTheory
