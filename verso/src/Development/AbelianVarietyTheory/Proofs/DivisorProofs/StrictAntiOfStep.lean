import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar

open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

/- English proof (translation)
Consider the cases of `N with`. Consider the case `zero => intro a`. Conclude with `a.elim0`. Consider the case `succ n`. Rewrite using `[Fin.strictAnti_iff_succ_lt]`.

Introduce `i`. Conclude with `h _ _ (by simp)`.
-/
theorem strictAnti_of_step {N : ℕ} {α : Type} [Preorder α] (f : Fin N → α)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  cases N with
  | zero => intro a; exact a.elim0
  | succ n =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact h _ _ (by simp)

/- English proof (translation)
Introduce `ι _ N W H hD τ`. Establish `hT : (4 : ℤ) ≤ W.T` using `by have := H.h1; omega`. Establish `hh : (0 : ℤ) < W.h0`. Take `⟨k1, _⟩` from `H.h2`. Use `H.weightConst_nonneg` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `step : ∀ a b : Fin N, (b : ℕ) = a + 1 → W.u1 τ b < W.u1 τ a ∧ W.u' τ b < W.u' τ a`. Introduce `a b hab`. Take `⟨g1, g2, _⟩` from `divided_gaps ι N W H hD τ a b hab`. Distinguish the cases in `hb : (b : ℕ) = W.p`.

Take `⟨e1, e2⟩` from `g2 hb`. Establish `ha : ¬ ((b : ℕ) < W.p)` using `by omega`. Establish `ha' : (a : ℕ) < W.p` using `by omega`. Establish `p1 : 0 < W.u1 τ a - W.u1 τ b`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Use the polynomial consequences of the given equalities and inequalities. Establish `p2 : 0 < W.u1 τ a - W.u1 τ b - 3 * N`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Use the polynomial consequences of the given equalities and inequalities. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Simplify using `only [Wts.u', if_pos ha', if_neg ha]`. Use linear arithmetic over natural numbers and integers. Establish `e` using `g1 hb`.

Establish `hN : (0 : ℤ) ≤ W.T + W.Dd + 2 + 2 * N` using `by positivity`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Simplify using `only [Wts.u']`. Distinguish the cases in `ha : (a : ℕ) < W.p`. Establish `hb' : (b : ℕ) < W.p` using `by omega`.

Rewrite using `[if_pos ha, if_pos hb']`. Use linear arithmetic over natural numbers and integers. Establish `hb' : ¬ (b : ℕ) < W.p` using `by omega`. Rewrite using `[if_neg ha, if_neg hb']`. Use linear arithmetic over natural numbers and integers.

Establish `s1 : StrictAnti (W.u1 τ)` using `strictAnti_of_step _ fun a b h => (step a b h).1`. Conclude with `⟨s1, strictAnti_of_step _ fun a b h => (step a b h).2, (Int.cast_strictMono (R := ℝ)).comp_strictAnti s1⟩`.
-/
theorem divided_strictAnti : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ,
    StrictAnti (W.u1 τ) ∧ StrictAnti (W.u' τ) ∧ StrictAnti (fun i => (W.u1 τ i : ℝ)) := by
  intro ι _ N W H hD τ
  have hT : (4 : ℤ) ≤ W.T := by have := H.h1; omega
  have hh : (0 : ℤ) < W.h0 := by
    obtain ⟨k1, _⟩ := H.h2
    have := H.weightConst_nonneg
    omega
  have step : ∀ a b : Fin N, (b : ℕ) = a + 1 → W.u1 τ b < W.u1 τ a ∧ W.u' τ b < W.u' τ a := by
    intro a b hab
    obtain ⟨g1, g2, _⟩ := divided_gaps ι N W H hD τ a b hab
    by_cases hb : (b : ℕ) = W.p
    · obtain ⟨e1, e2⟩ := g2 hb
      have ha : ¬ ((b : ℕ) < W.p) := by omega
      have ha' : (a : ℕ) < W.p := by omega
      have p1 : 0 < W.u1 τ a - W.u1 τ b := by
        by_contra hc
        push_neg at hc
        nlinarith
      have p2 : 0 < W.u1 τ a - W.u1 τ b - 3 * N := by
        by_contra hc
        push_neg at hc
        nlinarith
      refine ⟨by omega, ?_⟩
      simp only [Wts.u', if_pos ha', if_neg ha]
      omega
    · have e := g1 hb
      have hN : (0 : ℤ) ≤ W.T + W.Dd + 2 + 2 * N := by positivity
      refine ⟨by omega, ?_⟩
      simp only [Wts.u']
      by_cases ha : (a : ℕ) < W.p
      · have hb' : (b : ℕ) < W.p := by omega
        rw [if_pos ha, if_pos hb']; omega
      · have hb' : ¬ (b : ℕ) < W.p := by omega
        rw [if_neg ha, if_neg hb']; omega
  have s1 : StrictAnti (W.u1 τ) := strictAnti_of_step _ fun a b h => (step a b h).1
  exact ⟨s1, strictAnti_of_step _ fun a b h => (step a b h).2,
    (Int.cast_strictMono (R := ℝ)).comp_strictAnti s1⟩

end GlobalTheory.MeanTop
