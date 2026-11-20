import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.Wts

variable {ι : Type} {N : ℕ} (W : Wts ι N)

/- English proof (translation)
Establish `hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1` using `by positivity`. Establish `hc` using `h.weightConst_nonneg`. Take `⟨h41, -, h43⟩` from `h.h4 τ a b hab`. Establish `h2` using `h.h2.1`. Rewrite using `[(hd τ).2 a b hab]`.

Establish `hN : (0 : ℤ) ≤ N` using `by positivity`. Use `split_ifs with hb`. Use `h43 hb` as an intermediate fact. Use `⟨Int.ediv_nonneg (by linarith) hM.le, ?_⟩` and prove the remaining obligations. Use `(Int.mul_ediv_self_le hM.ne').trans ?_` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5` using `h41 hb`. Establish `h6 : (0 : ℤ) ≤ ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N)` using `by positivity`. Conclude with `⟨Int.ediv_nonneg (by linarith) hM.le, Int.mul_ediv_self_le hM.ne'⟩`.
-/
theorem div_gap_step (h : W.Hyp) (hd : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) :
    0 ≤ W.u1 τ a - W.u1 τ b ∧
      ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) ≤ W.u τ a - W.u τ b + 2 := by
  have hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hc := h.weightConst_nonneg
  obtain ⟨h41, -, h43⟩ := h.h4 τ a b hab
  have h2 := h.h2.1
  rw [(hd τ).2 a b hab]
  have hN : (0 : ℤ) ≤ N := by positivity
  split_ifs with hb
  · have := h43 hb
    refine ⟨Int.ediv_nonneg (by linarith) hM.le, ?_⟩
    refine (Int.mul_ediv_self_le hM.ne').trans ?_
    linarith
  · have h5 := h41 hb
    have h6 : (0 : ℤ) ≤ ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N) := by positivity
    exact ⟨Int.ediv_nonneg (by linarith) hM.le, Int.mul_ediv_self_le hM.ne'⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `a b hab`. Establish `: b = a` using `Fin.ext (by simpa using hab)`. Substitute `this` using the available equality.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `a b hab`. Establish `hlt : (a : ℕ) + n < N` using `by have := b.2; omega`. Take `⟨h1, h2⟩` from `ih a ⟨a + n, hlt⟩ rfl`.

Take `⟨h3, h4⟩` from `W.div_gap_step h hd τ ⟨a + n, hlt⟩ b (by simp; omega)`. Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem div_gap_sum (h : W.Hyp) (hd : W.IsDiv) (τ : ι) (n : ℕ) : ∀ a b : Fin N, (b : ℕ) = a + n →
    0 ≤ W.u1 τ a - W.u1 τ b ∧
      ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) ≤ W.u τ a - W.u τ b + 2 * n := by
  induction n with
  | zero =>
    intro a b hab
    have : b = a := Fin.ext (by simpa using hab)
    subst this
    simp
  | succ n ih =>
    intro a b hab
    have hlt : (a : ℕ) + n < N := by have := b.2; omega
    obtain ⟨h1, h2⟩ := ih a ⟨a + n, hlt⟩ rfl
    obtain ⟨h3, h4⟩ := W.div_gap_step h hd τ ⟨a + n, hlt⟩ b (by simp; omega)
    refine ⟨by linarith, ?_⟩
    push_cast
    nlinarith

end GlobalTheory.MeanTop.Wts

namespace GlobalTheory.MeanTop

/- English proof (translation)
Introduce `ι _ N W h hd τ i`. Establish `hk` using `h.kc_pos`. Establish `hk2` using `h.kc_lt`. Establish `hp` using `h.p_lt`. Establish `hc` using `h.weightConst_nonneg`.

Establish `hi` using `i.2`. Establish `hN : (0 : ℤ) ≤ N` using `by positivity`. Set `a : Fin N` to `⟨W.kc - 1, by omega⟩`. Establish `ha : (a : ℕ) + 1 = W.kc` using `by simp only [a]; omega`. Establish `hu : W.u τ a = 0` using `h.anchor τ a ha`.

Establish `hu1 : W.u1 τ a = 0` using `(hd τ).1 a ha`. Establish `up : (i : ℕ) < W.kc → 0 ≤ W.u1 τ i ∧ ((W.T : ℤ) + W.Dd + 1) * W.u1 τ i ≤ W.u τ i + 2 * N`. Introduce `hi'`. Take `⟨h1, h2⟩` from `W.div_gap_sum h hd τ (a - i) i a (by omega)`. Establish `h3 : (((a : ℕ) - i : ℕ) : ℤ) ≤ N` using `by omega`.

Rewrite `h1`, `h2` using `[hu1, sub_zero]`. Rewrite `h2` using `[hu]`. Conclude with `⟨h1, by linarith⟩`. Establish `down : W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0 ∧ ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) ≤ -W.u τ i + 2 * N`. Introduce `hi'`.

Take `⟨h1, h2⟩` from `W.div_gap_sum h hd τ (i - a) a i (by omega)`. Establish `h3 : (((i : ℕ) - a : ℕ) : ℤ) ≤ N` using `by omega`. Rewrite `h1`, `h2` using `[hu1, zero_sub]`. Rewrite `h2` using `[hu]`. Conclude with `⟨by linarith, by linarith⟩`.

Use `⟨?_, fun hi' => (down hi').1, fun hi' => (up hi').1⟩` and prove the remaining obligations. Distinguish the cases in `hi' : (i : ℕ) < W.kc`. Take `⟨h1, h2⟩` from `up hi'`. Rewrite using `[abs_of_nonneg h1]`. Use `le_abs_self (W.u τ i)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨h1, h2⟩` from `down (by omega)`. Rewrite using `[abs_of_nonpos h1]`. Use `neg_le_abs (W.u τ i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem divided_entries : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ i,
    ((W.T : ℤ) + W.Dd + 1) * |W.u1 τ i| ≤ |W.u τ i| + W.c0 + 4 * N ∧
      (W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0) ∧ ((i : ℕ) < W.kc → 0 ≤ W.u1 τ i) := by
  intro ι _ N W h hd τ i
  have hk := h.kc_pos
  have hk2 := h.kc_lt
  have hp := h.p_lt
  have hc := h.weightConst_nonneg
  have hi := i.2
  have hN : (0 : ℤ) ≤ N := by positivity
  let a : Fin N := ⟨W.kc - 1, by omega⟩
  have ha : (a : ℕ) + 1 = W.kc := by simp only [a]; omega
  have hu : W.u τ a = 0 := h.anchor τ a ha
  have hu1 : W.u1 τ a = 0 := (hd τ).1 a ha
  have up : (i : ℕ) < W.kc → 0 ≤ W.u1 τ i ∧
      ((W.T : ℤ) + W.Dd + 1) * W.u1 τ i ≤ W.u τ i + 2 * N := by
    intro hi'
    obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (a - i) i a (by omega)
    have h3 : (((a : ℕ) - i : ℕ) : ℤ) ≤ N := by omega
    rw [hu1, sub_zero] at h1 h2
    rw [hu] at h2
    exact ⟨h1, by linarith⟩
  have down : W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0 ∧
      ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) ≤ -W.u τ i + 2 * N := by
    intro hi'
    obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (i - a) a i (by omega)
    have h3 : (((i : ℕ) - a : ℕ) : ℤ) ≤ N := by omega
    rw [hu1, zero_sub] at h1 h2
    rw [hu] at h2
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, fun hi' => (down hi').1, fun hi' => (up hi').1⟩
  by_cases hi' : (i : ℕ) < W.kc
  · obtain ⟨h1, h2⟩ := up hi'
    rw [abs_of_nonneg h1]
    have := le_abs_self (W.u τ i)
    linarith
  · obtain ⟨h1, h2⟩ := down (by omega)
    rw [abs_of_nonpos h1]
    have := neg_le_abs (W.u τ i)
    linarith

end GlobalTheory.MeanTop
