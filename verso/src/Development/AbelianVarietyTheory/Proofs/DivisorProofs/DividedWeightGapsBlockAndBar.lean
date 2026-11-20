import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

/- English proof (translation)
Establish `h1 : m * (x / m) + x % m = x` using `Int.mul_ediv_add_emod x m`. Establish `h2 : x % m < m` using `Int.emod_lt_of_pos x hm`. Establish `h3 : 0 ≤ x / m` using `Int.ediv_nonneg (by omega) hm.le`. Establish `h4 : 4 * m * (x / m) ≤ 5 * T * (x / m)` using `mul_le_mul_of_nonneg_right hT h3`. Establish `h5 : 0 ≤ T * (x / m)` using `mul_nonneg (by omega) h3`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem le_two_mul_ediv {x m T h : ℤ} (hm : 0 < m) (hT : 4 * m ≤ 5 * T) (hh : 0 ≤ h)
    (hx : 3 * h ≤ 4 * (x - m)) : h ≤ 2 * T * (x / m) := by
  have h1 : m * (x / m) + x % m = x := Int.mul_ediv_add_emod x m
  have h2 : x % m < m := Int.emod_lt_of_pos x hm
  have h3 : 0 ≤ x / m := Int.ediv_nonneg (by omega) hm.le
  have h4 : 4 * m * (x / m) ≤ 5 * T * (x / m) := mul_le_mul_of_nonneg_right hT h3
  have h5 : 0 ≤ T * (x / m) := mul_nonneg (by omega) h3
  nlinarith

/- English proof (translation)
Introduce `ι _ N W H hD τ a b hab`. Establish `hq` using `(hD τ).2 a b hab`. Take `⟨g1, g2, g3⟩` from `H.h4 τ a b hab`. Take `⟨k1, k2⟩` from `H.h2`. Establish `c0` using `H.weightConst_nonneg`.

Establish `h1 : 4 * (W.Dd : ℤ) + 4 ≤ W.T` using `by exact_mod_cast H.h1`. Establish `hm : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1` using `by positivity`. Establish `hT : 4 * ((W.T : ℤ) + W.Dd + 1) ≤ 5 * (W.T : ℤ)` using `by omega`. Establish `hh : 0 ≤ W.h0` using `by omega`. Use `⟨fun hb => ?_, fun hb => ?_, fun hb ha => ?_⟩` and prove the remaining obligations.

Rewrite using `[hq, if_neg hb]`. Use `Int.le_ediv_of_mul_le hm ?_` and prove the remaining obligations. Use `g1 hb` as an intermediate fact. Establish `h0 : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Use `g3 hb` as an intermediate fact. Establish `key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b)`. Rewrite using `[hq, if_pos hb]`. Conclude with `le_two_mul_ediv hm hT hh (by omega)`. Conclude with `⟨key, by nlinarith⟩`.

Use `g2 ha` as an intermediate fact. Establish `key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b)`. Rewrite using `[hq, if_neg hb]`. Conclude with `le_two_mul_ediv hm hT hh (by omega)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem divided_gaps : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (((b : ℕ) ≠ W.p → (W.T : ℤ) + W.Dd + 2 + 2 * N ≤ W.u1 τ a - W.u1 τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) ∧ W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b - 3 * N)) ∧ ((b : ℕ) ≠ W.p → W.kc ≤ (a : ℕ) → W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b))) := by
  intro ι _ N W H hD τ a b hab
  have hq := (hD τ).2 a b hab
  obtain ⟨g1, g2, g3⟩ := H.h4 τ a b hab
  obtain ⟨k1, k2⟩ := H.h2
  have c0 := H.weightConst_nonneg
  have h1 : 4 * (W.Dd : ℤ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hm : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hT : 4 * ((W.T : ℤ) + W.Dd + 1) ≤ 5 * (W.T : ℤ) := by omega
  have hh : 0 ≤ W.h0 := by omega
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb ha => ?_⟩
  · rw [hq, if_neg hb]
    refine Int.le_ediv_of_mul_le hm ?_
    have := g1 hb
    have h0 : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N := by positivity
    nlinarith
  · have := g3 hb
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_pos hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    exact ⟨key, by nlinarith⟩
  · have := g2 ha
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_neg hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    nlinarith

end GlobalTheory.MeanTop
