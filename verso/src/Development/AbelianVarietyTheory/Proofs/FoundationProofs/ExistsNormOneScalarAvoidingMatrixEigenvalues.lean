import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.ConjSqrtMinusD
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormOneScalar

/- English proof (translation)
Establish `hm : ∀ k : ℕ, ((k : E) + 1) - s ≠ 0`. Introduce `k h`. Establish `h1 : s = (k : E) + 1` using `by linear_combination -h`. Establish `h2 : c s = s` using `by rw [h1]; simp`. Apply `hs` to reduce the goal to its premises.

Establish `: (2 : E) * s = 0` using `by linear_combination hc - h2`. Simplify using `using this`. Establish `hp : ∀ k : ℕ, ((k : E) + 1) + s ≠ 0`. Introduce `k h`. Establish `h1 : s = -((k : E) + 1)` using `by linear_combination h`.

Establish `h2 : c s = s` using `by rw [h1]; simp`. Apply `hs` to reduce the goal to its premises. Establish `: (2 : E) * s = 0` using `by linear_combination hc - h2`. Simplify using `using this`. Set `f : ℕ → E` to `fun k => (((k : E) + 1) + s) / (((k : E) + 1) - s)`.

Establish `hf : Function.Injective f`. Introduce `a b h`. Establish `h'` using `(div_eq_div_iff (hm a) (hm b)).1 h`. Establish `: (2 : E) * s * ((a : E) - b) = 0` using `by linear_combination -h'`. Establish `h3 : (a : E) - b = 0`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero two_ne_zero hs)`. Conclude with `h`. Conclude with `sub_eq_zero.1 h3` after adjusting the coercions. Establish `hP : γ.charpolyRev ≠ 0`.

Introduce `h`. Use `Matrix.eval_charpolyRev (M := γ)` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`. Establish `hfin : {z : E | γ.charpolyRev.IsRoot z}.Finite` using `Polynomial.finite_setOfPred_isRoot hP`.

Take `⟨z, ⟨k, rfl⟩, hz⟩` from `(Set.infinite_range_of_injective hf).exists_notMem_finite hfin`. Use `⟨f k, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hm k`. Establish `h2` using `hp k`. Simplify using `only [f, map_div₀, map_add, map_sub, map_natCast, map_one, hc, sub_neg_eq_add, ← sub_eq_add_neg]`.

Clear the denominators using the available nonvanishing facts. Introduce `h`. Establish `h'` using `(div_eq_one_iff_eq (hm k)).1 h`. Apply `hs` to reduce the goal to its premises. Establish `: (2 : E) * s = 0` using `by linear_combination h'`.

Simplify using `using this`. Introduce `h`. Apply `hz` to reduce the goal to its premises. Use `show Polynomial.eval (f k) γ.charpolyRev = 0`. Rewrite using `[← h, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]`.

Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij] <;> exact mul_comm _ _`.
-/
theorem exists_of_anti {E : Type} [Field E] [CharZero E] (c : E →+* E) (s : E) (hs : s ≠ 0) (hc : c s = -s)
    (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) : ∃ z : E, z * c z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  have hm : ∀ k : ℕ, ((k : E) + 1) - s ≠ 0 := by
    intro k h
    have h1 : s = (k : E) + 1 := by linear_combination -h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  have hp : ∀ k : ℕ, ((k : E) + 1) + s ≠ 0 := by
    intro k h
    have h1 : s = -((k : E) + 1) := by linear_combination h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  let f : ℕ → E := fun k => (((k : E) + 1) + s) / (((k : E) + 1) - s)
  have hf : Function.Injective f := by
    intro a b h
    have h' := (div_eq_div_iff (hm a) (hm b)).1 h
    have : (2 : E) * s * ((a : E) - b) = 0 := by linear_combination -h'
    have h3 : (a : E) - b = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hs)
      · exact h
    exact_mod_cast sub_eq_zero.1 h3
  have hP : γ.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := γ)
    rw [h] at this
    simp at this
  have hfin : {z : E | γ.charpolyRev.IsRoot z}.Finite := Polynomial.finite_setOfPred_isRoot hP
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finite hfin
  refine ⟨f k, ?_, ?_, ?_⟩
  · have h1 := hm k
    have h2 := hp k
    simp only [f, map_div₀, map_add, map_sub, map_natCast, map_one, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    field_simp
  · intro h
    have h' := (div_eq_one_iff_eq (hm k)).1 h
    apply hs
    have : (2 : E) * s = 0 := by linear_combination h'
    simpa using this
  · intro h
    apply hz
    show Polynomial.eval (f k) γ.charpolyRev = 0
    rw [← h, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij] <;> exact mul_comm _ _

/- English proof (translation)
Introduce `D n γ`. Establish `hs : D.host.sqrtMinusD ≠ 0`. Introduce `h`. Establish `h1` using `D.host.sqrtMinusD_sq`. Rewrite `h1` using `[h]`.

Establish `h2 : (D.host.d : D.host.E) = 0` using `by linear_combination h1`. Conclude with `D.host.hyp.2.1.ne_zero (by exact_mod_cast h2)`. Conclude with `exists_of_anti (D.host.conj : D.host.E →+* D.host.E) D.host.sqrtMinusD hs D.host.conj_sqrtMinusD n γ`.
-/
theorem exists_norm_one_det_ne_zero : ∀ (D : D7) (n : ℕ) (γ : Matrix (Fin n) (Fin n) D.host.E),
    ∃ z : D.host.E, z * D.host.conj z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  intro D n γ
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have h1 := D.host.sqrtMinusD_sq
    rw [h] at h1
    have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
    exact D.host.hyp.2.1.ne_zero (by exact_mod_cast h2)
  exact exists_of_anti (D.host.conj : D.host.E →+* D.host.E) D.host.sqrtMinusD hs D.host.conj_sqrtMinusD n γ

end GlobalTheory.NormOneScalar
