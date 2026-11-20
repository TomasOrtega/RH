import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

/- English proof (translation)
Introduce `N M f a hN hM h τ`. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hM' : (M : ℂ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hinj : Function.Injective (fun k : ℕ => M * k)` using `fun x y hxy => Nat.eq_of_mul_eq_mul_left hM hxy`. Use `(hinj.hasSum_iff ?_).mp ?_` and prove the remaining obligations.

Introduce `n hn`. Simplify using `only [spread]`. Rewrite using `[if_neg, zero_mul]`. Introduce and unpack `⟨k, rfl⟩`. Conclude with `hn ⟨k, rfl⟩`.

Use `h τ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left k hM]`. Use `congr 2`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem hasQ_mul_spread : ∀ (N M : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → 0 < M → HasQ N f a →
    HasQ (N * M) f (spread M a) := by
  intro N M f a hN hM h τ
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hinj : Function.Injective (fun k : ℕ => M * k) := fun x y hxy =>
    Nat.eq_of_mul_eq_mul_left hM hxy
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hn ⟨k, rfl⟩
  · convert h τ using 1
    funext k
    simp only [Function.comp, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left k hM]
    congr 2
    push_cast
    field_simp

end GlobalTheory.QFam
