import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

/- English proof (translation)
Establish `hna : Summable fun n => ‖a n * e n‖` using `summable_norm_iff.mpr ha.summable`. Establish `hnb : Summable fun n => ‖b n * e n‖` using `summable_norm_iff.mpr hb.summable`. Establish `hS : HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (a p.1 * e p.1) * (b p.2 * e p.2)) (x * y)`. Rewrite using `[← ha.tsum_eq, ← hb.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]`. Conclude with `(summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm.hasSum`.

Use `hS using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Rewrite using `[conv, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[← hp, he]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hasSum_conv_mul_of_multiplicative {a b : ℕ → ℂ} {e : ℕ → ℂ} {x y : ℂ}
    (he : ∀ m n, e (m + n) = e m * e n)
    (ha : HasSum (fun n => a n * e n) x) (hb : HasSum (fun n => b n * e n) y) :
    HasSum (fun n => conv a b n * e n) (x * y) := by
  have hna : Summable fun n => ‖a n * e n‖ := summable_norm_iff.mpr ha.summable
  have hnb : Summable fun n => ‖b n * e n‖ := summable_norm_iff.mpr hb.summable
  have hS : HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (a p.1 * e p.1) * (b p.2 * e p.2)) (x * y) := by
    rw [← ha.tsum_eq, ← hb.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm.hasSum
  convert hS using 1
  funext n
  rw [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, he]
  ring

/- English proof (translation)
Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mvExp_add_character_germs (N : ℕ) (τ : ℍ) (m n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m + n : ℕ) : ℂ) * τ / N) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / N) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / N) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `τ` and use `hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)`.
-/
theorem HasQ.mul_conv {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ * g τ) (conv a b) :=
  fun τ => hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

/- English proof (translation)
Introduce `N f g a b _ hf hg τ`. Conclude with `hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)`.
-/
theorem hasQ_mul_conv : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b →
    HasQ N (fun τ => f τ * g τ) (conv a b) := by
  intro N f g a b _ hf hg τ
  exact hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

end GlobalTheory.QFam
