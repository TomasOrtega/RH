import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

/- English proof (translation)
Introduce `N _ r R hs`. Set `F : ℤ → ℂ` to `fun t => if (t : ZMod N) = r then R t else 0`. Set `g : ℤ → ℤ` to `fun n => (r.val : ℤ) + n * N`. Establish `hN : (N : ℤ) ≠ 0` using `by exact_mod_cast NeZero.ne N`. Establish `hg : Function.Injective g`.

Introduce `a b h`. Simplify using `only [g] at h`. Conclude with `mul_right_cancel₀ hN (add_left_cancel h)`. Establish `hz : ∀ t ∉ Set.range g, F t = 0`. Introduce `t ht`.

Simplify using `only [F]`. Rewrite using `[if_neg]`. Introduce `h`. Apply `ht` to reduce the goal to its premises. Establish `h2 : ((t - (r.val : ℤ) : ℤ) : ZMod N) = 0`.

Use `push_cast`. Rewrite using `[h, ZMod.natCast_zmod_val, sub_self]`. Take `⟨k, hk⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2`. Conclude with `⟨k, by simp only [g]; linear_combination -hk⟩`. Establish `hFg : F ∘ g = fun n : ℤ => R ((r.val : ℤ) + n * N)`.

Use function extensionality and compare the values at `n`. Simplify using `[F, g]`. Establish `hH : HasSum F (∑' n : ℤ, R ((r.val : ℤ) + n * N))`. Rewrite using `[← hg.hasSum_iff hz, hFg]`. Conclude with `hs.hasSum`.

Rewrite using `[← hH.tsum_eq, tsum_int_eq_zero_add_tsum_pnat hH.summable]`. Use `congr 1`. Use `congr 1`. Simplify using `only [F, Int.cast_zero, eq_comm]`. Use `tsum_congr fun d => ?_` and prove the remaining obligations.

Simplify using `only [F, Int.cast_natCast]`. Use `tsum_congr fun d => ?_` and prove the remaining obligations. Simplify using `only [F, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg]`.
-/
theorem tsum_residue_class_split : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (R : ℤ → ℂ), Summable (fun n : ℤ => R ((r.val : ℤ) + n * N)) → ∑' n : ℤ, R ((r.val : ℤ) + n * N) = (if r = 0 then R 0 else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = r then R ((d : ℕ) : ℤ) else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = -r then R (-((d : ℕ) : ℤ)) else 0) := by
  intro N _ r R hs
  classical
  let F : ℤ → ℂ := fun t => if (t : ZMod N) = r then R t else 0
  let g : ℤ → ℤ := fun n => (r.val : ℤ) + n * N
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hg : Function.Injective g := by
    intro a b h
    simp only [g] at h
    exact mul_right_cancel₀ hN (add_left_cancel h)
  have hz : ∀ t ∉ Set.range g, F t = 0 := by
    intro t ht
    simp only [F]
    rw [if_neg]
    intro h
    apply ht
    have h2 : ((t - (r.val : ℤ) : ℤ) : ZMod N) = 0 := by
      push_cast
      rw [h, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
    exact ⟨k, by simp only [g]; linear_combination -hk⟩
  have hFg : F ∘ g = fun n : ℤ => R ((r.val : ℤ) + n * N) := by
    funext n
    simp [F, g]
  have hH : HasSum F (∑' n : ℤ, R ((r.val : ℤ) + n * N)) := by
    rw [← hg.hasSum_iff hz, hFg]
    exact hs.hasSum
  rw [← hH.tsum_eq, tsum_int_eq_zero_add_tsum_pnat hH.summable]
  congr 1
  · congr 1
    · simp only [F, Int.cast_zero, eq_comm]
    · refine tsum_congr fun d => ?_
      simp only [F, Int.cast_natCast]
  · refine tsum_congr fun d => ?_
    simp only [F, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg]

end GlobalTheory.WpFam
