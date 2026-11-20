import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Formalism.JacquetSubsetSums.SeparationTR

noncomputable section

namespace GlobalTheory.NoFixedCharSum

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [LinearMap.sum_apply, LinearMap.zero_apply]`. Apply `h` to reduce the goal to its premises. Introduce `m hm`. Rewrite using `[map_sum]`.

Use `Fintype.sum_equiv (Equiv.mulLeft (⟨m, hm⟩ : N)) _ _ ?_` and prove the remaining obligations. Introduce `n`. Simplify using `[map_mul]`.
-/
theorem sum_rep_subgroup_eq_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N]
    (h : ∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) : ∑ n : N, τ (n : G) = 0 := by
  ext v
  simp only [LinearMap.sum_apply, LinearMap.zero_apply]
  apply h
  intro m hm
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨m, hm⟩ : N)) _ _ ?_
  intro n
  simp [map_mul]

/- English proof (translation)
Introduce `G V _ _ _ _ τ N _ h x y`. Establish `h0` using `sum_rep_subgroup_eq_zero τ N h`. Establish `: ∑ n : N, τ (x * (n : G) * y) = τ x * (∑ n : N, τ (n : G)) * τ y`. Simplify using `[Finset.mul_sum, Finset.sum_mul, map_mul]`. Rewrite using `[← map_sum, this, h0]`.

Simplify using the standard rewrite rules.
-/
theorem noFixedSum : Formalism.PacketSums.NoFixedSum := by
  intro G V _ _ _ _ τ N _ h x y
  have h0 := sum_rep_subgroup_eq_zero τ N h
  have : ∑ n : N, τ (x * (n : G) * y) = τ x * (∑ n : N, τ (n : G)) * τ y := by
    simp [Finset.mul_sum, Finset.sum_mul, map_mul]
  rw [← map_sum, this, h0]
  simp

end GlobalTheory.NoFixedCharSum
