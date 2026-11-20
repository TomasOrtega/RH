import Mathlib

namespace GlobalTheory.AlgHomEqEval

/- English proof (translation)
Introduce `K _ P _ _ θ`. Establish `hsum : ∑ p, (Pi.single p (1:K) : P → K) = 1`. Use extensionality with `x`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `h1 : ∑ p, θ (Pi.single p 1) = 1`.

Rewrite using `[← map_sum, hsum, map_one]`. Choose the witnesses or unpack the hypotheses as in `⟨p, -, hp⟩ : ∃ p ∈ Finset.univ, θ (Pi.single p 1) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Rewrite `h1` using `[Finset.sum_eq_zero h]`.

Conclude with `zero_ne_one h1`. Use `⟨p, fun z => ?_⟩` and prove the remaining obligations. Establish `hz : z * Pi.single p 1 = (algebraMap K (P → K) (z p)) * Pi.single p 1`. Use extensionality with `x`. Distinguish the cases in `hx : x = p`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hx]`. Establish `h2` using `congrArg θ hz`. Rewrite `h2` using `[map_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]`.

Conclude with `mul_right_cancel₀ hp h2`.
-/
theorem algHom_eq_eval : ∀ {K : Type} [inst : Field K] {P : Type} [Fintype P] [DecidableEq P]
    (θ : (P → K) →ₐ[K] K), ∃ (p : P), ∀ (z : P → K), (θ : (P → K) → K) z = z p := by
  intro K _ P _ _ θ
  have hsum : ∑ p, (Pi.single p (1:K) : P → K) = 1 := by
    ext x; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : ∑ p, θ (Pi.single p 1) = 1 := by
    rw [← map_sum, hsum, map_one]
  obtain ⟨p, -, hp⟩ : ∃ p ∈ Finset.univ, θ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    rw [Finset.sum_eq_zero h] at h1
    exact zero_ne_one h1
  refine ⟨p, fun z => ?_⟩
  have hz : z * Pi.single p 1 = (algebraMap K (P → K) (z p)) * Pi.single p 1 := by
    ext x
    by_cases hx : x = p
    · subst hx; simp
    · simp [Pi.single_apply, hx]
  have h2 := congrArg θ hz
  rw [map_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h2
  exact mul_right_cancel₀ hp h2

end GlobalTheory.AlgHomEqEval
