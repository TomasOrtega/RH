import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

/- English proof (translation)
Introduce `Λ _ N hN M h0 _ hlaw t ht`. Distinguish the cases in `hQ : t ∈ Λ`. Conclude with `h0 t hQ`. Establish `key : ∀ k : ℕ, M ((k:ℂ) * t) = (k:ℝ)^2 * M t ∧ M (((k:ℂ)+1) * t) = ((k:ℝ)+1)^2 * M t`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `[h0 0 (zero_mem Λ)]`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Use `⟨by push_cast; exact ih.2, ?_⟩` and prove the remaining obligations. Establish `hmem : (N:ℂ) * (((k:ℂ)+1) * t) ∈ Λ`. Establish `e : (N:ℂ) * (((k:ℂ)+1) * t) = (k+1 : ℕ) • ((N:ℂ) * t)`. Rewrite using `[nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `AddSubgroup.nsmul_mem Λ ht _`. Establish `h` using `hlaw (((k:ℂ)+1) * t) t hmem ht hQ`.

Establish `e1 : ((k:ℂ)+1) * t + t = ((k:ℂ)+1+1) * t` using `by ring`. Establish `e2 : ((k:ℂ)+1) * t - t = (k:ℂ) * t` using `by ring`. Rewrite `h` using `[e1, e2, ih.1, ih.2]`. Use `push_cast`. Take the linear combination `h`.

Establish `h1` using `(key N).1`. Rewrite `h1` using `[h0 _ ht]`. Establish `hN' : (N:ℝ)^2 ≠ 0` using `by positivity`. Conclude with `(mul_eq_zero.mp h1.symm).resolve_left hN'`.
-/
theorem GlobalTheory.torsion_parallelogram_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  intro Λ _ N hN M h0 _ hlaw t ht
  by_cases hQ : t ∈ Λ
  · exact h0 t hQ
  have key : ∀ k : ℕ, M ((k:ℂ) * t) = (k:ℝ)^2 * M t ∧
      M (((k:ℂ)+1) * t) = ((k:ℝ)+1)^2 * M t := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [h0 0 (zero_mem Λ)]
      · simp
    | succ k ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have hmem : (N:ℂ) * (((k:ℂ)+1) * t) ∈ Λ := by
        have e : (N:ℂ) * (((k:ℂ)+1) * t) = (k+1 : ℕ) • ((N:ℂ) * t) := by
          rw [nsmul_eq_mul]; push_cast; ring
        rw [e]; exact AddSubgroup.nsmul_mem Λ ht _
      have h := hlaw (((k:ℂ)+1) * t) t hmem ht hQ
      have e1 : ((k:ℂ)+1) * t + t = ((k:ℂ)+1+1) * t := by ring
      have e2 : ((k:ℂ)+1) * t - t = (k:ℂ) * t := by ring
      rw [e1, e2, ih.1, ih.2] at h
      push_cast
      linear_combination h
  have h1 := (key N).1
  rw [h0 _ ht] at h1
  have hN' : (N:ℝ)^2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h1.symm).resolve_left hN'
