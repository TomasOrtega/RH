import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ d h2 hd`. Use `haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩`. Use `haveI : IsGalois ℚ K := inferInstance`. Establish `hcard : Nat.card (K ≃ₐ[ℚ] K) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h2]`. Take `⟨σ, hσ, huniq⟩` from `(Nat.card_eq_two_iff' (1 : K ≃ₐ[ℚ] K)).1 hcard`.

Establish `huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, σ}`. Use extensionality with `y`. Simplify using `only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]`. Distinguish the cases in `hy : y = 1`. Conclude with `Or.inl hy`.

Conclude with `Or.inr (huniq y hy)`. Establish `htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x`. Introduce `x`. Rewrite using `[_root_.trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hσ)]`. Both sides reduce to the same expression.

Set `e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2` to `Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (integralBasis K), h2])`. Set `b : Fin 2 → K` to `fun i => integralBasis K (e.symm i)`. Establish `hb : ⇑(integralBasis K) ∘ ⇑e.symm = b` using `rfl`. Establish `key : algebraMap ℚ K (discr K : ℚ) = (b 0 * σ (b 1) - b 1 * σ (b 0)) ^ 2`. Rewrite using `[coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, hb, Algebra.discr_def, Matrix.det_fin_two]`.

Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, htr]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨b 0 * σ (b 1) - b 1 * σ (b 0), ?_⟩` and prove the remaining obligations. Rewrite using `[← key, hd]`. Use `push_cast`.

Simplify using the standard rewrite rules.
-/
theorem exists_sq_eq_neg_of_discr_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  classical
  intro K _ _ d h2 hd
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := inferInstance
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[ℚ] K)).1 hcard
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, σ} := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hy : y = 1
    · exact Or.inl hy
    · exact Or.inr (huniq y hy)
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x := by
    intro x
    rw [_root_.trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hσ)]
    rfl
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (integralBasis K), h2])
  let b : Fin 2 → K := fun i => integralBasis K (e.symm i)
  have hb : ⇑(integralBasis K) ∘ ⇑e.symm = b := rfl
  have key : algebraMap ℚ K (discr K : ℚ) = (b 0 * σ (b 1) - b 1 * σ (b 0)) ^ 2 := by
    rw [coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, hb, Algebra.discr_def,
      Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, htr]
    ring
  refine ⟨b 0 * σ (b 1) - b 1 * σ (b 0), ?_⟩
  rw [← key, hd]
  push_cast
  simp

end GlobalTheory
