import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_dotProduct_eq_one :
    ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  intro k _ _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  have hax₀ : a ⬝ᵥ Pi.single i (a i)⁻¹ = 1 := by
    rw [dotProduct_single, mul_inv_cancel₀ hi]
  have hfib : ∀ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card =
      (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card := by
    intro c
    apply Finset.card_bij' (fun x _ => x + (1 - c) • Pi.single i (a i)⁻¹)
      (fun x _ => x - (1 - c) • Pi.single i (a i)⁻¹)
    case hi =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_add, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case hj =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_sub, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case left_inv =>
      intro x _
      simp
    case right_inv =>
      intro x _
      simp
  have htot : (Finset.univ : Finset (Fin (n + 1) → k)).card =
      ∑ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (a ⬝ᵥ x))
  have hcard : (Finset.univ : Finset (Fin (n + 1) → k)).card = Fintype.card k ^ (n + 1) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [← hcard, htot, Finset.sum_congr rfl (fun c _ => hfib c), Finset.sum_const,
    Finset.card_univ, smul_eq_mul]

end GlobalTheory.CompanionTheory.GapOpCount
