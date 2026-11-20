import Mathlib

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

/- English proof (translation)
Take `⟨V, hV⟩ : ∃ V : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ, V = Matrix.vandermonde fun s => ((s : ℕ) : ℂ)` from `⟨_, rfl⟩`. Establish `hdet : IsUnit V.det`. Rewrite using `[isUnit_iff_ne_zero, hV, Matrix.det_vandermonde_ne_zero_iff]`. Introduce `i j hij`. Simplify `hij` using `[Fin.ext_iff]`.

Establish `hinv : V⁻¹ * V = 1` using `Matrix.nonsing_inv_mul V hdet`. Use `⟨fun q s => (V⁻¹ : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q s, fun E _ _ a q => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Establish `hrow : ∀ j : Fin (Q + 1), ∑ s : Fin (Q + 1), V⁻¹ q s * ((s : ℕ) : ℂ) ^ (j : ℕ) = (1 : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q j`. Introduce `j`.

Rewrite using `[← hinv, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[hV, Matrix.vandermonde_apply]`. Repeatedly rewrite using `[Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul, hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem vander' (Q : ℕ) : ∃ lam : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ (E : Type) [AddCommGroup E] [Module ℂ E]
    (a : Fin (Q + 1) → E) (q : Fin (Q + 1)),
    a q = ∑ s : Fin (Q + 1), lam q s • ∑ j : Fin (Q + 1), (((s : ℕ) : ℂ) ^ (j : ℕ)) • a j := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ,
      V = Matrix.vandermonde fun s => ((s : ℕ) : ℂ) := ⟨_, rfl⟩
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    simpa [Fin.ext_iff] using hij
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  refine ⟨fun q s => (V⁻¹ : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q s, fun E _ _ a q => ?_⟩
  beta_reduce
  have hrow : ∀ j : Fin (Q + 1),
      ∑ s : Fin (Q + 1), V⁻¹ q s * ((s : ℕ) : ℂ) ^ (j : ℕ) = (1 : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q j := by
    intro j
    rw [← hinv, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [hV, Matrix.vandermonde_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

end Formalism.FourierDecayAlt.P.NormalFormRelations
