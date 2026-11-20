import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide

namespace GlobalTheory

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Simplify using the standard rewrite rules.
-/
theorem orbK_eq_zero_of_charpoly_not_separable (G : Type) [Group G] (k : Type) [Field k] (n : ℕ)
    (π : G →* GL (Fin n) k) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hf : ∀ g, f g ≠ 0 → ((π g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (hδ : ¬ ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K δ f = 0 := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  have hz : ∀ x : G, f (x⁻¹ * δ * x) = 0 := by
    intro x
    by_contra h
    apply hδ
    have hs := hf _ h
    have hc : ((π (x⁻¹ * δ * x) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly
        = ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
        Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rwa [hc] at hs
  simp [hz]

end GlobalTheory
