import Formalism.FockGram.StatementFock

open Finset MvPolynomial

namespace Formalism.E

section
variable {R τ : Type*} [CommRing R] [StarRing R]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem fock_eq_sum_of_subset (f g : MvPolynomial τ R) (s : Finset (τ →₀ ℕ))
    (h : f.support ⊆ s) :
    fock f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R) := by
  classical
  unfold fock
  refine Finset.sum_subset h ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fock_add_left (f f' g : MvPolynomial τ R) : fock (f + f') g = fock f g + fock f' g := by
  classical
  rw [fock_eq_sum_of_subset (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fock_eq_sum_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    fock_eq_sum_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fock_smul_left (c : R) (f g : MvPolynomial τ R) : fock (c • f) g = c * fock f g := by
  classical
  rw [fock_eq_sum_of_subset (c • f) g f.support MvPolynomial.support_smul,
    fock_eq_sum_of_subset f g f.support (Finset.Subset.refl _), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fock_add_right (f g g' : MvPolynomial τ R) : fock f (g + g') = fock f g + fock f g' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add, star_add]; ring)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fock_smul_right (c : R) (f g : MvPolynomial τ R) :
    fock f (c • g) = star c * fock f g := by
  unfold fock
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by
    rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
    ring)

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem existsSesqForm : FockSesq := by
  intro R τ _ _
  exact ⟨LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) (fun f g => fock f g)
    (fun f f' g => fock_add_left f f' g) (fun c f g => by rw [fock_smul_left]; rfl)
    (fun f g g' => fock_add_right f g g') (fun c f g => by rw [fock_smul_right]; rfl),
    fun f g => rfl⟩

end Formalism.E
