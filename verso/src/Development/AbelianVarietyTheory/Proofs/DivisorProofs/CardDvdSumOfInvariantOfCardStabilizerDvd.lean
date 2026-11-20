import Mathlib

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_dvd_sum_of_invariant_of_card_stabilizer_dvd (G X : Type) [AddGroup G] [Finite G]
    [Fintype X] [AddAction G X] (h : X → ℤ) (hinv : ∀ (g : G) (x : X), h (g +ᵥ x) = h x)
    (hdvd : ∀ x, (Nat.card (AddAction.stabilizer G x) : ℤ) ∣ h x) :
    (Nat.card G : ℤ) ∣ ∑ x, h x := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun x : X => (Quotient.mk (AddAction.orbitRel G X) x)) (f := h)]
  refine Finset.dvd_sum fun q _ => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hconst : ∀ y ∈ Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y = Quotient.mk (AddAction.orbitRel G X) x),
      h y = h x := by
    intro y hy
    have hy' := Quotient.exact (Finset.mem_filter.mp hy).2
    obtain ⟨g, rfl⟩ : y ∈ AddAction.orbit G x := AddAction.orbitRel_apply.mp hy'
    exact hinv g x
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y
        = Quotient.mk (AddAction.orbitRel G X) x)).card = Nat.card (AddAction.orbit G x) := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Quotient.eq]
    exact AddAction.orbitRel_apply
  have hG : Nat.card G = Nat.card (AddAction.orbit G x) * Nat.card (AddAction.stabilizer G x) := by
    rw [Nat.card_congr (AddAction.orbitEquivQuotientStabilizer G x)]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  rw [hcard, hG, Nat.cast_mul]
  exact mul_dvd_mul_left _ (hdvd x)

end GlobalTheory
