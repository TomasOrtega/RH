import Mathlib

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : X => (Quotient.mk (AddAction.orbitRel G X) x)) (f := h)]`. Use `Finset.dvd_sum fun q _ => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Quotient.exists_rep q`. Establish `hconst : ∀ y ∈ Finset.univ.filter (fun y : X => Quotient.mk (AddAction.orbitRel G X) y = Quotient.mk (AddAction.orbitRel G X) x), h y = h x`. Introduce `y hy`.

Establish `hy'` using `Quotient.exact (Finset.mem_filter.mp hy).2`. Take `⟨g, rfl⟩ : y ∈ AddAction.orbit G x` from `AddAction.orbitRel_apply.mp hy'`. Conclude with `hinv g x`. Rewrite using `[Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]`. Establish `hcard : (Finset.univ.filter (fun y : X => Quotient.mk (AddAction.orbitRel G X) y = Quotient.mk (AddAction.orbitRel G X) x)).card = Nat.card (AddAction.orbit G x)`.

Rewrite using `[← Nat.card_eq_finsetCard]`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[Quotient.eq]`. Conclude with `AddAction.orbitRel_apply`.

Establish `hG : Nat.card G = Nat.card (AddAction.orbit G x) * Nat.card (AddAction.stabilizer G x)`. Rewrite using `[Nat.card_congr (AddAction.orbitEquivQuotientStabilizer G x)]`. Conclude with `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _`. Rewrite using `[hcard, hG, Nat.cast_mul]`. Conclude with `mul_dvd_mul_left _ (hdvd x)`.
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
