import Mathlib

namespace Bl.general_b_fact_right_further

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ {n : Nat} (J : Finset.{0} (Fin n)) {k : Nat} (h : Eq.{1} (Finset.card.{0} J) k) (i : Fin k),
  Eq.{1}
    (Finset.card.{0}
      (Finset.filter.{0} (fun (x : Fin n) ↦ LT.lt.{0} x (DFunLike.coe.{1, 1, 1} (Finset.orderEmbOfFin.{0} J h) i)) J))
    i.val := by
  intro n J k h i
  have key : Finset.filter (fun (x : Fin n) ↦ x < J.orderEmbOfFin h i) J
      = (Finset.Iio i).map (J.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      have hr : x ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, (J.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem J h j, (J.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  rw [key, Finset.card_map, Fin.card_Iio]

end Bl.general_b_fact_right_further
