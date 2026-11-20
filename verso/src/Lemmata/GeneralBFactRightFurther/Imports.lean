import Mathlib

namespace Bl.general_b_fact_right_further

/- English proof (translation)
Introduce `n J k h i`. Establish `key : Finset.filter (fun (x : Fin n) ↦ x < J.orderEmbOfFin h i) J = (Finset.Iio i).map (J.orderEmbOfFin h).toEmbedding`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hx, hlt⟩`. Establish `hr : x ∈ Set.range (J.orderEmbOfFin h)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `hx`. Take `⟨j, rfl⟩` from `hr`.

Conclude with `⟨j, (J.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩`. Introduce and unpack `⟨j, hj, rfl⟩`. Conclude with `⟨Finset.orderEmbOfFin_mem J h j, (J.orderEmbOfFin h).lt_iff_lt.mpr hj⟩`. Rewrite using `[key, Finset.card_map, Fin.card_Iio]`.
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
