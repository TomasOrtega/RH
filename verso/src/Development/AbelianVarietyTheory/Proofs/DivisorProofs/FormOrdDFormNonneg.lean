import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair.Place

/- English proof (translation)
Introduce `k K _ _ _ c n x E hx hmem`. Set `y : Fin n → E.ring` to `fun i => ⟨x i, hmem i⟩`. Establish `e₁ : E.toRat n (dForm E.const y) = dForm c x`. Conclude with `formMap_dForm (α := E.const) (β := c) E.ring.subtype rfl y`. Take `⟨ω, hω⟩` from `E.exists_isFreeGen hx`.

Take `⟨a, ha⟩` from `hω.2 (dForm E.const y)`. Rewrite using `[← e₁, ← ha, map_smulₛₗ]`. Distinguish the cases in `h0 : (a : K) = 0`. Establish `hz : (E.ring.subtype a) • E.toRat n ω = 0`. Express the relevant statement in the definitionally equal form `(a : K) • _ = 0`.

Rewrite using `[h0, zero_smul]`. Rewrite using `[hz, formOrd, dif_neg]`. Introduce and unpack `⟨b, hb⟩`. Conclude with `hb.ne_zero rfl`. Express the relevant statement in the definitionally equal form `0 ≤ E.formOrd ((a : K) • E.toRat n ω)`.

Rewrite using `[E.formOrd_smul_toRat hω h0]`. Conclude with `(E.ord_nonneg_iff h0).2 a.2`.
-/
theorem formOrd_dForm_nonneg : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K) (E : Place c),
  TrBasis c x → (∀ i, x i ∈ E.ring) → 0 ≤ E.formOrd (dForm c x) := by
  intro k K _ _ _ c n x E hx hmem
  let y : Fin n → E.ring := fun i => ⟨x i, hmem i⟩
  have e₁ : E.toRat n (dForm E.const y) = dForm c x := by
    exact formMap_dForm (α := E.const) (β := c) E.ring.subtype rfl y
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hx
  obtain ⟨a, ha⟩ := hω.2 (dForm E.const y)
  rw [← e₁, ← ha, map_smulₛₗ]
  by_cases h0 : (a : K) = 0
  · have hz : (E.ring.subtype a) • E.toRat n ω = 0 := by
      change (a : K) • _ = 0
      rw [h0, zero_smul]
    rw [hz, formOrd, dif_neg]
    rintro ⟨b, hb⟩
    exact hb.ne_zero rfl
  · change 0 ≤ E.formOrd ((a : K) • E.toRat n ω)
    rw [E.formOrd_smul_toRat hω h0]
    exact (E.ord_nonneg_iff h0).2 a.2

end GlobalTheory.FieldPair.Place
