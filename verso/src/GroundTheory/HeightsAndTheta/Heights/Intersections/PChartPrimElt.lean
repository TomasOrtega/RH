import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartPrimElt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

/- English proof (translation)
Introduce `Φ _ _ Φ' _ _ Q _ r hfin`. Use `set L := IntermediateField.adjoin Φ (Set.range r) with hL`. Take `⟨α, hα⟩` from `Field.exists_primitive_element Φ L`. Establish `hint : IsIntegral Φ α` using `IsIntegral.of_finite Φ α`. Establish `hmemL : ∀ q, r q ∈ L` using `fun q => IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩`.

Establish `halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `(IntermediateField.isAlgebraic_iff (x := (⟨r q, hmemL q⟩ : L))).1 (Algebra.IsAlgebraic.isAlgebraic _)`. Establish `hmem : (α : Φ') ∈ Algebra.adjoin Φ (Set.range r)`. Rewrite using `[← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]`.

Conclude with `α.2`. Rewrite `hmem` using `[Algebra.adjoin_range_eq_range_aeval]`. Take `⟨τ, hτ0⟩` from `hmem`. Establish `hτ : MvPolynomial.aeval r τ = (α : Φ')` using `hτ0`. Establish `hm : minpoly Φ (MvPolynomial.aeval r τ) = minpoly Φ α`.

Rewrite using `[hτ]`. Conclude with `minpoly.algHom_eq L.val Subtype.val_injective α`. Establish `hg : ∀ q, ∃ p : Φ[X], aeval α p = (⟨r q, hmemL q⟩ : L)`. Introduce `q`. Establish `h1 : (⟨r q, hmemL q⟩ : L) ∈ IntermediateField.adjoin Φ ({α} : Set L)` using `by rw [hα]; trivial`.

Rewrite `h1` using `[← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, hp⟩` from `h1`. Conclude with `⟨p, hp⟩`. Use `choose g hg using hg`. Establish `hgθ : ∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q`.

Introduce `q`. Rewrite using `[hτ, show (α : Φ') = L.val α from rfl, Polynomial.aeval_algHom_apply, hg q]`. Both sides reduce to the same expression. Establish `hirr : Irreducible (minpoly Φ (MvPolynomial.aeval r τ))`. Rewrite using `[hm]`.

Conclude with `minpoly.irreducible hint`. Use `⟨τ, g, ?_⟩` and prove the remaining obligations. Establish `hsep : IsCoprime (minpoly Φ (MvPolynomial.aeval r τ)) (derivative (minpoly Φ (MvPolynomial.aeval r τ)))` using `hirr.separable`. Take `⟨a, b, hab⟩` from `hsep`. Use `⟨b, ?_, hgθ, ⟨-a, by linear_combination hab⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hm]`. Conclude with `(Field.primitive_element_iff_minpoly_natDegree_eq Φ α).1 hα`. Apply `minpoly.dvd` to reduce the goal to its premises. Establish `hfun : (fun q => aeval (MvPolynomial.aeval r τ) (g q)) = r` using `funext hgθ`. Rewrite using `[map_sub, aeval_X, MvPolynomial.comp_aeval_apply, hfun, sub_self]`.

Introduce `q hq`. Establish `hnd : ¬ minpoly Φ (MvPolynomial.aeval r τ) ∣ g q`. Introduce and unpack `⟨c, hc⟩`. Apply `hq` to reduce the goal to its premises. Rewrite using `[← hgθ q, hc, map_mul, minpoly.aeval, zero_mul]`.

Take `⟨a', b', hab'⟩` from `(hirr.coprime_iff_not_dvd).2 hnd`. Conclude with `⟨b', ⟨-a', by linear_combination hab'⟩⟩`.
-/
theorem ChartPrimElt.proof : ChartPrimElt.Statement := by
  intro Φ _ _ Φ' _ _ Q _ r hfin
  set L := IntermediateField.adjoin Φ (Set.range r) with hL
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Φ L
  have hint : IsIntegral Φ α := IsIntegral.of_finite Φ α
  have hmemL : ∀ q, r q ∈ L := fun q => IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
  have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
    rintro _ ⟨q, rfl⟩
    exact (IntermediateField.isAlgebraic_iff (x := (⟨r q, hmemL q⟩ : L))).1
      (Algebra.IsAlgebraic.isAlgebraic _)
  have hmem : (α : Φ') ∈ Algebra.adjoin Φ (Set.range r) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact α.2
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  obtain ⟨τ, hτ0⟩ := hmem
  have hτ : MvPolynomial.aeval r τ = (α : Φ') := hτ0
  have hm : minpoly Φ (MvPolynomial.aeval r τ) = minpoly Φ α := by
    rw [hτ]
    exact minpoly.algHom_eq L.val Subtype.val_injective α
  have hg : ∀ q, ∃ p : Φ[X], aeval α p = (⟨r q, hmemL q⟩ : L) := by
    intro q
    have h1 : (⟨r q, hmemL q⟩ : L) ∈ IntermediateField.adjoin Φ ({α} : Set L) := by rw [hα]; trivial
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨p, hp⟩ := h1
    exact ⟨p, hp⟩
  choose g hg using hg
  have hgθ : ∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q := by
    intro q
    rw [hτ, show (α : Φ') = L.val α from rfl, Polynomial.aeval_algHom_apply, hg q]
    rfl
  have hirr : Irreducible (minpoly Φ (MvPolynomial.aeval r τ)) := by
    rw [hm]
    exact minpoly.irreducible hint
  refine ⟨τ, g, ?_⟩
  have hsep : IsCoprime (minpoly Φ (MvPolynomial.aeval r τ))
      (derivative (minpoly Φ (MvPolynomial.aeval r τ))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  refine ⟨b, ?_, hgθ, ⟨-a, by linear_combination hab⟩, ?_, ?_⟩
  · rw [hm]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq Φ α).1 hα
  · apply minpoly.dvd
    have hfun : (fun q => aeval (MvPolynomial.aeval r τ) (g q)) = r := funext hgθ
    rw [map_sub, aeval_X, MvPolynomial.comp_aeval_apply, hfun, sub_self]
  · intro q hq
    have hnd : ¬ minpoly Φ (MvPolynomial.aeval r τ) ∣ g q := by
      rintro ⟨c, hc⟩
      apply hq
      rw [← hgθ q, hc, map_mul, minpoly.aeval, zero_mul]
    obtain ⟨a', b', hab'⟩ := (hirr.coprime_iff_not_dvd).2 hnd
    exact ⟨b', ⟨-a', by linear_combination hab'⟩⟩

end GroundTheory.Heights₂.Heights.Inter
