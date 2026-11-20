import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem eq_of_chartHom_eq {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type}
    [CommRing S] (c c' : Sp S ⟶ Y) (hc : c ⁻¹ᵁ V = ⊤) (hc' : c' ⁻¹ᵁ V = ⊤)
    (e : ∀ x, chartHom V c hc x = chartHom V c' hc' x) : c = c' := by
  have e₁ : c.appLE V ⊤ hc.ge = c'.appLE V ⊤ hc'.ge := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of S)).hom]
    exact CommRingCat.hom_ext (RingHom.ext e)
  have a := IsAffineOpen.SpecMap_appLE_fromSpec c hV (isAffineOpen_top (Sp S)) hc.ge
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec c' hV (isAffineOpen_top (Sp S)) hc'.ge
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem combIn_unique : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by
  intro Y V hV S _ ι _ u c c' w a h h'
  obtain ⟨hu, hc, hw, e⟩ := h
  obtain ⟨hu', hc', hw', e'⟩ := h'
  refine eq_of_chartHom_eq hV c c' hc hc' fun x => ?_
  rw [e x, e' x]

end GlobalTheory.SecGlue
