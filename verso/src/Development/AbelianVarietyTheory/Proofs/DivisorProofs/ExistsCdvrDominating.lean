import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.DvrDom

/- English proof (translation)
Introduce `R _ _ _ _ _`. Distinguish the cases in `hR : IsField R`. Use `letI : Field R := hR.toField`. Establish `hC : Function.Injective (PowerSeries.C (R` using `R)) := PowerSeries.C_injective`. Establish `: CharZero (PowerSeries R)` using `charZero_of_injective_ringHom hC`.

Establish `hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries R)) (PowerSeries R)` using `by first`. Consider the case `infer_instance`. Consider the case `(rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)`. Establish `hl : IsLocalHom (PowerSeries.C (R` using `R)) := by`. Prove the components needed by the constructor for the conclusion.

Introduce `a ha`. Distinguish the cases in `h0 : a = 0`. Substitute `h0` using the available equality. Simplify using `at ha`. Conclude with `isUnit_iff_ne_zero.mpr h0`.

Conclude with `⟨PowerSeries R, inferInstance, inferInstance, inferInstance, PowerSeries.C (R := R), (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, this⟩, hC, hl⟩`. Take `⟨O, _, hO, hO', hO'', φ, h1, h2⟩` from `GlobalTheory.exists_complete_discreteValuationRing_dominating (R := R) hR`. Establish `: CharZero O` using `charZero_of_injective_ringHom h1`. Conclude with `⟨O, inferInstance, hO, inferInstance, φ, (GlobalTheory.LN.cDvr_iff _).2 ⟨hO', hO'', this⟩, h1, h2⟩`.
-/
theorem exists_cdvr_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ IsLocalHom φ := by
  intro R _ _ _ _ _
  by_cases hR : IsField R
  · letI : Field R := hR.toField
    have hC : Function.Injective (PowerSeries.C (R := R)) := PowerSeries.C_injective
    have : CharZero (PowerSeries R) := charZero_of_injective_ringHom hC
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries R)) (PowerSeries R) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    have hl : IsLocalHom (PowerSeries.C (R := R)) := by
      constructor
      intro a ha
      by_cases h0 : a = 0
      · subst h0; simp at ha
      · exact isUnit_iff_ne_zero.mpr h0
    exact ⟨PowerSeries R, inferInstance, inferInstance, inferInstance, PowerSeries.C (R := R),
      (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, this⟩, hC, hl⟩
  · obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating (R := R) hR
    have : CharZero O := charZero_of_injective_ringHom h1
    exact ⟨O, inferInstance, hO, inferInstance, φ, (GlobalTheory.LN.cDvr_iff _).2 ⟨hO', hO'', this⟩, h1, h2⟩

end GlobalTheory.DvrDom
