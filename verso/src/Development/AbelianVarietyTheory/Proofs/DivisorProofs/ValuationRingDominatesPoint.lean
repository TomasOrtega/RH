import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_valuationRing_dominating_geo {P : Type} [CommRing P] (t t' : PrimeSpectrum P) (htt : t ≤ t') :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : ValuationRing R) (_ : Algebra R (Cell.GeoF t))
      (_ : IsFractionRing R (Cell.GeoF t)) (χR : P →+* R),
      (algebraMap R (Cell.GeoF t)).comp χR = Cell.geoHom t ∧
        RingHom.ker ((IsLocalRing.residue R).comp χR) = t'.asIdeal := by
  classical
  have hunit : ∀ y : t'.asIdeal.primeCompl, IsUnit (Cell.geoHom t (y : P)) := by
    intro y
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    have hy : (y : P) ∈ RingHom.ker (Cell.geoHom t) := h0
    rw [Cell.ker_geoHom] at hy
    exact y.2 (htt hy)
  let f : Localization.AtPrime t'.asIdeal →+* Cell.GeoF t :=
    IsLocalization.lift (M := t'.asIdeal.primeCompl) hunit
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let g : Localization.AtPrime t'.asIdeal →+* V := f.codRestrict V.toSubring hV
  haveI : IsLocalHom g := hloc
  let χ : P →+* V := g.comp (algebraMap P (Localization.AtPrime t'.asIdeal))
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, χ, ?_, ?_⟩
  · ext x
    show f (algebraMap P (Localization.AtPrime t'.asIdeal) x) = Cell.geoHom t x
    exact IsLocalization.lift_eq _ x
  · ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    show ¬ IsUnit (g (algebraMap P (Localization.AtPrime t'.asIdeal) x)) ↔ _
    rw [isUnit_map_iff g, IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime t'.asIdeal) t'.asIdeal x]
    simp [Ideal.primeCompl]

end GlobalTheory.ShFam.Cell
