import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringExtendingRingHomStatement
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `W L _ _ _ _ _ _ k _ _ x`. Use `set j' : W →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) with hj'`. Establish `hinj : Function.Injective j'` using `(algebraMap L (AlgebraicClosure L)).injective.comp (IsFractionRing.injective W L)`. Use `set g : W →+* k := (Spec.preimage x).hom with hg`. Take `⟨U, hU, h, hh⟩` from `GlobalTheory.T.exists_valuationSubring_extending_ringHom W (AlgebraicClosure L) k j' hinj g`.

Use `⟨U, j'.codRestrict U.toSubring hU, h, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Both sides reduce to the same expression. Establish `hcomp : h.comp (j'.codRestrict U.toSubring hU) = g`. Use extensionality with `w`.

Conclude with `hh w`. Establish `hx : x = Spec.map (Spec.preimage x)` using `(Spec.map_preimage x).symm`. Rewrite using `[hx]`. Simplify using `only [spMap, Sp]`. Rewrite using `[← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `w`. Express the relevant statement in the definitionally equal form `g w = h (j'.codRestrict U.toSubring hU w)`. Rewrite using `[← hcomp]`. Both sides reduce to the same expression.
-/
theorem geomPoint_factors_valuationSubring_algClosure :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
      [IsFractionRing W L] (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W),
      ∃ (U : ValuationSubring (AlgebraicClosure L)) (j : W →+* U) (h : U →+* k),
        (algebraMap U (AlgebraicClosure L)).comp j = (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) ∧
          x = spMap h ≫ spMap j := by
  intro W L _ _ _ _ _ _ k _ _ x
  set j' : W →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) with hj'
  have hinj : Function.Injective j' :=
    (algebraMap L (AlgebraicClosure L)).injective.comp (IsFractionRing.injective W L)
  set g : W →+* k := (Spec.preimage x).hom with hg
  obtain ⟨U, hU, h, hh⟩ := GlobalTheory.T.exists_valuationSubring_extending_ringHom W (AlgebraicClosure L) k j' hinj g
  refine ⟨U, j'.codRestrict U.toSubring hU, h, ?_, ?_⟩
  · ext w; rfl
  · have hcomp : h.comp (j'.codRestrict U.toSubring hU) = g := by
      ext w; exact hh w
    have hx : x = Spec.map (Spec.preimage x) := (Spec.map_preimage x).symm
    rw [hx]
    simp only [spMap, Sp]
    rw [← Spec.map_comp]
    congr 1
    ext w
    change g w = h (j'.codRestrict U.toSubring hU w)
    rw [← hcomp]; rfl

end GlobalTheory
