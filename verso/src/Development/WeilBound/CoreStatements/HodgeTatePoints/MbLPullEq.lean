import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPulllocCentre

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LPullEq

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem pull_eq_pullLoc_of_dominates : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type)
    [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F]
    (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i →
      L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' := by
  intro o _ Ω _ _ κ _ x M E _ _ L X' Ω' _ ξ' i F _ _ j f hL hd
  have dl := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ X' Ω' ξ' i f hd
  refine ⟨?_, fun p' => ?_⟩
  · funext p'
    obtain ⟨h, hc⟩ := dl p'
    rw [PositivityTheory.HtPt.Mb.pullloc_centre o Ω κ x M E L X' Ω' ξ' i F j ⟨f p'.1, h⟩ p' hL hc]
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨h, e, he, rfl⟩
  · obtain ⟨h, h1, -⟩ := dl p'
    obtain ⟨c, hc⟩ := M.tie.cover ⟨f p'.1, h⟩
    exact ⟨c, hc.1, fun a ha => h1 a (((M.tie.ring c hc.1) a).1 ha _ hc)⟩

end PositivityTheory.HtPt.Mb.LPullEq

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PositivityTheory.HtPt.Mb.pull_eq : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i → L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' :=
  @PositivityTheory.HtPt.Mb.LPullEq.pull_eq_pullLoc_of_dominates
