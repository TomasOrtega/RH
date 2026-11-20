import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.CountableCompletion

open Cardinal IsLocalRing

/- English proof (translation)
Establish `hinj : Function.Injective (fun x : AdicCompletion I R => (x.1 : ∀ n : ℕ, R ⧸ (I ^ n • ⊤ : Submodule R R)))` using `fun x y h => Subtype.ext h`. Use `(mk_le_of_injective hinj).trans ?_` and prove the remaining obligations. Rewrite using `[mk_pi]`. Use `(prod_le_prod _ (fun _ => ℵ₀) fun n => (mk_le_of_surjective (Submodule.mkQ_surjective _)).trans mk_le_aleph0).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem mk_adicCompletion_le_continuum (R : Type) [CommRing R] [Countable R] (I : Ideal R) :
    #(AdicCompletion I R) ≤ 𝔠 := by
  have hinj : Function.Injective
      (fun x : AdicCompletion I R => (x.1 : ∀ n : ℕ, R ⧸ (I ^ n • ⊤ : Submodule R R))) :=
    fun x y h => Subtype.ext h
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    (mk_le_of_surjective (Submodule.mkQ_surjective _)).trans mk_le_aleph0).trans ?_
  simp

noncomputable abbrev completionCDVR (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharZero R] : CDVR :=
  haveI : CharZero (AdicCompletion (maximalIdeal R) R) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R)
  { V := AdicCompletion (maximalIdeal R) R }

/- English proof (translation)
Introduce `R _ _ _ _ hR`. Conclude with `⟨completionCDVR R, algebraMap R (AdicCompletion (maximalIdeal R) R), GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance, mk_adicCompletion_le_continuum R (maximalIdeal R)⟩`.
-/
theorem exists_cdvr_mk_le_continuum :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R], Countable R →
      ∃ (T : CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i ∧
        Cardinal.mk T.V ≤ Cardinal.continuum := by
  intro R _ _ _ _ hR
  exact ⟨completionCDVR R, algebraMap R (AdicCompletion (maximalIdeal R) R),
    GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance,
    mk_adicCompletion_le_continuum R (maximalIdeal R)⟩

end GlobalTheory.CountableCompletion
