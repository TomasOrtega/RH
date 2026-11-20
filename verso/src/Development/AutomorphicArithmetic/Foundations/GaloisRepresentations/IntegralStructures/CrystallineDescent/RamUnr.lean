import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Int.Core

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem ramUnr_holds : RamUnr := by
  intro F Ω _ _ _ _ _ T Q hQ
  obtain ⟨u, huT, A, hA, τ, hτ, hfix⟩ := hQ
  haveI : Algebra.IsQuadraticExtension F ↥Q.K := ⟨Q.two⟩
  haveI : IsGalois F ↥Q.K := inferInstance
  obtain ⟨w, hw, hwu⟩ := CompanionTheory.FamInh.exists_place_between (K := F) (L := ↥Q.K) hA
  have hunder : w.under (𝓞 F) = u :=
    ReciprocityTheory.Gal.eq_of_isPlaceOver (fun x => by
      rw [IsScalarTower.algebraMap_apply F ↥Q.K Ω]
      exact hw (algebraMap (𝓞 F) (𝓞 ↥Q.K) x)) hA
  refine ⟨w, fun hun => hfix fun x => ?_, hunder ▸ huT⟩
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hs := CompanionTheory.FamInh.res_mem_inertia (L := ↥Q.K) hw hτ
  rw [(CompanionTheory.FamInh.inertia_eq_bot_iff u w).2 he, Subgroup.mem_bot] at hs
  have hc := AlgEquiv.restrictNormal_commutes τ ↥Q.K x
  have h1 : AlgEquiv.restrictNormal τ ↥Q.K x = x := DFunLike.congr_fun hs x
  rw [h1] at hc
  exact hc.symm

end UpperTheory.Gal.Int.Core
