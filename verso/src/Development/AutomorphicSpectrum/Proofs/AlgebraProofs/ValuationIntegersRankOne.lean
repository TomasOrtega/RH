import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin

/- English proof (translation)
Introduce `C _ _ v R _ _ hv`. Use `haveI hdom : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj`. Use `haveI hval : ValuationRing R := ValuationRing.of_integers v hv`. Use `⟨hdom, hval, ⟨?_⟩, ?_⟩` and prove the remaining obligations. Introduce `p hp0 hp`.

Establish `hle : IsLocalRing.maximalIdeal R ≤ p`. Introduce `x hx`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `p.zero_mem`.

Take `⟨y, hyp, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hp0`. Establish `hxu : ¬ IsUnit x`. Simplify `hx` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Establish `hvx : v (algebraMap R C x) < 1` using `lt_of_le_of_ne (hv.map_le_one x) fun e => hxu (hv.isUnit_iff_valuation_eq_one.2 e)`. Establish `hvy : 0 < v (algebraMap R C y)`.

Rewrite using `[zero_lt_iff, Valuation.ne_zero_iff]`. Conclude with `fun e => hy0 (hv.hom_inj (by rw [e, map_zero]))`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hvy hvx`. Establish `hdvd : y ∣ x ^ n`. Rewrite using `[hv.dvd_iff_le, map_pow, map_pow]`.

Conclude with `hn.le`. Conclude with `hp.mem_of_pow_mem n (p.mem_of_dvd hdvd hyp)`. Establish `heq : p = IsLocalRing.maximalIdeal R` using `le_antisymm (IsLocalRing.le_maximalIdeal hp.ne_top) hle`. Rewrite using `[heq]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal R`.

Use `haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hv.hom_inj`. Use `IsFractionRing.of_field R C fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz0 : z = 0`. Conclude with `⟨0, 1, by simp [hz0]⟩`. Break down `le_total (v z) 1 with h | h` into its components or cases.

Take `⟨a, ha⟩` from `hv.exists_of_le_one h`. Conclude with `⟨a, 1, by simp [ha]⟩`. Establish `h' : v z⁻¹ ≤ 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ h`.

Take `⟨a, ha⟩` from `hv.exists_of_le_one h'`. Conclude with `⟨1, a, by simp [ha]⟩`.
-/
theorem integers_valuationRing_dimensionLEOne_isFractionRing :
    ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    ∃ (_ : IsDomain R), ValuationRing R ∧ Ring.DimensionLEOne R ∧ IsFractionRing R C := by
  intro C _ _ v R _ _ hv
  haveI hdom : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI hval : ValuationRing R := ValuationRing.of_integers v hv
  refine ⟨hdom, hval, ⟨?_⟩, ?_⟩
  · intro p hp0 hp
    have hle : IsLocalRing.maximalIdeal R ≤ p := by
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact p.zero_mem
      obtain ⟨y, hyp, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
      have hxu : ¬ IsUnit x := by
        simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
      have hvx : v (algebraMap R C x) < 1 :=
        lt_of_le_of_ne (hv.map_le_one x) fun e => hxu (hv.isUnit_iff_valuation_eq_one.2 e)
      have hvy : 0 < v (algebraMap R C y) := by
        rw [zero_lt_iff, Valuation.ne_zero_iff]
        exact fun e => hy0 (hv.hom_inj (by rw [e, map_zero]))
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hvy hvx
      have hdvd : y ∣ x ^ n := by
        rw [hv.dvd_iff_le, map_pow, map_pow]
        exact hn.le
      exact hp.mem_of_pow_mem n (p.mem_of_dvd hdvd hyp)
    have heq : p = IsLocalRing.maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal hp.ne_top) hle
    rw [heq]
    exact IsLocalRing.maximalIdeal.isMaximal R
  · haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hv.hom_inj
    refine IsFractionRing.of_field R C fun z => ?_
    by_cases hz0 : z = 0
    · exact ⟨0, 1, by simp [hz0]⟩
    rcases le_total (v z) 1 with h | h
    · obtain ⟨a, ha⟩ := hv.exists_of_le_one h
      exact ⟨a, 1, by simp [ha]⟩
    · have h' : v z⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ h
      obtain ⟨a, ha⟩ := hv.exists_of_le_one h'
      exact ⟨1, a, by simp [ha]⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin
