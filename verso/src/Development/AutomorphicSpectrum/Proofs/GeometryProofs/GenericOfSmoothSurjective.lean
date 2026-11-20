import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.CptLift

/- English proof (translation)
Introduce `K _ X₀ X' Ω _ ξ ξ' π s' hs hc hξ hsurj`. Substitute `hc` using the available equality. Establish `hd : ∀ x : X', IsDomain (X'.presheaf.stalk x)` using `fun x => GroundTheory.Arith.SchemeCoh.isDomain_stalk_of_smooth_field s' x`. Establish `hcomp : (Scheme.stalkClosedPointTo (ξ' ≫ π)).hom = (Scheme.stalkClosedPointTo ξ').hom.comp (π.stalkMap (genPt ξ')).hom` using `congrArg (fun t => t.hom) (Scheme.stalkClosedPointTo_comp ξ' π)`. Establish `hbij : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom`.

Establish `hb` using `hξ.bij`. Rewrite `hb` using `[hcomp]`. Use `⟨fun a b hab => ?_, fun c => ?_⟩` and prove the remaining obligations. Take `⟨a', rfl⟩` from `hsurj a`. Take `⟨b', rfl⟩` from `hsurj b`.

Conclude with `congrArg _ (hb.1 hab)`. Take `⟨a, ha⟩` from `hb.2 c`. Conclude with `⟨_, ha⟩`. Use `⟨hbij, fun p => ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (X'.presheaf.stalkSpecializes p.2).hom` using `by haveI := hd (genPt ξ')`.

Conclude with `GlobalTheory.PushInv.stalkSpecializes_injective p.2`. Introduce `a b hab`. Conclude with `hinj (hbij.1 hab)`.
-/
theorem isCptGen_of_smooth_of_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀)
    (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ →
    Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  intro K _ X₀ X' Ω _ ξ ξ' π s' hs hc hξ hsurj
  subst hc
  have hd : ∀ x : X', IsDomain (X'.presheaf.stalk x) := fun x =>
    GroundTheory.Arith.SchemeCoh.isDomain_stalk_of_smooth_field s' x
  have hcomp : (Scheme.stalkClosedPointTo (ξ' ≫ π)).hom =
      (Scheme.stalkClosedPointTo ξ').hom.comp (π.stalkMap (genPt ξ')).hom :=
    congrArg (fun t => t.hom) (Scheme.stalkClosedPointTo_comp ξ' π)
  have hbij : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom := by
    have hb := hξ.bij
    rw [hcomp] at hb
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', rfl⟩ := hsurj b
      exact congrArg _ (hb.1 hab)
    · obtain ⟨a, ha⟩ := hb.2 c
      exact ⟨_, ha⟩
  refine ⟨hbij, fun p => ?_⟩
  have hinj : Function.Injective (X'.presheaf.stalkSpecializes p.2).hom := by
    haveI := hd (genPt ξ')
    exact GlobalTheory.PushInv.stalkSpecializes_injective p.2
  intro a b hab
  exact hinj (hbij.1 hab)

end GlobalTheory.CompanionTheory.Ar.CptLift
