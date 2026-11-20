import Mathlib
import Formalism.UnipotentAdelicQuotients.ClassNumberFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGLStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrouStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompactMeetsFinitelyManyLeftCosetsOpenStatement

open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ n S hS U hUo _`. Take `⟨T₀, hT₀, hx⟩` from `GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL F n S (fun B _ _ => ⟨(hS B).1, fun g h hg hh => (hS B).2.1 g hg h hh, fun g hg => (hS B).2.2 g hg⟩)`. Establish `hK` using `GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup F n S (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) (fun g => Iff.rfl)`. Take `⟨T₁, hT₁⟩` from `GlobalTheory.T.compact_meets_finitely_many_leftCosets_open _ U _ hUo hK`. Use `⟨Finset.image₂ (fun (s : T₀) (t : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) => (⟨s.1, hT₀ s.1 s.2⟩ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) * t) T₀.attach T₁, ?_⟩` and prove the remaining obligations.

Introduce `x`. Take `⟨γ, hγ, s, hs, k, hk, hki, hxe⟩` from `hx x.1 x.2`. Take `⟨t, ht, u, hu, hke⟩` from `hT₁ ⟨k, hk⟩ hki`. Use `⟨γ, hγ, _, Finset.mem_image₂_of_mem (Finset.mem_attach T₀ ⟨s, hs⟩) ht, u, hu, ?_⟩` and prove the remaining obligations. Establish `hke' : k = t.1 * u.1` using `congrArg Subtype.val hke`.

Rewrite using `[hxe, hke']`. Simplify using `only [Subgroup.coe_mul, mul_assoc]`.
-/
theorem classNumberFinite_holds : HeckeCharacterZeroLocus.ClassNumberFinite := by
  classical
  intro F _ _ n S hS U hUo _
  obtain ⟨T₀, hT₀, hx⟩ := GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL F n S (fun B _ _ =>
    ⟨(hS B).1, fun g h hg hh => (hS B).2.1 g hg h hh, fun g hg => (hS B).2.2 g hg⟩)
  have hK := GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup F n S (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))
    (fun g => Iff.rfl)
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.compact_meets_finitely_many_leftCosets_open _ U _ hUo hK
  refine ⟨Finset.image₂ (fun (s : T₀) (t : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) =>
    (⟨s.1, hT₀ s.1 s.2⟩ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) * t) T₀.attach T₁, ?_⟩
  intro x
  obtain ⟨γ, hγ, s, hs, k, hk, hki, hxe⟩ := hx x.1 x.2
  obtain ⟨t, ht, u, hu, hke⟩ := hT₁ ⟨k, hk⟩ hki
  refine ⟨γ, hγ, _, Finset.mem_image₂_of_mem (Finset.mem_attach T₀ ⟨s, hs⟩) ht, u, hu, ?_⟩
  have hke' : k = t.1 * u.1 := congrArg Subtype.val hke
  rw [hxe, hke']
  simp only [Subgroup.coe_mul, mul_assoc]

end GlobalTheory
