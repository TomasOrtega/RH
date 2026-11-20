import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedEmptyOfUniversallyClosedOfLeJacobsonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersionStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

/- English proof (translation)
Introduce `R _ I hI W W' f j hf hj hA t ht hp`. Take `⟨hs, hsp, hsc⟩` from `GlobalTheory.T.compatibleReductionSystem_map_immersion R I W W' f j hf inferInstance t ht hp`. Take `⟨T, hTp, hTr⟩` from `hA _ hs hsp`. Establish `hs0 : ((((t 0).map j).support : Set W)) ⊆ Set.range j` using `by haveI : IsProper ((t 0).subschemeι ≫ j ≫ f) := hp 0 haveI : IsProper (((t 0).subschemeι ≫ j) ≫ f) := by rw [Category.assoc]; infer_instance haveI : UniversallyClosed ((t 0).subschemeι ≫ j) := UniversallyClosed.of_comp_of_isSeparated _ f haveI : QuasiCompact ((t 0).subschemeι ≫ …`. Establish `hker : (t 0).map j = Scheme.Hom.ker ((t 0).subschemeι ≫ j)`.

Rewrite using `[← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]`. Rewrite using `[hker, Scheme.Hom.support_ker, (((t 0).subschemeι ≫ j).isClosedMap.isClosed_range).closure_eq]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨(t 0).subschemeι x, by simp⟩`. Establish `hT : ((T.support : Set W)) ⊆ Set.range j` using `by haveI : UniversallyClosed (T.subschemeι ≫ f) := inferInstance`.

Establish `hZ : IsClosed (T.subschemeι.base ⁻¹' (Set.range j)ᶜ)` using `(j.isOpenEmbedding.isOpen_range.isClosed_compl).preimage T.subschemeι.continuous`. Establish `hE` using `GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI T.subscheme (T.subschemeι ≫ f) inferInstance _ hZ (by`. Introduce `x hx hIx`. Apply `hx` to reduce the goal to its premises. Apply `hs0` to reduce the goal to its premises.

Establish `h0 : T ⊔ baseIdeal f (I ^ (0 + 1)) = (t 0).map j` using `hTr 0`. Rewrite using `[← h0, Scheme.IdealSheafData.support_sup]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.IdealSheafData.range_subschemeι]`. Conclude with `⟨x, rfl⟩`.

Use `((GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).2.2 R W f (I ^ (0 + 1)) (T.subschemeι x)).2 ?_` and prove the remaining obligations. Rewrite using `[zero_add, pow_one]`. Simplify using `using hIx)`. Introduce `y hy`. Rewrite `hy` using `[← Scheme.IdealSheafData.range_subschemeι]`.

Take `⟨x, rfl⟩` from `hy`. Assume the negation of the conclusion as `hc`. Establish `: x ∈ (T.subschemeι.base ⁻¹' (Set.range j)ᶜ)` using `hc`. Rewrite `this` using `[hE]`. Conclude with `this`.

Use `⟨T.comap j, ?_, fun e => ?_⟩` and prove the remaining obligations. Establish `hsurj : Function.Surjective (pullback.snd j T.subschemeι)`. Introduce `x`. Take `⟨w, hw⟩` from `hT (by`. Rewrite using `[← Scheme.IdealSheafData.range_subschemeι]`.

Conclude with `⟨x, rfl⟩)`. Take `⟨z, -, hz⟩` from `Scheme.Pullback.exists_preimage_pullback w x hw`. Conclude with `⟨z, hz⟩`. Use `haveI : IsIso (pullback.snd j T.subschemeι) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨hsurj⟩⟩`. Establish `he : (T.comap j).subschemeι ≫ j ≫ f = (T.comapIso j).hom ≫ pullback.snd j T.subschemeι ≫ T.subschemeι ≫ f`.

Rewrite using `[← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]`. Rewrite using `[he]`. Use `infer_instance`. Rewrite using `[← (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R W W' f j, ← Scheme.IdealSheafData.comap_sup, show T ⊔ baseIdeal f (I ^ (e + 1)) = (t e).map j from hTr e, hsc e]`.
-/
theorem alg_comp_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
    ∀ (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (j : W' ⟶ W), IsSeparated f →
      IsOpenImmersion j → Alg f I → Alg (j ≫ f) I := by
  intro R _ I hI W W' f j hf hj hA t ht hp
  obtain ⟨hs, hsp, hsc⟩ := GlobalTheory.T.compatibleReductionSystem_map_immersion R I W W' f j hf inferInstance t ht hp
  obtain ⟨T, hTp, hTr⟩ := hA _ hs hsp

  have hs0 : ((((t 0).map j).support : Set W)) ⊆ Set.range j := by
    haveI : IsProper ((t 0).subschemeι ≫ j ≫ f) := hp 0
    haveI : IsProper (((t 0).subschemeι ≫ j) ≫ f) := by rw [Category.assoc]; infer_instance
    haveI : UniversallyClosed ((t 0).subschemeι ≫ j) := UniversallyClosed.of_comp_of_isSeparated _ f
    haveI : QuasiCompact ((t 0).subschemeι ≫ j) := QuasiCompact.of_comp _ f
    have hker : (t 0).map j = Scheme.Hom.ker ((t 0).subschemeι ≫ j) := by
      rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]
    rw [hker, Scheme.Hom.support_ker,
      (((t 0).subschemeι ≫ j).isClosedMap.isClosed_range).closure_eq]
    rintro _ ⟨x, rfl⟩
    exact ⟨(t 0).subschemeι x, by simp⟩

  have hT : ((T.support : Set W)) ⊆ Set.range j := by
    haveI : UniversallyClosed (T.subschemeι ≫ f) := inferInstance
    have hZ : IsClosed (T.subschemeι.base ⁻¹' (Set.range j)ᶜ) :=
      (j.isOpenEmbedding.isOpen_range.isClosed_compl).preimage T.subschemeι.continuous
    have hE := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI T.subscheme (T.subschemeι ≫ f) inferInstance _ hZ (by
      intro x hx hIx
      apply hx
      apply hs0
      have h0 : T ⊔ baseIdeal f (I ^ (0 + 1)) = (t 0).map j := hTr 0
      rw [← h0, Scheme.IdealSheafData.support_sup]
      refine ⟨?_, ?_⟩
      · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
      · refine ((GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).2.2 R W f (I ^ (0 + 1)) (T.subschemeι x)).2 ?_
        rw [zero_add, pow_one]
        simpa using hIx)
    intro y hy
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy
    obtain ⟨x, rfl⟩ := hy
    by_contra hc
    have : x ∈ (T.subschemeι.base ⁻¹' (Set.range j)ᶜ) := hc
    rw [hE] at this
    exact this
  refine ⟨T.comap j, ?_, fun e => ?_⟩
  · have hsurj : Function.Surjective (pullback.snd j T.subschemeι) := by
      intro x
      obtain ⟨w, hw⟩ := hT (by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩)
      obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
      exact ⟨z, hz⟩
    haveI : IsIso (pullback.snd j T.subschemeι) :=
      (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨hsurj⟩⟩
    have he : (T.comap j).subschemeι ≫ j ≫ f =
        (T.comapIso j).hom ≫ pullback.snd j T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [he]
    infer_instance
  · rw [← (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R W W' f j, ← Scheme.IdealSheafData.comap_sup, show T ⊔ baseIdeal f (I ^ (e + 1)) = (t e).map j from hTr e, hsc e]

end GlobalTheory.FormalAlg
