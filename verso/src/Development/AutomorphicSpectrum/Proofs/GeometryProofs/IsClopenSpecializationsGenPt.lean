import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Establish `hF : (irreducibleComponents Y).Finite` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`. Use `⟨⋂ Z ∈ {Z ∈ irreducibleComponents Y | p ∉ Z}, Zᶜ, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(hF.subset (Set.sep_subset _ _)).isOpen_biInter fun Z hZ => ?_` and prove the remaining obligations. Conclude with `(isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl`. Simplify using `only [Set.mem_iInter]`.

Conclude with `fun Z hZ => hZ.2`. Introduce `q hq`. Establish `hmem` using `irreducibleComponent_mem_irreducibleComponents q`. Establish `hpZ : p ∈ irreducibleComponent q`. Assume the negation of the conclusion as `hp`.

Conclude with `(Set.mem_iInter₂.1 hq _ ⟨hmem, hp⟩) mem_irreducibleComponent`. Take `⟨z, hz⟩` from `QuasiSober.sober (isIrreducible_irreducibleComponent (x := q)) isClosed_irreducibleComponent`. Conclude with `⟨z, hz.specializes hpZ, hz.specializes mem_irreducibleComponent⟩`.
-/
theorem exists_isOpen_common_generization {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] (p : Y) :
    ∃ V : Set Y, IsOpen V ∧ p ∈ V ∧ ∀ q ∈ V, ∃ z : Y, z ⤳ p ∧ z ⤳ q := by
  have hF : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine ⟨⋂ Z ∈ {Z ∈ irreducibleComponents Y | p ∉ Z}, Zᶜ, ?_, ?_, ?_⟩
  · refine (hF.subset (Set.sep_subset _ _)).isOpen_biInter fun Z hZ => ?_
    exact (isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl
  · simp only [Set.mem_iInter]
    exact fun Z hZ => hZ.2
  · intro q hq
    have hmem := irreducibleComponent_mem_irreducibleComponents q
    have hpZ : p ∈ irreducibleComponent q := by
      by_contra hp
      exact (Set.mem_iInter₂.1 hq _ ⟨hmem, hp⟩) mem_irreducibleComponent
    obtain ⟨z, hz⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := q))
      isClosed_irreducibleComponent
    exact ⟨z, hz.specializes hpZ, hz.specializes mem_irreducibleComponent⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨y, rfl⟩ : z ∈ Set.range (X.fromSpecStalk p) := by`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hz`. Establish `hinj` using `h.inj ⟨p, hp⟩`. Use `haveI : IsDomain (X.presheaf.stalk p) := hinj.isDomain (genMap ξ ⟨p, hp⟩)`.

Establish `hp' : ξ (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ p` using `hp`. Set `φ` to `X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ`. Establish `hφ : Spec.map φ ≫ X.fromSpecStalk p = ξ`. Express the relevant statement in the definitionally equal form `Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = ξ`. Rewrite using `[Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`.

Conclude with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ`. Establish `hbot : (Spec.map φ) (IsLocalRing.closedPoint Ω) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p))`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (genMap ξ ⟨p, hp⟩) (IsLocalRing.maximalIdeal Ω) = ⊥`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`.

Conclude with `Ideal.comap_bot_of_injective _ hinj`. Establish `hη : genPt ξ = X.fromSpecStalk p ⟨⊥, Ideal.isPrime_bot⟩`. Rewrite using `[← hbot]`. Use `conv_lhs => rw [genPt, ← hφ]`. Both sides reduce to the same expression.

Rewrite using `[hη]`. Conclude with `((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map (X.fromSpecStalk p).continuous`.
-/
theorem genPt_specializes_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p z : X}
    (hp : genPt ξ ⤳ p) (hz : z ⤳ p) : genPt ξ ⤳ z := by
  obtain ⟨y, rfl⟩ : z ∈ Set.range (X.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact hz
  have hinj := h.inj ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := hinj.isDomain (genMap ξ ⟨p, hp⟩)
  have hp' : ξ (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ p := hp
  let φ := X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ
  have hφ : Spec.map φ ≫ X.fromSpecStalk p = ξ := by
    change Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = ξ
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hbot : (Spec.map φ) (IsLocalRing.closedPoint Ω) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (genMap ξ ⟨p, hp⟩) (IsLocalRing.maximalIdeal Ω) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  have hη : genPt ξ = X.fromSpecStalk p ⟨⊥, Ideal.isPrime_bot⟩ := by
    rw [← hbot]
    conv_lhs => rw [genPt, ← hφ]
    rfl
  rw [hη]
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map (X.fromSpecStalk p).continuous

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: {q : X | genPt ξ ⤳ q} = closure {genPt ξ}`. Use extensionality with `q`. Conclude with `specializes_iff_mem_closure`. Rewrite using `[this]`.

Conclude with `isClosed_closure`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `p hp`. Take `⟨U, hU, hpU, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial`. Use `haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`.

Take `⟨V, hV, hpV, hVq⟩` from `@exists_isOpen_common_generization U _ (noetherianSpace_of_isAffineOpen U hU) U.isOpen.isOpenEmbedding_subtypeVal.quasiSober ⟨p, hpU⟩`. Establish `hopen : IsOpen (Subtype.val '' V : Set X)` using `U.isOpen.isOpenMap_subtype_val V hV`. Use `Filter.mem_of_superset (hopen.mem_nhds ⟨_, hpV, rfl⟩) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Take `⟨z, hzp, hzq⟩` from `hVq q hq`.

Conclude with `(genPt_specializes_of_specializes ξ h (p := p) hp (hzp.map continuous_subtype_val)).trans (hzq.map continuous_subtype_val)`.
-/
theorem isClopen_setOf_genPt_specializes (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsClopen {q : X | genPt ξ ⤳ q} := by
  refine ⟨?_, ?_⟩
  · have : {q : X | genPt ξ ⤳ q} = closure {genPt ξ} := by
      ext q; exact specializes_iff_mem_closure
    rw [this]; exact isClosed_closure
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨V, hV, hpV, hVq⟩ := @exists_isOpen_common_generization U _
      (noetherianSpace_of_isAffineOpen U hU) U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
      ⟨p, hpU⟩
    have hopen : IsOpen (Subtype.val '' V : Set X) := U.isOpen.isOpenMap_subtype_val V hV
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨_, hpV, rfl⟩) ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨z, hzp, hzq⟩ := hVq q hq
    exact (genPt_specializes_of_specializes ξ h (p := p) hp
      (hzp.map continuous_subtype_val)).trans (hzq.map continuous_subtype_val)

end GlobalTheory.CompanionTheory.Ar
