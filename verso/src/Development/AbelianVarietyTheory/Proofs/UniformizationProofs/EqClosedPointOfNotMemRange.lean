import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericExt

universe u

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Rewrite using `[← hU.fromSpecStalk_eq_fromSpecStalk hxU]`. Express the relevant statement in the definitionally equal form `Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)`. Establish `: Flat (Spec.map (X.presheaf.germ U x hxU))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`.

Set `` to `X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)`. Use `hU.isLocalization_stalk ⟨x, hxU⟩` as an intermediate fact. Conclude with `IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl`. Establish `h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU)` using `IsAffineOpen.isOpenImmersion_fromSpec hU`. Establish `h₃ : Flat (IsAffineOpen.fromSpec hU)` using `inferInstance`.

Conclude with `MorphismProperty.comp_mem @Flat _ _ this h₃`.
-/
theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

/- English proof (translation)
Set `h` to `Spec.map (g'.stalkMap p)`. Take `⟨h₁, h₂⟩ : Flat h ∧ Surjective h` from `(flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_stalkMap_of_flat g' p)`. Establish `hh : h ≫ Y.fromSpecStalk (g' p) = T.fromSpecStalk p ≫ g'` using `Scheme.SpecMap_stalkMap_fromSpecStalk g'`. Use `flat_fromSpecStalk Y (g' p)` as an intermediate fact. Establish `key : pullback.fst h h ≫ T.fromSpecStalk p ≫ g = pullback.snd h h ≫ T.fromSpecStalk p ≫ g`.

Set `q` to `pullback.fst h h ≫ h ≫ Y.fromSpecStalk (g' p)`. Establish `hq : Flat q` using `inferInstance`. Use `hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst q j) (terminal.from X) ?_ (terminal.hom_ext _ _)` and prove the remaining obligations. Establish `e₁` using `H _ (pullback.fst q j ≫ pullback.fst h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by`. Rewrite using `[← pullback.condition]`.

Simplify using `only [q, Category.assoc, hh])`. Establish `e₂` using `H _ (pullback.fst q j ≫ pullback.snd h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by`. Rewrite using `[← pullback.condition]`. Simplify using `only [q, Category.assoc, ← hh, pullback.condition_assoc])`. Simplify `e₁.symm.trans e₂` using `only [Category.assoc]`.

Set `φ` to `EffectiveEpi.desc h (T.fromSpecStalk p ≫ g) (fun a b hab => by`. Use `congrArg (pullback.lift a b hab ≫ ·) key` as an intermediate fact. Simplify `this)` using `only [pullback.lift_fst_assoc, pullback.lift_snd_assoc]`. Establish `hφ : h ≫ φ = T.fromSpecStalk p ≫ g` using `EffectiveEpi.fac _ _ _`. Use `⟨φ, fun Z ρ r hr => ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_epi (pullback.fst ρ h), pullback.condition_assoc, hφ]`. Use `H _ (pullback.snd ρ h ≫ T.fromSpecStalk p) (pullback.fst ρ h ≫ r) (by` as an intermediate fact. Rewrite using `[Category.assoc, hr, pullback.condition_assoc, hh, Category.assoc])`. Simplify `this` using `only [Category.assoc]`.
-/
theorem exists_hom_specStalk {W Y T X : Scheme.{u}} (j : W ⟶ Y) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] [X.IsSeparated] (F : W ⟶ X) (g' : T ⟶ Y) [Flat g'] (g : T ⟶ X)
    (H : ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) (p : T) :
    ∃ φ : Spec (Y.presheaf.stalk (g' p)) ⟶ X, ∀ (Z : Scheme.{u})
      (ρ : Z ⟶ Spec (Y.presheaf.stalk (g' p))) (r : Z ⟶ W),
      r ≫ j = ρ ≫ Y.fromSpecStalk (g' p) → r ≫ F = ρ ≫ φ := by
  let h := Spec.map (g'.stalkMap p)
  obtain ⟨h₁, h₂⟩ : Flat h ∧ Surjective h :=
    (flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_stalkMap_of_flat g' p)
  have hh : h ≫ Y.fromSpecStalk (g' p) = T.fromSpecStalk p ≫ g' :=
    Scheme.SpecMap_stalkMap_fromSpecStalk g'
  have := flat_fromSpecStalk Y (g' p)
  have key : pullback.fst h h ≫ T.fromSpecStalk p ≫ g = pullback.snd h h ≫ T.fromSpecStalk p ≫ g := by
    let q := pullback.fst h h ≫ h ≫ Y.fromSpecStalk (g' p)
    have hq : Flat q := inferInstance
    refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst q j) (terminal.from X) ?_
      (terminal.hom_ext _ _)
    have e₁ := H _ (pullback.fst q j ≫ pullback.fst h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]; simp only [q, Category.assoc, hh])
    have e₂ := H _ (pullback.fst q j ≫ pullback.snd h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]
      simp only [q, Category.assoc, ← hh, pullback.condition_assoc])
    simpa only [Category.assoc] using e₁.symm.trans e₂
  let φ := EffectiveEpi.desc h (T.fromSpecStalk p ≫ g) (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hφ : h ≫ φ = T.fromSpecStalk p ≫ g := EffectiveEpi.fac _ _ _
  refine ⟨φ, fun Z ρ r hr => ?_⟩
  rw [← cancel_epi (pullback.fst ρ h), pullback.condition_assoc, hφ]
  have := H _ (pullback.snd ρ h ≫ T.fromSpecStalk p) (pullback.fst ρ h ≫ r) (by
    rw [Category.assoc, hr, pullback.condition_assoc, hh, Category.assoc])
  simpa only [Category.assoc] using this

/- English proof (translation)
Establish `hX : X.IsSeparated` using `⟨by rw [← terminal.comp_from sX]; infer_instance⟩`. Establish `: IsSchemeTheoreticallyDominant j` using `.of_isDominant j`. Set `e₀` to `Y.fromSpecStalk (genericPoint Y)`. Establish `: IsDominant e₀` using `isDominant_fromSpecStalk_genericPoint Y`. Establish `hr : Set.range e₀ ⊆ Set.range j`.

Rewrite using `[Scheme.range_fromSpecStalk]`. Introduce `z hz`. Establish `hg : genericPoint Y ∈ Set.range j` using `(genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range |>.2 (by simpa [Set.range_nonempty_iff_nonempty] using j.denseRange.nonempty)`. Conclude with `Specializes.mem_open hz j.isOpenEmbedding.isOpen_range hg`. Set `e` to `IsOpenImmersion.lift j e₀ hr`.

Establish `he : e ≫ j = e₀` using `IsOpenImmersion.lift_fac _ _ _`. Establish `loc : ∀ y : Y, ∃ (U : Scheme.{u}) (k : U ⟶ Y) (_ : IsOpenImmersion k) (ψ : U ⟶ X) (l : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ U), y ∈ Set.range k ∧ l ≫ k = e₀ ∧ l ≫ ψ = e ≫ F`. Introduce `y`. Distinguish the cases in `hy : y ∈ Set.range j`. Conclude with `⟨W, j, inferInstance, F, e, hy, he, rfl⟩`.

Take `⟨T, g', g, hg', ⟨p, rfl⟩, hT⟩` from `H y hy`. Take `⟨φ, hφ⟩` from `exists_hom_specStalk j F g' g hT p`. Use `flat_fromSpecStalk Y (g' p)` as an intermediate fact. Establish `hover : φ ≫ sX = Y.fromSpecStalk (g' p) ≫ sY`. Use `hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst (Y.fromSpecStalk (g' p)) j) (terminal.from S) ?_ (terminal.hom_ext _ _)` and prove the remaining obligations.

Rewrite using `[← reassoc_of% (hφ _ _ _ pullback.condition.symm), hF, pullback.condition_assoc]`. Take `⟨U, hU, ψ, h₁, -⟩` from `spread_out_of_isGermInjective' sY sX φ hover`. Set `m` to `Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (g' p)))`. Establish `hm : m ≫ Y.fromSpecStalk (g' p) = e₀` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk _`. Use `⟨U, U.ι, inferInstance, ψ, m ≫ U.fromSpecStalkOfMem _ hU, ⟨⟨_, hU⟩, rfl⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hm]`. Rewrite using `[Category.assoc, ← h₁]`. Conclude with `(hφ _ m e (he.trans hm.symm)).symm`. Use `choose U k hk ψ l hy hl hψ using loc`. Set `𝒰 : Y.OpenCover` to `Scheme.Cover.mkOfCovers Y U k (fun y => ⟨y, hy y⟩) hk`.

Establish `hc : ∀ a b : Y, pullback.fst (k a) (k b) ≫ ψ a = pullback.snd (k a) (k b) ≫ ψ b`. Introduce `a b`. Set `m` to `pullback.lift (l a) (l b) ((hl a).trans (hl b).symm)`. Establish `: IsReduced (pullback (k a) (k b))` using `isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ k a)`. Establish `: IsDominant (m ≫ pullback.fst _ _ ≫ k a)`.

Rewrite using `[pullback.lift_fst_assoc, hl]`. Use `infer_instance`. Establish `: IsDominant m` using `.of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ k a)`. Use `ext_of_isDominant m ?_` and prove the remaining obligations. Rewrite using `[pullback.lift_fst_assoc, pullback.lift_snd_assoc, hψ, hψ]`.

Establish `hι : ∀ a : Y, k a ≫ 𝒰.glueMorphisms ψ hc = ψ a` using `fun a => 𝒰.ι_glueMorphisms ψ hc a`. Establish `h1 : j ≫ 𝒰.glueMorphisms ψ hc = F`. Establish `: IsReduced W` using `isReduced_of_isOpenImmersion j`. Establish `: IsDominant (e ≫ j)` using `by rw [he]; infer_instance`. Establish `: IsDominant e` using `.of_comp_of_isOpenImmersion e j`.

Use `ext_of_isDominant e ?_` and prove the remaining obligations. Rewrite using `[reassoc_of% he, ← hl (genericPoint Y), Category.assoc, hι, hψ]`. Use `⟨_, h1, ext_of_isDominant j ?_⟩` and prove the remaining obligations. Rewrite using `[reassoc_of% h1, hF]`.
-/
theorem exists_extension {W Y X S : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j] [IsIntegral Y] [S.IsSeparated] (sY : Y ⟶ S) (sX : X ⟶ S) [IsSeparated sX]
    [LocallyOfFiniteType sX] (F : W ⟶ X) (hF : F ≫ sX = j ≫ sY)
    (H : ∀ y : Y, y ∉ Set.range j → ∃ (T : Scheme.{u}) (g' : T ⟶ Y) (g : T ⟶ X), Flat g' ∧ y ∈ Set.range g' ∧
      ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) :
    ∃ ψ : Y ⟶ X, j ≫ ψ = F ∧ ψ ≫ sX = sY := by
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  let e₀ := Y.fromSpecStalk (genericPoint Y)
  have : IsDominant e₀ := isDominant_fromSpecStalk_genericPoint Y
  have hr : Set.range e₀ ⊆ Set.range j := by
    rw [Scheme.range_fromSpecStalk]
    intro z hz
    have hg : genericPoint Y ∈ Set.range j :=
      (genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range |>.2
        (by simpa [Set.range_nonempty_iff_nonempty] using j.denseRange.nonempty)
    exact Specializes.mem_open hz j.isOpenEmbedding.isOpen_range hg
  let e := IsOpenImmersion.lift j e₀ hr
  have he : e ≫ j = e₀ := IsOpenImmersion.lift_fac _ _ _
  have loc : ∀ y : Y, ∃ (U : Scheme.{u}) (k : U ⟶ Y) (_ : IsOpenImmersion k) (ψ : U ⟶ X)
      (l : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ U),
      y ∈ Set.range k ∧ l ≫ k = e₀ ∧ l ≫ ψ = e ≫ F := by
    intro y
    by_cases hy : y ∈ Set.range j
    · exact ⟨W, j, inferInstance, F, e, hy, he, rfl⟩
    obtain ⟨T, g', g, hg', ⟨p, rfl⟩, hT⟩ := H y hy
    obtain ⟨φ, hφ⟩ := exists_hom_specStalk j F g' g hT p
    have := flat_fromSpecStalk Y (g' p)
    have hover : φ ≫ sX = Y.fromSpecStalk (g' p) ≫ sY := by
      refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst (Y.fromSpecStalk (g' p)) j)
        (terminal.from S) ?_ (terminal.hom_ext _ _)
      rw [← reassoc_of% (hφ _ _ _ pullback.condition.symm), hF, pullback.condition_assoc]
    obtain ⟨U, hU, ψ, h₁, -⟩ := spread_out_of_isGermInjective' sY sX φ hover
    let m := Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (g' p)))
    have hm : m ≫ Y.fromSpecStalk (g' p) = e₀ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    refine ⟨U, U.ι, inferInstance, ψ, m ≫ U.fromSpecStalkOfMem _ hU, ⟨⟨_, hU⟩, rfl⟩, ?_, ?_⟩
    · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hm]
    · rw [Category.assoc, ← h₁]
      exact (hφ _ m e (he.trans hm.symm)).symm
  choose U k hk ψ l hy hl hψ using loc
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y U k (fun y => ⟨y, hy y⟩) hk
  have hc : ∀ a b : Y, pullback.fst (k a) (k b) ≫ ψ a = pullback.snd (k a) (k b) ≫ ψ b := by
    intro a b
    let m := pullback.lift (l a) (l b) ((hl a).trans (hl b).symm)
    have : IsReduced (pullback (k a) (k b)) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ k a)
    have : IsDominant (m ≫ pullback.fst _ _ ≫ k a) := by
      rw [pullback.lift_fst_assoc, hl]
      infer_instance
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ k a)
    refine ext_of_isDominant m ?_
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hψ, hψ]
  have hι : ∀ a : Y, k a ≫ 𝒰.glueMorphisms ψ hc = ψ a := fun a => 𝒰.ι_glueMorphisms ψ hc a
  have h1 : j ≫ 𝒰.glueMorphisms ψ hc = F := by
    have : IsReduced W := isReduced_of_isOpenImmersion j
    have : IsDominant (e ≫ j) := by rw [he]; infer_instance
    have : IsDominant e := .of_comp_of_isOpenImmersion e j
    refine ext_of_isDominant e ?_
    rw [reassoc_of% he, ← hl (genericPoint Y), Category.assoc, hι, hψ]
  refine ⟨_, h1, ext_of_isDominant j ?_⟩
  rw [reassoc_of% h1, hF]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `: IsLocalization.Away ϖ (FractionRing R)`. Use `(IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun a ha => ?_).2 inferInstance` and prove the remaining obligations. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ`. Conclude with `⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩`.

Conclude with `IsOpenImmersion.of_isLocalization ϖ`.
-/
theorem isOpenImmersion_jK (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsOpenImmersion (jK R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

/- English proof (translation)
Distinguish the cases in `h : s.asIdeal = ⊥`. Use `(hs ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩).elim` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)`. Conclude with `PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (s.isPrime.isMaximal h))`.
-/
theorem eq_closedPoint_of_not_mem_range (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (s : Spec (CommRingCat.of R)) (hs : s ∉ Set.range (jK R)) : s = IsLocalRing.closedPoint R := by
  by_cases h : s.asIdeal = ⊥
  · refine (hs ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩).elim
    rw [h]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  · exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (s.isPrime.isMaximal h))

/- English proof (translation)
Introduce `R _ _ _ X' X _ _ _ _ f H`. Use `isOpenImmersion_jK R` as an intermediate fact. Establish `: IsDominant (jK R)` using `DVR.isDominant_jK`. Use `IsSchemeTheoreticallyDominant.of_isDominant (jK R)` as an intermediate fact. Establish `: IsDominant (pullback.fst X'.hom (jK R))` using `inferInstance`.

Establish `hf : f.left ≫ pullback.snd X.hom (jK R) = pullback.snd X'.hom (jK R)` using `Over.w f`. Take `⟨ψ, h₁, h₂⟩` from `exists_extension (pullback.fst X'.hom (jK R)) X'.hom X.hom (f.left ≫ pullback.fst X.hom (jK R)) (by rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]; congr 1) (fun y hy => H y (eq_closedPoint_of_not_mem_range R _ fun h => hy (by`. Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `h)))`. Use `⟨Over.homMk ψ h₂, Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩` and prove the remaining obligations.

Conclude with `(pullback.lift_fst _ _ _).trans h₁`. Conclude with `(Over.w _).trans hf.symm`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X' X : Over (Spec (CommRingCat.of R))) [Flat X'.hom] [IsIntegral X'.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] (f : (Over.pullback (jK R)).obj X' ⟶ (Over.pullback (jK R)).obj X), (∀ x : X'.left, X'.hom x = IsLocalRing.closedPoint R → ∃ (T : Scheme.{0}) (g' : T ⟶ X'.left) (g : T ⟶ X.left), Flat g' ∧ x ∈ Set.range g' ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj X').left), r ≫ pullback.fst X'.hom (jK R) = ρ ≫ g' → r ≫ f.left ≫ pullback.fst X.hom (jK R) = ρ ≫ g) → ∃ ψ : X' ⟶ X, (Over.pullback (jK R)).map ψ = f := by
  intro R _ _ _ X' X _ _ _ _ f H
  have := isOpenImmersion_jK R
  have : IsDominant (jK R) := DVR.isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsDominant (pullback.fst X'.hom (jK R)) := inferInstance
  have hf : f.left ≫ pullback.snd X.hom (jK R) = pullback.snd X'.hom (jK R) := Over.w f
  obtain ⟨ψ, h₁, h₂⟩ := exists_extension (pullback.fst X'.hom (jK R)) X'.hom X.hom
    (f.left ≫ pullback.fst X.hom (jK R))
    (by rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]; congr 1)
    (fun y hy => H y (eq_closedPoint_of_not_mem_range R _ fun h => hy (by
      rw [Scheme.Pullback.range_fst]; exact h)))
  refine ⟨Over.homMk ψ h₂, Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
  · exact (pullback.lift_fst _ _ _).trans h₁
  · exact (Over.w _).trans hf.symm

end GlobalTheory.GenericExt
