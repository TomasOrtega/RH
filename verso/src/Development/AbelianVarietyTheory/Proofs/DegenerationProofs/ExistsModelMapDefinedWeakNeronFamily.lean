import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SS.WeakNeronDef

/- English proof (translation)
Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv, ← Scheme.ΓSpecIso_inv_naturality]`. Simplify using the standard rewrite rules.
-/
theorem fromSpecStalk_comp {X : Scheme.{0}} {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p =
      Spec.map ((Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `h : genericPoint X ∈ Set.range (X.fromSpecStalk x)`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `(genericPoint_spec X).specializes trivial`. Establish `h2 : Dense ({genericPoint X} : Set X)`.

Rewrite using `[dense_iff_closure_eq]`. Conclude with `genericPoint_spec X`. Conclude with `h2.mono (Set.singleton_subset_iff.2 h)`.
-/
theorem isDominant_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (x : X) : IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

/- English proof (translation)
Establish `h` using `Over.w N.e.inv`. Establish `: IsIso N.e.inv.left` using `inferInstanceAs (IsIso ((Over.forget _).map N.e.inv))`. Use `IsPullback.of_iso (IsPullback.of_hasPullback N.Y.hom (spMap (algebraMap R K))) (asIso N.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)` and prove the remaining obligations. Simplify using `[Model.j]`. Simplify using `[← h]`.
-/
theorem isPullback_j (N : Model R A) : IsPullback N.j A.hom N.Y.hom (spMap (algebraMap R K)) := by
  have h := Over.w N.e.inv
  have : IsIso N.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map N.e.inv))
  refine IsPullback.of_iso (IsPullback.of_hasPullback N.Y.hom (spMap (algebraMap R K)))
    (asIso N.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j]
  · simp [← h]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

/- English proof (translation)
Use `N.smooth` as an intermediate fact. Establish `hs` using `IsPullback.of_hasPullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))`. Use `set i := pullback.fst N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hi`. Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))` using `IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective`. Establish `: IsClosedImmersion i` using `by rw [hi]; infer_instance`.

Use `GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))` as an intermediate fact. Establish `hr : Set.range i = N.sp` using `Set.ext fun x => DvrModel.mem_range_special hs x`. Establish `: IrreducibleSpace ↥(pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))`. Establish `h1 : IrreducibleSpace (Set.range i)`. Rewrite using `[hr]`.

Conclude with `Subtype.irreducibleSpace hN`. Conclude with `i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.surjective.irreducibleSpace i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.continuous`. Use `isIntegral_of_irreducibleSpace_of_isReduced (pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))` as an intermediate fact. Conclude with `⟨_, hr.le ⟨_, rfl⟩, DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs⟩`.
-/
theorem exists_dvr_point (N : Model R A) [IsIntegral N.Y.left] (hN : N.Irr) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ y ∈ N.sp, IsDiscreteValuationRing (N.Y.left.presheaf.stalk y) ∧
      Irreducible (((Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫
        N.Y.left.presheaf.germ ⊤ y trivial).hom ϖ) := by
  have := N.smooth
  have hs := IsPullback.of_hasPullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  set i := pullback.fst N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hi
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : IsClosedImmersion i := by rw [hi]; infer_instance
  have := GlobalTheory.isReduced_of_smooth_of_isReduced
    (pullback.snd N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  have hr : Set.range i = N.sp := Set.ext fun x => DvrModel.mem_range_special hs x
  have : IrreducibleSpace ↥(pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
    have h1 : IrreducibleSpace (Set.range i) := by
      rw [hr]; exact Subtype.irreducibleSpace hN
    exact i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.surjective.irreducibleSpace
      i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.continuous
  have := isIntegral_of_irreducibleSpace_of_isReduced
    (pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact ⟨_, hr.le ⟨_, rfl⟩, DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs⟩

end GlobalTheory.SS.WeakNeronDef

namespace GlobalTheory.SS

open WeakNeronDef

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ A _ I M hM N hN`. Use `N.smooth` as an intermediate fact. Establish `hK` using `isPullback_j N`. Establish `: IsIntegral N.Y.left` using `DvrModel.isIntegral hK`. Establish `: IsOpenImmersion N.j` using `DvrModel.isOpenImmersion_generic hK`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Take `⟨y, hy, hd, hi⟩` from `exists_dvr_point N hN hϖ`. Set `ψ` to `(Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫ N.Y.left.presheaf.germ ⊤ y trivial`. Set `R' : Type` to `N.Y.left.presheaf.stalk y`. Set `K' : Type` to `FractionRing R'`.

Use `letI : Algebra R R' := ψ.hom.toAlgebra`. Set `s : Sp R' ⟶ N.Y.left` to `N.Y.left.fromSpecStalk y`. Establish `hs : s ≫ N.Y.hom = spMap (algebraMap R R')` using `fromSpecStalk_comp N.Y.hom y`. Establish `hi' : Irreducible (algebraMap R R' ϖ)` using `hi`. Use `DvrModel.isLocalization_away K hϖ` as an intermediate fact.

Establish `hu : IsUnit (((algebraMap R' K').comp (algebraMap R R')) ϖ)` using `((map_ne_zero_iff _ (IsFractionRing.injective R' K')).2 hi'.ne_zero).isUnit`. Set `k : K →+* K'` to `IsLocalization.Away.lift ϖ hu`. Establish `hk : spMap k ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R'))`. Rewrite using `[← Spec.map_comp, ← IsLocalization.Away.lift_comp ϖ (S := K) hu]`. Both sides reduce to the same expression.

Establish `hw : (spMap (algebraMap R' K') ≫ s) ≫ N.Y.hom = spMap k ≫ spMap (algebraMap R K)`. Rewrite using `[hk, Category.assoc, hs, ← Spec.map_comp]`. Both sides reduce to the same expression. Set `a` to `hK.lift _ _ hw`. Establish `ha : a ≫ N.j = spMap (algebraMap R' K') ≫ s` using `hK.lift_fst _ _ _`.

Establish `ha' : a ≫ A.hom = spMap k` using `hK.lift_snd _ _ _`. Take `⟨i, b, hb, hb'⟩` from `hM R' K' (by`. Rewrite using `[hϖ.maximalIdeal_eq, hi'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]) a`. Use the proof step `(by rw [← Category.assoc, ha', hk])`. Use `(M i).smooth` as an intermediate fact.

Use `(M i).sep` as an intermediate fact. Take `⟨U, hU, g, h₁, h₂⟩` from `spread_out_of_isGermInjective' N.Y.hom (M i).Y.hom (x := y) b (hb.trans hs.symm)`. Use `⟨i, y, hy, U, g, hU, h₂, ?_⟩` and prove the remaining obligations. Set `t : Sp R' ⟶ U.toScheme` to `U.fromSpecStalkOfMem y hU`. Establish `ht : t ≫ U.ι = s` using `Scheme.Opens.fromSpecStalkOfMem_ι _ _ _`.

Establish `hP` using `isPullback_morphismRestrict N.j U`. Establish `hc : a ≫ N.j = (spMap (algebraMap R' K') ≫ t) ≫ U.ι` using `by rw [ha, Category.assoc, ht]`. Set `c` to `hP.lift _ _ hc.symm`. Establish `hc₁ : c ≫ (N.j ⁻¹ᵁ U).ι = a` using `hP.lift_snd _ _ _`. Establish `hc₂ : c ≫ (N.j ∣_ U) = spMap (algebraMap R' K') ≫ t` using `hP.lift_fst _ _ _`.

Establish `: IsDominant s` using `isDominant_fromSpecStalk _ _`. Use `GlobalTheory.isDominant_spMap_of_isFractionRing R' K'` as an intermediate fact. Establish `: IsDominant (c ≫ (N.j ⁻¹ᵁ U).ι ≫ N.j)`. Rewrite using `[← Category.assoc, hc₁, ha]`. Use `infer_instance`.

Establish `: IsDominant c` using `IsDominant.of_comp_of_isOpenImmersion c ((N.j ⁻¹ᵁ U).ι ≫ N.j)`. Use `ext_of_isDominant_of_isSeparated (M i).Y.hom ?_ c ?_` and prove the remaining obligations. Simplify using `only [Category.assoc, h₂, Over.id_left, Category.id_comp, Model.j_hom]`. Rewrite using `[morphismRestrict_ι_assoc, Model.j_hom]`. Simplify using `only [Over.id_left, Category.id_comp]`.

Rewrite using `[← Category.assoc, hc₂, ← Category.assoc, hc₁, ← hb', Category.assoc]`. Conclude with `congrArg _ h₁.symm`.
-/
theorem exists_defAt_of_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  intro R K _ _ _ _ _ _ A _ I M hM N hN
  have := N.smooth
  have hK := isPullback_j N
  have : IsIntegral N.Y.left := DvrModel.isIntegral hK
  have : IsOpenImmersion N.j := DvrModel.isOpenImmersion_generic hK
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨y, hy, hd, hi⟩ := exists_dvr_point N hN hϖ
  let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫ N.Y.left.presheaf.germ ⊤ y trivial
  let R' : Type := N.Y.left.presheaf.stalk y
  let K' : Type := FractionRing R'
  letI : Algebra R R' := ψ.hom.toAlgebra
  let s : Sp R' ⟶ N.Y.left := N.Y.left.fromSpecStalk y
  have hs : s ≫ N.Y.hom = spMap (algebraMap R R') := fromSpecStalk_comp N.Y.hom y
  have hi' : Irreducible (algebraMap R R' ϖ) := hi
  have := DvrModel.isLocalization_away K hϖ
  have hu : IsUnit (((algebraMap R' K').comp (algebraMap R R')) ϖ) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R' K')).2 hi'.ne_zero).isUnit
  let k : K →+* K' := IsLocalization.Away.lift ϖ hu
  have hk : spMap k ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) := by
    rw [← Spec.map_comp, ← IsLocalization.Away.lift_comp ϖ (S := K) hu]; rfl
  have hw : (spMap (algebraMap R' K') ≫ s) ≫ N.Y.hom = spMap k ≫ spMap (algebraMap R K) := by
    rw [hk, Category.assoc, hs, ← Spec.map_comp]; rfl
  let a := hK.lift _ _ hw
  have ha : a ≫ N.j = spMap (algebraMap R' K') ≫ s := hK.lift_fst _ _ _
  have ha' : a ≫ A.hom = spMap k := hK.lift_snd _ _ _
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' (by
    rw [hϖ.maximalIdeal_eq, hi'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]) a
    (by rw [← Category.assoc, ha', hk])
  have := (M i).smooth
  have := (M i).sep
  obtain ⟨U, hU, g, h₁, h₂⟩ := spread_out_of_isGermInjective' N.Y.hom (M i).Y.hom (x := y) b (hb.trans hs.symm)
  refine ⟨i, y, hy, U, g, hU, h₂, ?_⟩
  let t : Sp R' ⟶ U.toScheme := U.fromSpecStalkOfMem y hU
  have ht : t ≫ U.ι = s := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hP := isPullback_morphismRestrict N.j U
  have hc : a ≫ N.j = (spMap (algebraMap R' K') ≫ t) ≫ U.ι := by rw [ha, Category.assoc, ht]
  let c := hP.lift _ _ hc.symm
  have hc₁ : c ≫ (N.j ⁻¹ᵁ U).ι = a := hP.lift_snd _ _ _
  have hc₂ : c ≫ (N.j ∣_ U) = spMap (algebraMap R' K') ≫ t := hP.lift_fst _ _ _
  have : IsDominant s := isDominant_fromSpecStalk _ _
  have := GlobalTheory.isDominant_spMap_of_isFractionRing R' K'
  have : IsDominant (c ≫ (N.j ⁻¹ᵁ U).ι ≫ N.j) := by
    rw [← Category.assoc, hc₁, ha]; infer_instance
  have : IsDominant c := IsDominant.of_comp_of_isOpenImmersion c ((N.j ⁻¹ᵁ U).ι ≫ N.j)
  refine ext_of_isDominant_of_isSeparated (M i).Y.hom ?_ c ?_
  · simp only [Category.assoc, h₂, Over.id_left, Category.id_comp, Model.j_hom]
    rw [morphismRestrict_ι_assoc, Model.j_hom]
  · simp only [Over.id_left, Category.id_comp]
    rw [← Category.assoc, hc₂, ← Category.assoc, hc₁, ← hb', Category.assoc]
    exact congrArg _ h₁.symm

end GlobalTheory.SS
