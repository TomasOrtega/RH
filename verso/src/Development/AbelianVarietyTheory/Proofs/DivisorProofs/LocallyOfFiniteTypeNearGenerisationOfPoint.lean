import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrimeStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.USpread

/- English proof (translation)
Establish `h1` using `(IsPullback.of_hasPullback j (pullback.fst q s)).paste_vert (IsPullback.of_hasPullback q s)`. Establish `h2` using `(IsPullback.of_hasPullback (pullback.snd j (pullback.fst q s) ≫ pullback.snd q s) t).paste_horiz h1`. Rewrite using `[← h.isoIsPullback_hom_snd _ _ h2]`. Use `infer_instance`.
-/
theorem lft_of_pullback {X V P S T Y : Scheme.{0}} (j : X ⟶ V) (q : V ⟶ P) (s : S ⟶ P) (t : T ⟶ S)
    (u : Y ⟶ X) (b : Y ⟶ T) [LocallyOfFiniteType j] [LocallyOfFiniteType (pullback.snd q s)]
    (h : IsPullback u b (j ≫ q) (t ≫ s)) : LocallyOfFiniteType b := by
  have h1 := (IsPullback.of_hasPullback j (pullback.fst q s)).paste_vert (IsPullback.of_hasPullback q s)
  have h2 := (IsPullback.of_hasPullback (pullback.snd j (pullback.fst q s) ≫ pullback.snd q s) t).paste_horiz h1
  rw [← h.isoIsPullback_hom_snd _ _ h2]
  infer_instance

/- English proof (translation)
Set `y : PrimeSpectrum R` to `x`. Use `haveI := StructureSheaf.IsLocalization.to_stalk R y`. Set `e` to `IsLocalization.algEquiv (R := R) y.asIdeal.primeCompl ((Spec.structureSheaf R).presheaf.stalk y) (Localization.AtPrime y.asIdeal)`. Use `⟨Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom), ?_⟩` and prove the remaining obligations. Use `Scheme.Spec_fromSpecStalk' (CommRingCat.of R) x` as an intermediate fact.

Use `erw [this, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `r`. Conclude with `e.commutes r`.
-/
theorem exists_to_stalk (R : Type) [CommRing R] (x : Sp R) [x.asIdeal.IsPrime] :
    ∃ t : Sp (Localization.AtPrime x.asIdeal) ⟶ Spec ((Sp R).presheaf.stalk x),
      t ≫ (Sp R).fromSpecStalk x =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime x.asIdeal))) := by
  let y : PrimeSpectrum R := x
  haveI := StructureSheaf.IsLocalization.to_stalk R y
  let e := IsLocalization.algEquiv (R := R) y.asIdeal.primeCompl
    ((Spec.structureSheaf R).presheaf.stalk y) (Localization.AtPrime y.asIdeal)
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom), ?_⟩
  have := Scheme.Spec_fromSpecStalk' (CommRingCat.of R) x
  erw [this, ← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

/- English proof (translation)
Set `D` to `Localization.Away (algebraMap R C f)`. Establish `hu : IsUnit (algebraMap R D f)`. Rewrite using `[IsScalarTower.algebraMap_apply R C D]`. Conclude with `IsLocalization.Away.algebraMap_isUnit _`. Set `ψ : Localization.Away f →+* D` to `IsLocalization.Away.lift f hu`.

Establish `hψ : ψ.comp (algebraMap R (Localization.Away f)) = algebraMap R D` using `IsLocalization.Away.lift_comp f hu`. Set `k : Sp D ⟶ Sp C` to `Spec.map (CommRingCat.ofHom (algebraMap C D))`. Use `haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C f)`. Establish `hψ' : Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f = Spec.map (CommRingCat.ofHom (algebraMap R D))`. Rewrite using `[← hψ, CommRingCat.ofHom_comp, Spec.map_comp]`.

Establish `w : (k ≫ j) ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f`. Rewrite using `[hψ', Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp, Spec.map_comp]`. Use `haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f`. Use `haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›`. Set `l` to `h.lift _ _ w`.

Establish `hl : l ≫ ιA = k ≫ j` using `h.lift_fst _ _ w`. Use `haveI : IsOpenImmersion (l ≫ ιA) := by rw [hl]; infer_instance`. Use `haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l ιA`. Establish `: LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D)))`. Rewrite using `[← hψ', ← h.lift_snd _ _ w]`.

Express the relevant statement in the definitionally equal form `LocallyOfFiniteType ((l ≫ a) ≫ _)`. Use `infer_instance`. Conclude with `RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)`.
-/
theorem away_finiteType (R : Type) [CommRing R] (f : R) (P A : Scheme.{0})
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (C : Type) [CommRing C] [Algebra R C] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    Algebra.FiniteType R (Localization.Away (algebraMap R C f)) := by
  let D := Localization.Away (algebraMap R C f)
  have hu : IsUnit (algebraMap R D f) := by
    rw [IsScalarTower.algebraMap_apply R C D]
    exact IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away f →+* D := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R (Localization.Away f)) = algebraMap R D :=
    IsLocalization.Away.lift_comp f hu
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C f)
  have hψ' : Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  have w : (k ≫ j) ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f := by
    rw [hψ', Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
      Spec.map_comp]
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  let l := h.lift _ _ w
  have hl : l ≫ ιA = k ≫ j := h.lift_fst _ _ w
  haveI : IsOpenImmersion (l ≫ ιA) := by rw [hl]; infer_instance
  haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l ιA
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) := by
    rw [← hψ', ← h.lift_snd _ _ w]
    change LocallyOfFiniteType ((l ≫ a) ≫ _)
    infer_instance
  exact RingHom.finiteType_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)

/- English proof (translation)
Introduce `h0`. Use `haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f`. Use `haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›`. Take `⟨y, ⟨c, hc⟩, ⟨t, ht⟩⟩` from `nonempty_preirreducible_inter j.isOpenEmbedding.isOpen_range ιA.isOpenEmbedding.isOpen_range (Set.range_nonempty _) (Set.range_nonempty _)`. Establish `h1 : p y = PrimeSpectrum.comap (algebraMap R C) c`.

Rewrite using `[← hc, ← Scheme.Hom.comp_apply, hj]`. Both sides reduce to the same expression. Establish `h2 : p y = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (a t)`. Rewrite using `[← ht, ← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]`. Both sides reduce to the same expression.

Establish `h3 : f ∈ (PrimeSpectrum.comap (algebraMap R C) c).asIdeal`. Express the relevant statement in the definitionally equal form `algebraMap R C f ∈ c.asIdeal`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Rewrite `h3` using `[← h1, h2]`.

Conclude with `(a t).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 (IsLocalization.Away.algebraMap_isUnit f))`.
-/
theorem ne_zero (R : Type) [CommRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f))
    (C : Type) [CommRing C] [Algebra R C] [Nonempty (Sp C)] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    algebraMap R C f ≠ 0 := by
  intro h0
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  obtain ⟨y, ⟨c, hc⟩, ⟨t, ht⟩⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range ιA.isOpenEmbedding.isOpen_range
    (Set.range_nonempty _) (Set.range_nonempty _)
  have h1 : p y = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← hc, ← Scheme.Hom.comp_apply, hj]; rfl
  have h2 : p y = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (a t) := by
    rw [← ht, ← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]; rfl
  have h3 : f ∈ (PrimeSpectrum.comap (algebraMap R C) c).asIdeal := by
    change algebraMap R C f ∈ c.asIdeal
    rw [h0]; exact zero_mem _
  rw [← h1, h2] at h3
  exact (a t).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h3
    (IsLocalization.Away.algebraMap_isUnit f))

/- English proof (translation)
Use `haveI : Nonempty (Sp C) := ⟨c⟩`. Use `haveI := x.isPrime`. Establish `h1` using `ne_zero R f P A p ιA a h C (j ≫ V.ι) hj`. Establish `h2` using `away_finiteType R f P A p ιA a h C (j ≫ V.ι) hj`. Take `⟨t, ht⟩` from `exists_to_stalk R x`.

Establish `hpb` using `(isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R (Localization.AtPrime x.asIdeal) C)).flip`. Rewrite `hpb` using `[← hj, ← ht, Category.assoc]`. Establish `h3` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 (lft_of_pullback _ _ _ _ _ _ hpb)`. Establish `h4 : Algebra.FiniteType (Localization.AtPrime x.asIdeal) (TensorProduct R (Localization.AtPrime x.asIdeal) C)` using `RingHom.finiteType_algebraMap.1 h3`. Take `⟨g, hg, hft⟩` from `GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime R C f x.asIdeal h1 h2 h4`.

Set `D` to `Localization.Away (algebraMap R C g)`. Set `k : Sp D ⟶ Sp C` to `Spec.map (CommRingCat.ofHom (algebraMap C D))`. Use `haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C g)`. Establish `h5 : p ((j ≫ V.ι) c) = PrimeSpectrum.comap (algebraMap R C) c`. Rewrite using `[← Scheme.Hom.comp_apply, hj]`.

Both sides reduce to the same expression. Use `⟨(k ≫ j ≫ V.ι).opensRange, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: c ∈ Set.range (PrimeSpectrum.comap (algebraMap C D))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range D (algebraMap R C g)]`. Introduce `hgc`.

Apply `hg` to reduce the goal to its premises. Apply `hc` to reduce the goal to its premises. Rewrite using `[h5]`. Conclude with `hgc`. Take `⟨d, hd⟩` from `this`.

Conclude with `⟨d, by rw [Scheme.Hom.comp_apply, ← hd]; rfl⟩`. Introduce and unpack `_ ⟨d, rfl⟩`. Rewrite using `[← Category.assoc, Scheme.Hom.comp_apply]`. Conclude with `((k ≫ j) d).2`. Establish `: LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D)))` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 hft)`.

Establish `e : (k ≫ j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R D))`. Rewrite using `[Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp, Spec.map_comp]`. Rewrite using `[← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, e]`. Use `infer_instance`.
-/
theorem affine_case (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0})
    [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (x : Sp R) (V : P.Opens)
    [LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x))]
    (C : Type) [CommRing C] [IsDomain C] [Algebra R C] (j : Sp C ⟶ V) [IsOpenImmersion j]
    (hj : (j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (c : Sp C) (hc : (p ((j ≫ V.ι) c)).asIdeal ≤ x.asIdeal) :
    ∃ W : P.Opens, (j ≫ V.ι) c ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  haveI : Nonempty (Sp C) := ⟨c⟩
  haveI := x.isPrime
  have h1 := ne_zero R f P A p ιA a h C (j ≫ V.ι) hj
  have h2 := away_finiteType R f P A p ιA a h C (j ≫ V.ι) hj
  obtain ⟨t, ht⟩ := exists_to_stalk R x
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.AtPrime x.asIdeal) C)).flip
  rw [← hj, ← ht, Category.assoc] at hpb
  have h3 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1
    (lft_of_pullback _ _ _ _ _ _ hpb)
  have h4 : Algebra.FiniteType (Localization.AtPrime x.asIdeal)
      (TensorProduct R (Localization.AtPrime x.asIdeal) C) := RingHom.finiteType_algebraMap.1 h3
  obtain ⟨g, hg, hft⟩ := GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime R C f x.asIdeal h1 h2 h4
  let D := Localization.Away (algebraMap R C g)
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C g)
  have h5 : p ((j ≫ V.ι) c) = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← Scheme.Hom.comp_apply, hj]; rfl
  refine ⟨(k ≫ j ≫ V.ι).opensRange, ?_, ?_, ?_⟩
  · have : c ∈ Set.range (PrimeSpectrum.comap (algebraMap C D)) := by
      rw [PrimeSpectrum.localization_away_comap_range D (algebraMap R C g)]
      intro hgc
      apply hg
      apply hc
      rw [h5]
      exact hgc
    obtain ⟨d, hd⟩ := this
    exact ⟨d, by rw [Scheme.Hom.comp_apply, ← hd]; rfl⟩
  · rintro _ ⟨d, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact ((k ≫ j) d).2
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
        (RingHom.finiteType_algebraMap.2 hft)
    have e : (k ≫ j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
      rw [Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
        Spec.map_comp]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, e]
    infer_instance

/- English proof (translation)
Introduce `R _ _ f P A _ _ p ιA a h ha x V hV z hz hzx`. Take `⟨_, ⟨W₀, hW₀, rfl⟩, hzW, hWV⟩` from `P.isBasis_affineOpens.exists_subset_of_mem_open hz V.isOpen`. Use `replace hW₀ : IsAffineOpen W₀ := hW₀`. Use `haveI : Nonempty W₀ := ⟨⟨z, hzW⟩⟩`. Establish `hr : Set.range hW₀.fromSpec ⊆ Set.range V.ι`.

Rewrite using `[hW₀.range_fromSpec, Scheme.Opens.range_ι]`. Conclude with `hWV`. Set `j` to `IsOpenImmersion.lift V.ι hW₀.fromSpec hr`. Establish `hj : j ≫ V.ι = hW₀.fromSpec` using `IsOpenImmersion.lift_fac _ _ _`. Use `haveI : IsOpenImmersion (j ≫ V.ι) := by rw [hj]; infer_instance`.

Use `haveI : IsOpenImmersion j := IsOpenImmersion.of_comp j V.ι`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (hW₀.fromSpec ≫ p)`. Use `letI : Algebra R Γ(P, W₀) := φ.hom.toAlgebra`. Take `⟨c, hc⟩ : z ∈ Set.range hW₀.fromSpec` from `by rw [hW₀.range_fromSpec]; exact hzW`. Establish `hc' : (j ≫ V.ι) c = z` using `by rw [hj]; exact hc`.

Use `affine_case R f P A p ιA a h x V Γ(P, W₀) j (by rw [hj, ← hφ]; rfl) c (by erw [hc']; exact hzx)` as an intermediate fact. Use `erw [hc'] at this`. Conclude with `this`.
-/
theorem locally_finiteType_near : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (GlobalTheory.Desc.awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  intro R _ _ f P A _ _ p ιA a h ha x V hV z hz hzx
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW, hWV⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open hz V.isOpen
  replace hW₀ : IsAffineOpen W₀ := hW₀
  haveI : Nonempty W₀ := ⟨⟨z, hzW⟩⟩
  have hr : Set.range hW₀.fromSpec ⊆ Set.range V.ι := by
    rw [hW₀.range_fromSpec, Scheme.Opens.range_ι]; exact hWV
  let j := IsOpenImmersion.lift V.ι hW₀.fromSpec hr
  have hj : j ≫ V.ι = hW₀.fromSpec := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
  haveI : IsOpenImmersion j := IsOpenImmersion.of_comp j V.ι
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW₀.fromSpec ≫ p)
  letI : Algebra R Γ(P, W₀) := φ.hom.toAlgebra
  obtain ⟨c, hc⟩ : z ∈ Set.range hW₀.fromSpec := by rw [hW₀.range_fromSpec]; exact hzW
  have hc' : (j ≫ V.ι) c = z := by rw [hj]; exact hc
  have := affine_case R f P A p ιA a h x V Γ(P, W₀) j (by rw [hj, ← hφ]; rfl) c
    (by erw [hc']; exact hzx)
  erw [hc'] at this
  exact this

end GlobalTheory.USpread
