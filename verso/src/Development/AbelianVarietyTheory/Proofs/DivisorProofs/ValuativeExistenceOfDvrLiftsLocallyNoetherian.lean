import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DvrCriterion

open Scheme.IdealSheafData TopologicalSpace

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `X' Y' i₁ i₂ f' H`. Establish `c` using `fun i ↦ (h i).universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ (g i)).paste_horiz H)`. Introduce `Zs hZ`. Establish `e : f' '' Zs = ⋃ i, (pullback.fst i₁ (g i) ≫ f') '' (pullback.fst i₁ (g i) ⁻¹' Zs)`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨i, a, ha⟩` from `hcov (i₁ x)`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback x a ha.symm`. Conclude with `Set.mem_iUnion.2 ⟨i, z, by simpa [hz] using hx, by simp [hz]⟩`.

Introduce `y hy`. Take `⟨i, z, hz, rfl⟩` from `Set.mem_iUnion.1 hy`. Conclude with `⟨_, hz, by simp⟩`. Rewrite using `[e]`. Conclude with `isClosed_iUnion_of_finite fun i ↦ c i _ (hZ.preimage (Scheme.Hom.continuous _))`.
-/
theorem universallyClosed_of_finite_jointly_surjective {ι : Type} [Finite ι] {X Z : Scheme.{0}}
    (A : ι → Scheme.{0}) (g : ∀ i, A i ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, ∃ i, ∃ a, g i a = x)
    (h : ∀ i, UniversallyClosed (g i ≫ k)) : UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c := fun i ↦ (h i).universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ (g i)).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = ⋃ i, (pullback.fst i₁ (g i) ≫ f') '' (pullback.fst i₁ (g i) ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, a, ha⟩ := hcov (i₁ x)
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
      exact Set.mem_iUnion.2 ⟨i, z, by simpa [hz] using hx, by simp [hz]⟩
    · intro y hy
      obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
      exact ⟨_, hz, by simp⟩
  rw [e]
  exact isClosed_iUnion_of_finite fun i ↦ c i _ (hZ.preimage (Scheme.Hom.continuous _))

/- English proof (translation)
Use `set s := pullback.snd π u with hs`. Establish `: CompactSpace (pullback π u : Scheme.{0})` using `QuasiCompact.compactSpace_of_compactSpace s`. Establish `: IsLocallyNoetherian (pullback π u : Scheme.{0})` using `LocallyOfFiniteType.isLocallyNoetherian s`. Establish `: IsNoetherian (pullback π u : Scheme.{0})` using `{}`. Set `C : irreducibleComponents (pullback π u : Scheme.{0}) → Closeds (pullback π u : Scheme.{0})` to `fun c ↦ ⟨c.1, isClosed_of_mem_irreducibleComponents _ c.2⟩`.

Establish `: Finite (irreducibleComponents (pullback π u : Scheme.{0}))` using `NoetherianSpace.finite_irreducibleComponents.to_subtype`. Establish `hr : ∀ c, Set.range (vanishingIdeal (C c)).subschemeι = c.1` using `fun c ↦ by`. Rewrite using `[range_subschemeι, coe_support_vanishingIdeal]`. Both sides reduce to the same expression. Use `universallyClosed_of_finite_jointly_surjective (fun c ↦ (vanishingIdeal (C c)).subscheme) (fun c ↦ (vanishingIdeal (C c)).subschemeι) s (fun x ↦ ?_) (fun c ↦ ?_)` and prove the remaining obligations.

Use `⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩` and prove the remaining obligations. Establish `: x ∈ Set.range (vanishingIdeal (C ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩)).subschemeι`. Rewrite using `[hr]`. Conclude with `mem_irreducibleComponent`. Conclude with `this`.

Use `set I := vanishingIdeal (C c)`. Establish `: IsReduced I.subscheme` using `GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _`. Establish `: IrreducibleSpace (Set.range I.subschemeι)`. Establish `h1 : IsIrreducible (Set.range I.subschemeι)` using `by rw [hr]; exact c.2.1`. Conclude with `Subtype.irreducibleSpace h1`.

Establish `: IrreducibleSpace I.subscheme` using `I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.2 this`. Establish `: IsIntegral I.subscheme` using `isIntegral_of_irreducibleSpace_of_isReduced _`. Establish `hP : IsProper (I.subschemeι ≫ s)`. Use `GlobalTheory.TraitProper.isProper_of_lift_genericPoint R I.subscheme (I.subschemeι ≫ s) ?_` and prove the remaining obligations. Introduce `V K _ _ _ _ _ _ _ x y _ hxy`.

Set `e : FractionRing V ≃ₐ[V] K` to `IsLocalization.algEquiv (nonZeroDivisors V) (FractionRing V) K`. Set `ε : K →+* FractionRing V` to `e.symm.toRingEquiv.toRingHom`. Set `ε' : FractionRing V →+* K` to `e.toRingEquiv.toRingHom`. Establish `he1 : Spec.map (CommRingCat.ofHom ε) ≫ spMap (algebraMap V K) = Out.jK V`. Rewrite using `[spMap, ← Spec.map_comp]`.

Use `congr 2`. Use extensionality with `a`. Conclude with `e.symm.commutes a`. Establish `he2 : Spec.map (CommRingCat.ofHom ε') ≫ Out.jK V = spMap (algebraMap V K)`. Rewrite using `[spMap, Out.jK, ← Spec.map_comp]`.

Use `congr 2`. Use extensionality with `a`. Conclude with `e.commutes a`. Establish `he3 : Spec.map (CommRingCat.ofHom ε') ≫ Spec.map (CommRingCat.ofHom ε) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`.

Use `congr 2`. Use extensionality with `a`. Conclude with `e.apply_symm_apply a`. Set `xF : Sp (FractionRing V) ⟶ Y` to `Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι ≫ pullback.fst π u`. Establish `hxF : xF ≫ π = Out.jK V ≫ (y ≫ u)`.

Establish `: xF ≫ π = Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) ≫ u`. Simplify using `[xF, hs, pullback.condition]`. Rewrite using `[this, hxy, ← he1]`. Simplify using the standard rewrite rules. Take `⟨x'', hx1, hx2⟩` from `H V xF (y ≫ u) hxF`.

Set `x3 : Sp V ⟶ pullback π u` to `pullback.lift x'' y hx2`. Establish `h3 : Out.jK V ≫ x3 = Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [x3, Category.assoc, pullback.lift_fst]`. Conclude with `hx1`.

Establish `: Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) = Out.jK V ≫ y`. Rewrite using `[hxy, ← he1]`. Simplify using the standard rewrite rules. Simplify using `only [x3, Category.assoc, pullback.lift_snd]`. Conclude with `this.symm`.

Establish `hdom : IsDominant (Out.jK V)`. Establish `hinj : Function.Injective (algebraMap V (FractionRing V))` using `IsFractionRing.injective _ _`. Use `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩` and prove the remaining obligations. Conclude with `((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le`. Establish `hrange : Set.range x3 ⊆ (C c : Set (pullback π u : Scheme.{0}))`.

Introduce and unpack `_ ⟨v, rfl⟩`. Establish `hv : v ∈ closure (Set.range (Out.jK V))` using `(Out.jK V).denseRange v`. Use `map_mem_closure x3.continuous hv (t := (C c : Set (pullback π u : Scheme.{0}))) (by` as an intermediate fact. Introduce and unpack `_ ⟨w, rfl⟩`. Express the relevant statement in the definitionally equal form `x3 (Out.jK V w) ∈ c.1`.

Rewrite using `[← Scheme.Hom.comp_apply, h3, ← hr c]`. Conclude with `⟨(Spec.map (CommRingCat.ofHom ε) ≫ x) w, by rw [← Scheme.Hom.comp_apply, Category.assoc]⟩)`. Rewrite `this` using `[(C c).isClosed.closure_eq]`. Then use the resulting hypothesis. Establish `hker : I.subschemeι.ker ≤ x3.ker`. Rewrite using `[I.ker_subschemeι]`.

Conclude with `GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker x3 (C c) hrange`. Use `⟨IsClosedImmersion.lift I.subschemeι x3 hker, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac, ← he2, Category.assoc, h3, ← Category.assoc, ← Category.assoc, he3, Category.id_comp]`. Conclude with `inferInstance`.
-/
theorem universallyClosed_snd_of_lift {Y S : Scheme.{0}} (π : Y ⟶ S) [LocallyOfFiniteType π]
    [QuasiCompact π] [IsSeparated π] (R : Type) [CommRing R] [IsNoetherianRing R] (u : Sp R ⟶ S)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y →
        ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) :
    UniversallyClosed (pullback.snd π u) := by
  classical
  set s := pullback.snd π u with hs
  have : CompactSpace (pullback π u : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian (pullback π u : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian (pullback π u : Scheme.{0}) := {}
  let C : irreducibleComponents (pullback π u : Scheme.{0}) → Closeds (pullback π u : Scheme.{0}) :=
    fun c ↦ ⟨c.1, isClosed_of_mem_irreducibleComponents _ c.2⟩
  have : Finite (irreducibleComponents (pullback π u : Scheme.{0})) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hr : ∀ c, Set.range (vanishingIdeal (C c)).subschemeι = c.1 := fun c ↦ by
    rw [range_subschemeι, coe_support_vanishingIdeal]; rfl
  refine universallyClosed_of_finite_jointly_surjective (fun c ↦ (vanishingIdeal (C c)).subscheme)
    (fun c ↦ (vanishingIdeal (C c)).subschemeι) s (fun x ↦ ?_) (fun c ↦ ?_)
  · refine ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    have : x ∈ Set.range (vanishingIdeal (C ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩)).subschemeι := by
      rw [hr]; exact mem_irreducibleComponent
    exact this
  set I := vanishingIdeal (C c)
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace (Set.range I.subschemeι) := by
    have h1 : IsIrreducible (Set.range I.subschemeι) := by rw [hr]; exact c.2.1
    exact Subtype.irreducibleSpace h1
  have : IrreducibleSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.2 this
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hP : IsProper (I.subschemeι ≫ s) := by
    refine GlobalTheory.TraitProper.isProper_of_lift_genericPoint R I.subscheme (I.subschemeι ≫ s) ?_
    intro V K _ _ _ _ _ _ _ x y _ hxy
    let e : FractionRing V ≃ₐ[V] K := IsLocalization.algEquiv (nonZeroDivisors V) (FractionRing V) K
    let ε : K →+* FractionRing V := e.symm.toRingEquiv.toRingHom
    let ε' : FractionRing V →+* K := e.toRingEquiv.toRingHom
    have he1 : Spec.map (CommRingCat.ofHom ε) ≫ spMap (algebraMap V K) = Out.jK V := by
      rw [spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact e.symm.commutes a
    have he2 : Spec.map (CommRingCat.ofHom ε') ≫ Out.jK V = spMap (algebraMap V K) := by
      rw [spMap, Out.jK, ← Spec.map_comp]
      congr 2
      ext a
      exact e.commutes a
    have he3 : Spec.map (CommRingCat.ofHom ε') ≫ Spec.map (CommRingCat.ofHom ε) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 2
      ext a
      exact e.apply_symm_apply a
    let xF : Sp (FractionRing V) ⟶ Y :=
      Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι ≫ pullback.fst π u
    have hxF : xF ≫ π = Out.jK V ≫ (y ≫ u) := by
      have : xF ≫ π = Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) ≫ u := by
        simp [xF, hs, pullback.condition]
      rw [this, hxy, ← he1]
      simp
    obtain ⟨x'', hx1, hx2⟩ := H V xF (y ≫ u) hxF
    let x3 : Sp V ⟶ pullback π u := pullback.lift x'' y hx2
    have h3 : Out.jK V ≫ x3 = Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι := by
      apply pullback.hom_ext
      · simp only [x3, Category.assoc, pullback.lift_fst]
        exact hx1
      · have : Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) = Out.jK V ≫ y := by
          rw [hxy, ← he1]; simp
        simp only [x3, Category.assoc, pullback.lift_snd]
        exact this.symm
    have hdom : IsDominant (Out.jK V) := by
      have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hrange : Set.range x3 ⊆ (C c : Set (pullback π u : Scheme.{0})) := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ closure (Set.range (Out.jK V)) := (Out.jK V).denseRange v
      have := map_mem_closure x3.continuous hv (t := (C c : Set (pullback π u : Scheme.{0}))) (by
        rintro _ ⟨w, rfl⟩
        change x3 (Out.jK V w) ∈ c.1
        rw [← Scheme.Hom.comp_apply, h3, ← hr c]
        exact ⟨(Spec.map (CommRingCat.ofHom ε) ≫ x) w, by rw [← Scheme.Hom.comp_apply, Category.assoc]⟩)
      rwa [(C c).isClosed.closure_eq] at this
    have hker : I.subschemeι.ker ≤ x3.ker := by
      rw [I.ker_subschemeι]
      exact GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker x3 (C c) hrange
    refine ⟨IsClosedImmersion.lift I.subschemeι x3 hker, ?_⟩
    rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac, ← he2,
      Category.assoc, h3, ← Category.assoc, ← Category.assoc, he3, Category.id_comp]
  exact inferInstance

/- English proof (translation)
Introduce `Y S _ π _ _ _ H`. Establish `hUC : UniversallyClosed π`. Rewrite using `[IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) S.affineOpenCover.openCover]`. Introduce `i`. Use `S.affineOpenCover.map_prop i` as an intermediate fact.

Establish `hR : IsNoetherianRing (S.affineOpenCover.X i)` using `isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion (S.affineOpenCover.f i))`. Conclude with `@universallyClosed_snd_of_lift Y S π _ _ _ (S.affineOpenCover.X i) _ hR (S.affineOpenCover.openCover.f i) H`. Establish `h` using `hUC`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.
-/
theorem existence_of_lift_discreteValuationRing : ∀ {Y S : Scheme.{0}} [IsLocallyNoetherian S] (π : Y ⟶ S), LocallyOfFiniteType π → QuasiCompact π → IsSeparated π → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y → ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) → ValuativeCriterion.Existence π := by
  intro Y S _ π _ _ _ H
  have hUC : UniversallyClosed π := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) S.affineOpenCover.openCover]
    intro i
    have := S.affineOpenCover.map_prop i
    have hR : IsNoetherianRing (S.affineOpenCover.X i) :=
      isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion (S.affineOpenCover.f i))
    exact @universallyClosed_snd_of_lift Y S π _ _ _ (S.affineOpenCover.X i) _ hR
      (S.affineOpenCover.openCover.f i) H
  have h := hUC
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

end GlobalTheory.DvrCriterion
