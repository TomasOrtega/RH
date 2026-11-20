import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TraitProper

open GlobalTheory.ArcProper in

/- English proof (translation)
Introduce `k _ _ Y _ s _ _ _ H`. Establish `: CompactSpace Y` using `QuasiCompact.compactSpace_of_compactSpace s`. Establish `: IsLocallyNoetherian Y` using `LocallyOfFiniteType.isLocallyNoetherian s`. Establish `hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A` using `fun y ↦ by`. Take `⟨A, h₁, h₂, -⟩` from `exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial`.

Conclude with `⟨A, h₁, h₂⟩`. Use `choose A₀ hA₀ hyA using hA`. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y)) (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)`. Set `A : T → Y.Opens` to `fun i ↦ A₀ i`. Establish `hcov : ∀ y : Y, ∃ i : T, y ∈ A i` using `fun y ↦ by`.

Take `⟨i, hi, h⟩` from `Set.mem_iUnion₂.1 (hT (Set.mem_univ y))`. Conclude with `⟨⟨i, hi⟩, h⟩`. Establish `hP` using `fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i exists_isOpenImmersion_isProper ((A i).ι ≫ s))`. Use `choose P t j ht hj hjt using hP`. Set `U : Y.Opens` to `Finset.univ.inf A`.

Establish `hUA : ∀ i, U ≤ A i` using `fun i ↦ Finset.inf_le (Finset.mem_univ i)`. Establish `hU : genericPoint Y ∈ U`. Establish `: ∀ i, genericPoint Y ∈ A i` using `fun i ↦ ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩`. Use `Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i` and prove the remaining obligations. Establish `: Nonempty U.toScheme` using `⟨⟨_, hU⟩⟩`.

Establish `: IsIntegral U.toScheme` using `isIntegral_of_isOpenImmersion U.ι`. Take `⟨Q, q, ψ, _, hψ, hp⟩` from `exists_isProper_factor P t ht (U.ι ≫ s) (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc]) Finset.univ`. Use `choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)`. Take `⟨i₀, -⟩` from `hcov (genericPoint Y)`. Establish `: IsImmersion (ψ ≫ p i₀)` using `by rw [hψp]; infer_instance`.

Establish `: IsImmersion ψ` using `IsImmersion.of_comp ψ (p i₀)`. Establish `: QuasiCompact (ψ ≫ q)` using `by rw [hψ]; infer_instance`. Establish `: QuasiCompact ψ` using `QuasiCompact.of_comp ψ q`. Establish `: IsIntegral ψ.image` using `isIntegral_image ψ`. Set `z : ψ.image ⟶ Sp k` to `ψ.imageι ≫ q`.

Establish `hz : ψ.toImage ≫ z = U.ι ≫ s` using `by rw [ψ.toImage_imageι_assoc, hψ]`. Establish `: IsLocallyNoetherian ψ.image` using `LocallyOfFiniteType.isLocallyNoetherian z`. Set `V : T → ψ.image.Opens` to `fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange`. Set `η : U.toScheme` to `⟨_, hU⟩`. Establish `hη : ∀ u : U.toScheme, η ⤳ u` using `fun u ↦ (U.ι.isEmbedding.isInducing.specializes_iff).1 (genericPoint_specializes (U.ι u))`.

Establish `hs : ∀ x : ψ.image, ψ.toImage η ⤳ x`. Introduce `x`. Rewrite using `[specializes_iff_mem_closure]`. Use `closure_minimal ?_ isClosed_closure (ψ.toImage.denseRange x)` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`.

Conclude with `specializes_iff_mem_closure.1 ((hη u).map ψ.toImage.continuous)`. Establish `key : ∀ x : ψ.image, ∃ i, x ∈ V i`. Introduce `x`. Distinguish the cases in `hne : ψ.toImage η = x`. Use `⟨i₀, Y.homOfLE (hUA i₀) η, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hne, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ψ.toImage_imageι_assoc, hψp]`. Take `⟨O, _, _, _, c, hc₀, hcx⟩` from `exists_complete_discreteValuationRing_of_specializes (hs x) hne`. Establish `hinj : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective _ _`. Establish `: IsDominant (spMap (algebraMap O (FractionRing O)))`. Use `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩` and prove the remaining obligations.

Conclude with `((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le`. Establish `hpt' : (spMap (algebraMap O (FractionRing O)) ≫ c) (IsLocalRing.closedPoint (FractionRing O)) = ψ.toImage η`. Use `Eq.trans (congrArg c (PrimeSpectrum.ext ?_)) hc₀` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`.

Conclude with `Ideal.comap_bot_of_injective _ hinj`. Take `⟨l, hl, hlη⟩` from `ValuativeGeneric.exists_lift_of_surjectiveOnStalks ψ.toImage (FractionRing O) _ η hpt'`. Establish `hls : (l ≫ U.ι) ≫ s = spMap (algebraMap O (FractionRing O)) ≫ c ≫ z`. Rewrite using `[Category.assoc, ← hz, reassoc_of% hl]`. Take `⟨b, hb⟩` from `H O (FractionRing O) (l ≫ U.ι) (c ≫ z) (by`.

Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply, hlη]`. Use the proof step `rfl) hls`. Establish `hbs : b ≫ s = c ≫ z`. Use `ext_of_isDominant (spMap (algebraMap O (FractionRing O))) ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, hb, hls]`. Take `⟨i, hi⟩` from `hcov (b (IsLocalRing.closedPoint O))`. Establish `hr : Set.range b ⊆ Set.range (A i).ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi`. Take `⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b` from `⟨_, IsOpenImmersion.lift_fac _ _ hr⟩`. Establish `e : b' ≫ j i = c ≫ ψ.imageι ≫ p i`. Use `ext_of_isDominant_of_isSeparated (t i) ?_ (spMap (algebraMap O (FractionRing O))) ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt]`.

Rewrite using `[← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]`. Use `⟨i, b' (IsLocalRing.closedPoint O), ?_⟩` and prove the remaining obligations. Establish `e' : (b' ≫ j i) (IsLocalRing.closedPoint O) = (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint O)` using `by rw [e]`.

Conclude with `e'.trans (congrArg (ψ.imageι ≫ p i) hcx)`. Establish `hV : TopologicalSpace.IsOpenCover V`. Rewrite using `[TopologicalSpace.IsOpenCover, eq_top_iff]`. Introduce `x _`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 (key x)`.

Establish `hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i` using `fun i ↦ ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩`. Use `choose m hm using hm`. Take `⟨g, hg, hgU⟩` from `exists_extension_of_cover z s ψ.toImage U.ι V hV (fun i ↦ m i ≫ (A i).ι) (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt]) (fun i T a b e ↦ by`. Rewrite using `[← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]`. Use `congr 1`.

Rewrite using `[← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp, Category.assoc])`. Establish `: IsProper (g ≫ s)` using `by rw [hg]; infer_instance`. Establish `: IsProper g` using `IsProper.of_comp g s`. Establish `: IsDominant g` using `⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩`. Establish `: Surjective g` using `surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range`.

Establish `: UniversallyClosed s` using `.of_comp_surjective g s`. Conclude with `{}`.
-/
theorem isProper_of_lift_genericPoint : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f], (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Sp R), Set.range x ⊆ {genericPoint X} → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro k _ _ Y _ s _ _ _ H
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → Y.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : Y, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    exists_isOpenImmersion_isProper ((A i).ι ≫ s))
  choose P t j ht hj hjt using hP
  let U : Y.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint Y ∈ U := by
    have : ∀ i, genericPoint Y ∈ A i := fun i ↦
      ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨Q, q, ψ, _, hψ, hp⟩ := exists_isProper_factor P t ht (U.ι ≫ s)
    (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc])
    Finset.univ
  choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)
  obtain ⟨i₀, -⟩ := hcov (genericPoint Y)
  have : IsImmersion (ψ ≫ p i₀) := by rw [hψp]; infer_instance
  have : IsImmersion ψ := IsImmersion.of_comp ψ (p i₀)
  have : QuasiCompact (ψ ≫ q) := by rw [hψ]; infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ q
  have : IsIntegral ψ.image := isIntegral_image ψ
  let z : ψ.image ⟶ Sp k := ψ.imageι ≫ q
  have hz : ψ.toImage ≫ z = U.ι ≫ s := by rw [ψ.toImage_imageι_assoc, hψ]
  have : IsLocallyNoetherian ψ.image := LocallyOfFiniteType.isLocallyNoetherian z
  let V : T → ψ.image.Opens := fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange
  let η : U.toScheme := ⟨_, hU⟩
  have hη : ∀ u : U.toScheme, η ⤳ u := fun u ↦
    (U.ι.isEmbedding.isInducing.specializes_iff).1 (genericPoint_specializes (U.ι u))
  have hs : ∀ x : ψ.image, ψ.toImage η ⤳ x := by
    intro x
    rw [specializes_iff_mem_closure]
    refine closure_minimal ?_ isClosed_closure (ψ.toImage.denseRange x)
    rintro _ ⟨u, rfl⟩
    exact specializes_iff_mem_closure.1 ((hη u).map ψ.toImage.continuous)
  have key : ∀ x : ψ.image, ∃ i, x ∈ V i := by
    intro x
    by_cases hne : ψ.toImage η = x
    · refine ⟨i₀, Y.homOfLE (hUA i₀) η, ?_⟩
      rw [← hne, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ψ.toImage_imageι_assoc, hψp]
    obtain ⟨O, _, _, _, c, hc₀, hcx⟩ :=
      exists_complete_discreteValuationRing_of_specializes (hs x) hne
    have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
    have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hpt' : (spMap (algebraMap O (FractionRing O)) ≫ c)
        (IsLocalRing.closedPoint (FractionRing O)) = ψ.toImage η := by
      refine Eq.trans (congrArg c (PrimeSpectrum.ext ?_)) hc₀
      change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨l, hl, hlη⟩ := ValuativeGeneric.exists_lift_of_surjectiveOnStalks ψ.toImage
      (FractionRing O) _ η hpt'
    have hls : (l ≫ U.ι) ≫ s = spMap (algebraMap O (FractionRing O)) ≫ c ≫ z := by
      rw [Category.assoc, ← hz, reassoc_of% hl]
    obtain ⟨b, hb⟩ := H O (FractionRing O) (l ≫ U.ι) (c ≫ z) (by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Hom.comp_apply, hlη]
      rfl) hls
    have hbs : b ≫ s = c ≫ z := by
      refine ext_of_isDominant (spMap (algebraMap O (FractionRing O))) ?_
      rw [← Category.assoc, hb, hls]
    obtain ⟨i, hi⟩ := hcov (b (IsLocalRing.closedPoint O))
    have hr : Set.range b ⊆ Set.range (A i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨v, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi
    obtain ⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : b' ≫ j i = c ≫ ψ.imageι ≫ p i := by
      refine ext_of_isDominant_of_isSeparated (t i) ?_
        (spMap (algebraMap O (FractionRing O))) ?_
      · rw [Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt]
      · rw [← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]
    refine ⟨i, b' (IsLocalRing.closedPoint O), ?_⟩
    have e' : (b' ≫ j i) (IsLocalRing.closedPoint O) =
        (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint O) := by rw [e]
    exact e'.trans (congrArg (ψ.imageι ≫ p i) hcx)
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 (key x)
  have hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i := fun i ↦
    ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩
  choose m hm using hm
  obtain ⟨g, hg, hgU⟩ := exists_extension_of_cover z s ψ.toImage U.ι V hV
    (fun i ↦ m i ≫ (A i).ι)
    (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt])
    (fun i T a b e ↦ by
      rw [← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp,
        Category.assoc])
  have : IsProper (g ≫ s) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g s
  have : IsDominant g := ⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩
  have : Surjective g := surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have : UniversallyClosed s := .of_comp_surjective g s
  exact {}

end GlobalTheory.TraitProper
