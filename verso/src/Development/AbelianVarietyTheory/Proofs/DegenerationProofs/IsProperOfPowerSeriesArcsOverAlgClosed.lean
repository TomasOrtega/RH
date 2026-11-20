import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingEquivPowerSeriesOfComplete
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ArcProper

/- English proof (translation)
Take `⟨N, i, _, _, e⟩` from `(isAmpleLB_of_isAffine (LB.isLB_triv U)).isQProjOver s`. Use `isProper_str R N` as an intermediate fact. Conclude with `⟨i.image, i.imageι ≫ PSpace.str R N, i.toImage, inferInstance, inferInstance, by rw [i.toImage_imageι_assoc, e]⟩`.
-/
theorem exists_isOpenImmersion_isProper {R : Type} [CommRing R] {U : Scheme.{0}} [IsAffine U]
    (s : U ⟶ Sp R) [LocallyOfFiniteType s] :
    ∃ (P : Scheme.{0}) (t : P ⟶ Sp R) (j : U ⟶ P), IsProper t ∧ IsOpenImmersion j ∧ j ≫ t = s := by
  obtain ⟨N, i, _, _, e⟩ := (isAmpleLB_of_isAffine (LB.isLB_triv U)).isQProjOver s
  have := isProper_str R N
  exact ⟨i.image, i.imageι ≫ PSpace.str R N, i.toImage, inferInstance, inferInstance,
    by rw [i.toImage_imageι_assoc, e]⟩

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨S, 𝟙 S, u, inferInstance, Category.comp_id _, by simp⟩`. Consider the case `insert a T _ ih`. Take `⟨Q, q, ψ, _, e, H⟩` from `ih`. Use `⟨pullback q (t a), pullback.fst _ _ ≫ q, pullback.lift ψ (φ a) (e.trans (h a).symm), inferInstance, by rw [pullback.lift_fst_assoc, e], fun i hi ↦ ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Conclude with `⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩`. Take `⟨p, hp, hp'⟩` from `H i hi`. Conclude with `⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp], by rw [pullback.lift_fst_assoc, hp']⟩`.
-/
theorem exists_isProper_factor {S U : Scheme.{0}} {J : Type} (P : J → Scheme.{0})
    (t : ∀ i, P i ⟶ S) (ht : ∀ i, IsProper (t i)) (u : U ⟶ S) (φ : ∀ i, U ⟶ P i)
    (h : ∀ i, φ i ≫ t i = u) (T : Finset J) :
    ∃ (Q : Scheme.{0}) (q : Q ⟶ S) (ψ : U ⟶ Q), IsProper q ∧ ψ ≫ q = u ∧
      ∀ i ∈ T, ∃ p : Q ⟶ P i, p ≫ t i = q ∧ ψ ≫ p = φ i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨S, 𝟙 S, u, inferInstance, Category.comp_id _, by simp⟩
  | insert a T _ ih =>
    obtain ⟨Q, q, ψ, _, e, H⟩ := ih
    refine ⟨pullback q (t a), pullback.fst _ _ ≫ q, pullback.lift ψ (φ a) (e.trans (h a).symm),
      inferInstance, by rw [pullback.lift_fst_assoc, e], fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩
    · obtain ⟨p, hp, hp'⟩ := H i hi
      exact ⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp], by rw [pullback.lift_fst_assoc, hp']⟩

/- English proof (translation)
Set `𝒰` to `Z.openCoverOfIsOpenCover V hV`. Establish `hd : Dense (Set.range j)` using `j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)`. Establish `hc : ∀ i i', pullback.fst (V i).ι (V i').ι ≫ m i = pullback.snd (V i).ι (V i').ι ≫ m i'`. Introduce `i i'`. Set `r` to `pullback.fst (V i).ι (V i').ι ≫ (V i).ι`.

Establish `: IsReduced (pullback (V i).ι (V i').ι)` using `isReduced_of_isOpenImmersion r`. Establish `: IsDominant (pullback.fst r j)` using `⟨by`. Rewrite using `[DenseRange, Scheme.Pullback.range_fst]`. Conclude with `hd.preimage r.isOpenEmbedding.isOpenMap⟩`. Use `ext_of_isDominant_of_isSeparated s ?_ (pullback.fst r j) ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]`. Rewrite using `[← Category.assoc, ← Category.assoc, hu i _ (pullback.snd r j), hu i' _ (pullback.snd r j)]`. Rewrite using `[Category.assoc, ← pullback.condition, ← pullback.condition]`. Rewrite using `[Category.assoc, ← pullback.condition]`. Establish `hg : ∀ i, (V i).ι ≫ 𝒰.glueMorphisms m hc = m i` using `fun i ↦ 𝒰.ι_glueMorphisms m hc i`.

Use `⟨𝒰.glueMorphisms m hc, 𝒰.hom_ext _ _ fun i ↦ ?_, ?_⟩` and prove the remaining obligations. Conclude with `((reassoc_of% hg i) s).trans (hm i)`. Introduce and unpack `_ ⟨w, rfl⟩`. Take `⟨i, hi⟩` from `hV.exists_mem (j w)`. Establish `: w ∈ Set.range (pullback.fst j (V i).ι)`.

Rewrite using `[Scheme.Pullback.range_fst, Scheme.Opens.range_ι]`. Conclude with `hi`. Take `⟨v, rfl⟩` from `this`. Use `⟨(pullback.snd j (V i).ι ≫ (V i).ι) v, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hg, hu i _ _ _ pullback.condition]`.
-/
theorem exists_extension_of_cover {S Z X W : Scheme.{0}} [IsIntegral Z] [Nonempty W] (z : Z ⟶ S)
    (s : X ⟶ S) [IsSeparated s] (j : W ⟶ Z) [IsOpenImmersion j] (u : W ⟶ X) {J : Type}
    (V : J → Z.Opens) (hV : TopologicalSpace.IsOpenCover V) (m : ∀ i, (V i).toScheme ⟶ X)
    (hm : ∀ i, m i ≫ s = (V i).ι ≫ z)
    (hu : ∀ (i : J) (T : Scheme.{0}) (a : T ⟶ W) (b : T ⟶ V i), a ≫ j = b ≫ (V i).ι →
      b ≫ m i = a ≫ u) :
    ∃ g : Z ⟶ X, g ≫ s = z ∧ Set.range u ⊆ Set.range g := by
  let 𝒰 := Z.openCoverOfIsOpenCover V hV
  have hd : Dense (Set.range j) := j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  have hc : ∀ i i', pullback.fst (V i).ι (V i').ι ≫ m i = pullback.snd (V i).ι (V i').ι ≫ m i' := by
    intro i i'
    let r := pullback.fst (V i).ι (V i').ι ≫ (V i).ι
    have : IsReduced (pullback (V i).ι (V i').ι) := isReduced_of_isOpenImmersion r
    have : IsDominant (pullback.fst r j) := ⟨by
      rw [DenseRange, Scheme.Pullback.range_fst]
      exact hd.preimage r.isOpenEmbedding.isOpenMap⟩
    refine ext_of_isDominant_of_isSeparated s ?_ (pullback.fst r j) ?_
    · rw [Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc, hu i _ (pullback.snd r j), hu i' _ (pullback.snd r j)]
      · rw [Category.assoc, ← pullback.condition, ← pullback.condition]
      · rw [Category.assoc, ← pullback.condition]
  have hg : ∀ i, (V i).ι ≫ 𝒰.glueMorphisms m hc = m i := fun i ↦ 𝒰.ι_glueMorphisms m hc i
  refine ⟨𝒰.glueMorphisms m hc, 𝒰.hom_ext _ _ fun i ↦ ?_, ?_⟩
  · exact ((reassoc_of% hg i) s).trans (hm i)
  · rintro _ ⟨w, rfl⟩
    obtain ⟨i, hi⟩ := hV.exists_mem (j w)
    have : w ∈ Set.range (pullback.fst j (V i).ι) := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]; exact hi
    obtain ⟨v, rfl⟩ := this
    refine ⟨(pullback.snd j (V i).ι ≫ (V i).ι) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hg,
      hu i _ _ _ pullback.condition]

/- English proof (translation)
Take `⟨B, g, _, y, rfl⟩` from `Z.exists_Spec_apply_eq z`. Establish `: Nonempty (Spec B)` using `⟨y⟩`. Establish `: IsIntegral (Spec B)` using `isIntegral_of_isOpenImmersion g`. Establish `: IsDomain B` using `(affine_isIntegral_iff B).mp this`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (g ≫ s)`.

Establish `hft : ψ.hom.FiniteType`. Establish `: LocallyOfFiniteType (Spec.map ψ)` using `by rw [hψ]; infer_instance`. Conclude with `HasRingHomProperty.Spec_iff.1 this`. Set `_ : Algebra k B` to `ψ.hom.toAlgebra`. Establish `: Algebra.FiniteType k B` using `hft`.

Establish `hy : y.asIdeal.IsMaximal`. Use `(PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 ?_` and prove the remaining obligations. Use `hz.preimage g.continuous` as an intermediate fact. Rewrite `this` using `[← Set.image_singleton, Set.preimage_image_eq _ g.isOpenEmbedding.injective]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : (g ⁻¹' W).Nonempty := by`.

Take `⟨_, hw, w, rfl⟩` from `(g.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)).inter_open_nonempty W hW hW'`. Conclude with `⟨w, hw⟩`. Take `⟨_, ⟨f, rfl⟩, hwf, hf⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hw (hW.preimage g.continuous)`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hwf w.asIdeal.zero_mem`. Take `⟨φ, hφ, hφm⟩` from `GlobalTheory.ArcAvoid.exists_algHom_powerSeries_ne_zero k B y.asIdeal hy f hf0`. Use `⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hψ, ← Spec.map_comp]`. Use `congr 1`.

Use `ext1`. Conclude with `φ.comp_algebraMap`. Use `congrArg g (PrimeSpectrum.ext (Ideal.ext fun b ↦ ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ b ∈ IsLocalRing.maximalIdeal (PowerSeries k) ↔ _`. Rewrite using `[hφm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]`.

Introduce and unpack `_ ⟨p, rfl⟩`. Use `hf ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (φ f) ∉ p.asIdeal`. Introduce `h`. Use `p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsUnit.mk0 _ ?_))` and prove the remaining obligations.

Simplify using `using hφ`.
-/
theorem exists_arc (k : Type) [Field k] [IsAlgClosed k] {Z : Scheme.{0}} [IsIntegral Z]
    (s : Z ⟶ Sp k) [LocallyOfFiniteType s] (z : Z) (hz : IsClosed ({z} : Set Z)) (W : Set Z)
    (hW : IsOpen W) (hW' : W.Nonempty) :
    ∃ c : Sp (PowerSeries k) ⟶ Z, c ≫ s = spMap (algebraMap k (PowerSeries k)) ∧
      c (IsLocalRing.closedPoint (PowerSeries k)) = z ∧
      Set.range (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ c) ⊆ W := by
  obtain ⟨B, g, _, y, rfl⟩ := Z.exists_Spec_apply_eq z
  have : Nonempty (Spec B) := ⟨y⟩
  have : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion g
  have : IsDomain B := (affine_isIntegral_iff B).mp this
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (g ≫ s)
  have hft : ψ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra k B := ψ.hom.toAlgebra
  have : Algebra.FiniteType k B := hft
  have hy : y.asIdeal.IsMaximal := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 ?_
    have := hz.preimage g.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ g.isOpenEmbedding.injective] at this
  obtain ⟨w, hw⟩ : (g ⁻¹' W).Nonempty := by
    obtain ⟨_, hw, w, rfl⟩ := (g.isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)).inter_open_nonempty W hW hW'
    exact ⟨w, hw⟩
  obtain ⟨_, ⟨f, rfl⟩, hwf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hw
      (hW.preimage g.continuous)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hwf w.asIdeal.zero_mem
  obtain ⟨φ, hφ, hφm⟩ := GlobalTheory.ArcAvoid.exists_algHom_powerSeries_ne_zero k B y.asIdeal hy f hf0
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    congr 1
    ext1
    exact φ.comp_algebraMap
  · refine congrArg g (PrimeSpectrum.ext (Ideal.ext fun b ↦ ?_))
    change φ b ∈ IsLocalRing.maximalIdeal (PowerSeries k) ↔ _
    rw [hφm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not]
  · rintro _ ⟨p, rfl⟩
    refine hf ?_
    change algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (φ f) ∉ p.asIdeal
    intro h
    refine p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsUnit.mk0 _ ?_))
    simpa using hφ

/- English proof (translation)
Establish `: CompactSpace Y` using `QuasiCompact.compactSpace_of_compactSpace s`. Establish `: IsLocallyNoetherian Y` using `LocallyOfFiniteType.isLocallyNoetherian s`. Establish `hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A` using `fun y ↦ by`. Take `⟨A, h₁, h₂, -⟩` from `exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial`. Conclude with `⟨A, h₁, h₂⟩`.

Use `choose A₀ hA₀ hyA using hA`. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y)) (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)`. Set `A : T → Y.Opens` to `fun i ↦ A₀ i`. Establish `hcov : ∀ y : Y, ∃ i : T, y ∈ A i` using `fun y ↦ by`. Take `⟨i, hi, h⟩` from `Set.mem_iUnion₂.1 (hT (Set.mem_univ y))`.

Conclude with `⟨⟨i, hi⟩, h⟩`. Establish `hP` using `fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i exists_isOpenImmersion_isProper ((A i).ι ≫ s))`. Use `choose P t j ht hj hjt using hP`. Set `U : Y.Opens` to `Finset.univ.inf A`. Establish `hUA : ∀ i, U ≤ A i` using `fun i ↦ Finset.inf_le (Finset.mem_univ i)`.

Establish `hU : genericPoint Y ∈ U`. Establish `: ∀ i, genericPoint Y ∈ A i` using `fun i ↦ ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩`. Use `Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i` and prove the remaining obligations. Establish `: Nonempty U.toScheme` using `⟨⟨_, hU⟩⟩`. Establish `: IsIntegral U.toScheme` using `isIntegral_of_isOpenImmersion U.ι`.

Take `⟨Q, q, ψ, _, hψ, hp⟩` from `exists_isProper_factor P t ht (U.ι ≫ s) (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc]) Finset.univ`. Use `choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)`. Take `⟨i₀, -⟩` from `hcov (genericPoint Y)`. Establish `: IsImmersion (ψ ≫ p i₀)` using `by rw [hψp]; infer_instance`. Establish `: IsImmersion ψ` using `IsImmersion.of_comp ψ (p i₀)`.

Establish `: QuasiCompact (ψ ≫ q)` using `by rw [hψ]; infer_instance`. Establish `: QuasiCompact ψ` using `QuasiCompact.of_comp ψ q`. Establish `: IsIntegral ψ.image` using `isIntegral_image ψ`. Set `z : ψ.image ⟶ Sp k` to `ψ.imageι ≫ q`. Establish `hz : ψ.toImage ≫ z = U.ι ≫ s` using `by rw [ψ.toImage_imageι_assoc, hψ]`.

Set `V : T → ψ.image.Opens` to `fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange`. Establish `hinj : Function.Injective (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))` using `IsFractionRing.injective _ _`. Establish `: IsDominant (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))))`. Use `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩` and prove the remaining obligations. Conclude with `((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le`.

Establish `key : ∀ x : ψ.image, IsClosed ({x} : Set ψ.image) → ∃ i, x ∈ V i`. Introduce `x hx`. Take `⟨c, hc, hcx, hcU⟩` from `exists_arc k z x hx _ ψ.toImage.isOpenEmbedding.isOpen_range (Set.range_nonempty _)`. Take `⟨l, hl⟩ : ∃ l, l ≫ ψ.toImage = _` from `⟨_, IsOpenImmersion.lift_fac ψ.toImage _ hcU⟩`. Establish `hls : (l ≫ U.ι) ≫ s = spMap (algebraMap k (FractionRing (PowerSeries k)))`.

Rewrite using `[Category.assoc, ← hz, reassoc_of% hl, hc, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨b, hb⟩` from `H (l ≫ U.ι) hls`. Establish `hbs : b ≫ s = spMap (algebraMap k (PowerSeries k))`. Use `ext_of_isDominant (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, hb, hls, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨i, hi⟩` from `hcov (b (IsLocalRing.closedPoint (PowerSeries k)))`. Establish `hr : Set.range b ⊆ Set.range (A i).ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi`. Take `⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b` from `⟨_, IsOpenImmersion.lift_fac _ _ hr⟩`. Establish `e : b' ≫ j i = c ≫ ψ.imageι ≫ p i`. Use `ext_of_isDominant_of_isSeparated (t i) ?_ (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt, hc]`. Rewrite using `[← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]`. Use `⟨i, b' (IsLocalRing.closedPoint (PowerSeries k)), ?_⟩` and prove the remaining obligations.

Establish `e' : (b' ≫ j i) (IsLocalRing.closedPoint (PowerSeries k)) = (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint (PowerSeries k))` using `by rw [e]`. Conclude with `e'.trans (congrArg (ψ.imageι ≫ p i) hcx)`. Establish `: CompactSpace ψ.image` using `QuasiCompact.compactSpace_of_compactSpace z`. Establish `hV : TopologicalSpace.IsOpenCover V`. Rewrite using `[TopologicalSpace.IsOpenCover, eq_top_iff]`.

Introduce `x _`. Take `⟨x', hx', hc⟩` from `(isClosed_closure (s := {x})).exists_closed_singleton (Set.singleton_nonempty x).closure`. Take `⟨i, hi⟩` from `key x' hc`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, (specializes_iff_mem_closure.2 hx').mem_open (V i).isOpen hi⟩`. Establish `hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i` using `fun i ↦ ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩`.

Use `choose m hm using hm`. Take `⟨g, hg, hgU⟩` from `exists_extension_of_cover z s ψ.toImage U.ι V hV (fun i ↦ m i ≫ (A i).ι) (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt]) (fun i T a b e ↦ by`. Rewrite using `[← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp, Category.assoc])`.

Establish `: IsProper (g ≫ s)` using `by rw [hg]; infer_instance`. Establish `: IsProper g` using `IsProper.of_comp g s`. Establish `: IsDominant g` using `⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩`. Establish `: Surjective g` using `surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range`. Establish `: UniversallyClosed s` using `.of_comp_surjective g s`.

Conclude with `{}`.
-/
theorem isProper_of_arcs_extend (k : Type) [Field k] [IsAlgClosed k] {Y : Scheme.{0}} [IsIntegral Y]
    (s : Y ⟶ Sp k) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (H : ∀ a : Sp (FractionRing (PowerSeries k)) ⟶ Y,
      a ≫ s = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ Y,
        spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) :
    IsProper s := by
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
  let V : T → ψ.image.Opens := fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange
  have hinj : Function.Injective
      (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) := IsFractionRing.injective _ _
  have : IsDominant (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) := by
    refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  have key : ∀ x : ψ.image, IsClosed ({x} : Set ψ.image) → ∃ i, x ∈ V i := by
    intro x hx
    obtain ⟨c, hc, hcx, hcU⟩ := exists_arc k z x hx _ ψ.toImage.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    obtain ⟨l, hl⟩ : ∃ l, l ≫ ψ.toImage = _ := ⟨_, IsOpenImmersion.lift_fac ψ.toImage _ hcU⟩
    have hls : (l ≫ U.ι) ≫ s = spMap (algebraMap k (FractionRing (PowerSeries k))) := by
      rw [Category.assoc, ← hz, reassoc_of% hl, hc, ← Spec.map_comp]
      rfl
    obtain ⟨b, hb⟩ := H (l ≫ U.ι) hls
    have hbs : b ≫ s = spMap (algebraMap k (PowerSeries k)) := by
      refine ext_of_isDominant (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) ?_
      rw [← Category.assoc, hb, hls, ← Spec.map_comp]
      rfl
    obtain ⟨i, hi⟩ := hcov (b (IsLocalRing.closedPoint (PowerSeries k)))
    have hr : Set.range b ⊆ Set.range (A i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨v, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi
    obtain ⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : b' ≫ j i = c ≫ ψ.imageι ≫ p i := by
      refine ext_of_isDominant_of_isSeparated (t i) ?_
        (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) ?_
      · rw [Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt, hc]
      · rw [← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]
    refine ⟨i, b' (IsLocalRing.closedPoint (PowerSeries k)), ?_⟩
    have e' : (b' ≫ j i) (IsLocalRing.closedPoint (PowerSeries k)) =
        (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint (PowerSeries k)) := by rw [e]
    exact e'.trans (congrArg (ψ.imageι ≫ p i) hcx)
  have : CompactSpace ψ.image := QuasiCompact.compactSpace_of_compactSpace z
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨x', hx', hc⟩ := (isClosed_closure (s := {x})).exists_closed_singleton
      (Set.singleton_nonempty x).closure
    obtain ⟨i, hi⟩ := key x' hc
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨i, (specializes_iff_mem_closure.2 hx').mem_open (V i).isOpen hi⟩
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

/- English proof (translation)
The claim follows from `fun k _ _ X _ _ _ _ H ↦ isProper_of_arcs_extend k X.hom H`.
-/
theorem isProper_of_arcs : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left], IsSeparated X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom → (∀ a : Sp (FractionRing (PowerSeries k)) ⟶ X.left, a ≫ X.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ X.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → IsProper X.hom :=
  fun k _ _ X _ _ _ _ H ↦ isProper_of_arcs_extend k X.hom H

end GlobalTheory.ArcProper
