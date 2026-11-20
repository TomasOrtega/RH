import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDomainOfIsIntegrallyClosedOfIsReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.ExtendNormal

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[DenseRange, Scheme.Pullback.range_fst]`. Conclude with `i.denseRange.preimage p.isOpenEmbedding.isOpenMap`.
-/
theorem isDominant_fst {P Y₀ Y : Scheme.{0}} (p : P ⟶ Y) (i : Y₀ ⟶ Y) [IsOpenImmersion p] [IsDominant i] :
    IsDominant (pullback.fst p i) := by
  refine ⟨?_⟩
  rw [DenseRange, Scheme.Pullback.range_fst]
  exact i.denseRange.preimage p.isOpenEmbedding.isOpenMap

/- English proof (translation)
Use `choose U hy t ht using h`. Establish `hU : TopologicalSpace.IsOpenCover U`. Rewrite using `[TopologicalSpace.IsOpenCover, eq_top_iff]`. Introduce `y _`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩`.

Set `𝒰` to `Y.openCoverOfIsOpenCover U hU`. Establish `hc : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ t x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ t y`. Introduce `x y`. Express the relevant statement in the definitionally equal form `pullback.fst (U x).ι (U y).ι ≫ t x = pullback.snd (U x).ι (U y).ι ≫ t y`. Set `p` to `pullback.fst (U x).ι (U y).ι ≫ (U x).ι`.

Establish `: IsReduced (pullback (U x).ι (U y).ι)` using `isReduced_of_isOpenImmersion p`. Use `isDominant_fst p i` as an intermediate fact. Use `ext_of_isDominant (pullback.fst p i) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc, ht x _ _ (pullback.snd p i), ht y _ _ (pullback.snd p i)]`. Rewrite using `[Category.assoc, ← pullback.condition]`.

Conclude with `pullback.condition`. Rewrite using `[Category.assoc]`. Conclude with `pullback.condition`. Use `⟨𝒰.glueMorphisms t hc, ?_⟩` and prove the remaining obligations. Use `Scheme.Cover.hom_ext (𝒰.pullback₁ i) _ _ fun y => ?_` and prove the remaining obligations.

Establish `e` using `𝒰.ι_glueMorphisms t hc y`. Express the relevant statement in the definitionally equal form `pullback.fst i (𝒰.f y) ≫ _ = pullback.fst i (𝒰.f y) ≫ _`. Rewrite using `[pullback.condition_assoc, e]`. Conclude with `ht y _ _ _ pullback.condition.symm`.
-/
theorem glue {Y₀ Y X : Scheme.{0}} (i : Y₀ ⟶ Y) (t₀ : Y₀ ⟶ X) [IsDominant i] [IsReduced Y] [X.IsSeparated]
    (h : ∀ y : Y, ∃ (U : Y.Opens) (_ : y ∈ U) (t : U.toScheme ⟶ X),
      ∀ (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ Y₀), a ≫ U.ι = b ≫ i → a ≫ t = b ≫ t₀) :
    ∃ t : Y ⟶ X, i ≫ t = t₀ := by
  choose U hy t ht using h
  have hU : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
  let 𝒰 := Y.openCoverOfIsOpenCover U hU
  have hc : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ t x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ t y := by
    intro x y
    change pullback.fst (U x).ι (U y).ι ≫ t x = pullback.snd (U x).ι (U y).ι ≫ t y
    let p := pullback.fst (U x).ι (U y).ι ≫ (U x).ι
    have : IsReduced (pullback (U x).ι (U y).ι) := isReduced_of_isOpenImmersion p
    have := isDominant_fst p i
    refine ext_of_isDominant (pullback.fst p i) ?_
    rw [← Category.assoc, ← Category.assoc, ht x _ _ (pullback.snd p i), ht y _ _ (pullback.snd p i)]
    · rw [Category.assoc, ← pullback.condition]
      exact pullback.condition
    · rw [Category.assoc]
      exact pullback.condition
  refine ⟨𝒰.glueMorphisms t hc, ?_⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ i) _ _ fun y => ?_
  have e := 𝒰.ι_glueMorphisms t hc y
  change pullback.fst i (𝒰.f y) ≫ _ = pullback.fst i (𝒰.f y) ≫ _
  rw [pullback.condition_assoc, e]
  exact ht y _ _ _ pullback.condition.symm

/- English proof (translation)
Establish `hr : Set.range z ⊆ Set.range hW.fromSpec`. Rewrite using `[hW.range_fromSpec]`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `hz p`. Conclude with `⟨Spec.preimage (IsOpenImmersion.lift hW.fromSpec z hr), by`.

Rewrite using `[Spec.map_preimage, IsOpenImmersion.lift_fac]⟩`.
-/
theorem exists_eq_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (A : CommRingCat.{0})
    (z : Spec A ⟶ X) (hz : ∀ p, z p ∈ W) : ∃ ψ : Γ(X, W) ⟶ A, Spec.map ψ ≫ hW.fromSpec = z := by
  have hr : Set.range z ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact hz p
  exact ⟨Spec.preimage (IsOpenImmersion.lift hW.fromSpec z hr), by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

/- English proof (translation)
Establish `h' : ∀ (V : ValuationSubring K), IsDiscreteValuationRing V → LocalSubring.range (algebraMap O K) ≤ V.toLocalSubring → ∃ ψ : Γ(X, W) ⟶ CommRingCat.of V, Spec.map (ψ ≫ CommRingCat.ofHom (algebraMap V K)) ≫ hW.fromSpec = x`. Introduce `V hV hle`. Take `⟨h1, h2⟩` from `(localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp hle`. Take `⟨z, hz, hzW⟩` from `h V h1 h2`. Take `⟨ψ, rfl⟩` from `exists_eq_fromSpec hW _ z fun p => ((IsLocalRing.specializes_closedPoint p).map z.continuous).mem_open W.isOpen hzW`.

Conclude with `⟨ψ, by rw [Spec.map_comp, Category.assoc, ← hz]⟩`. Distinguish the cases in `hO : IsField O`. Establish `hb : Function.Bijective (algebraMap O K)` using `⟨IsFractionRing.injective O K, IsFractionRing.surjective_iff_isField.mpr hO⟩`. Establish `: IsIso (CommRingCat.ofHom (algebraMap O K))` using `(ConcreteCategory.isIso_iff_bijective _).mpr hb`. Conclude with `⟨inv (spMap (algebraMap O K)) ≫ x, IsIso.hom_inv_id_assoc _ _⟩`.

Take `⟨V₀, hV₀, hle₀⟩` from `exists_discreteValuationSubring_dominating O K K hO`. Take `⟨ψ₀, hψ₀⟩` from `h' V₀ hV₀ hle₀`. Use `set φ := ψ₀ ≫ CommRingCat.ofHom (algebraMap V₀ K) with hφ`. Establish `hmem : ∀ b, φ.hom b ∈ (algebraMap O K).range`. Introduce `b`.

Rewrite using `[range_algebraMap_eq_iInf_discreteValuationSubring, Subring.mem_iInf]`. Introduce and unpack `⟨V, h1, h2⟩`. Take `⟨ψ, hψ⟩` from `h' V h1 h2`. Rewrite `hψ` using `[← hψ₀, cancel_mono]`. Rewrite using `[← Spec.map_injective hψ]`.

Conclude with `(ψ.hom b).2`. Set `e : O ≃+* (algebraMap O K).range` to `RingEquiv.ofBijective (algebraMap O K).rangeRestrict ⟨fun a b hab => IsFractionRing.injective O K (congrArg Subtype.val hab), (algebraMap O K).rangeRestrict_surjective⟩`. Set `φ' : Γ(X, W) →+* O` to `e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)`. Use `⟨Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[← hψ₀, ← Spec.map_comp_assoc]`.

Use `congr 2`. Use extensionality with `b`. Conclude with `congrArg Subtype.val (e.apply_symm_apply ⟨φ.hom b, hmem b⟩)`.
-/
theorem exists_extension_local {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (O K : Type) [CommRing O]
    [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K]
    [IsFractionRing O K] (x : Sp K ⟶ X)
    (h : ∀ (V : ValuationSubring K) [IsDiscreteValuationRing V] (hV : ∀ r, algebraMap O K r ∈ V),
      IsLocalHom ((algebraMap O K).codRestrict V hV) →
      ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ∧ z (IsLocalRing.closedPoint V) ∈ W) :
    ∃ g : Sp O ⟶ X, spMap (algebraMap O K) ≫ g = x := by
  have h' : ∀ (V : ValuationSubring K), IsDiscreteValuationRing V →
      LocalSubring.range (algebraMap O K) ≤ V.toLocalSubring →
      ∃ ψ : Γ(X, W) ⟶ CommRingCat.of V, Spec.map (ψ ≫ CommRingCat.ofHom (algebraMap V K)) ≫ hW.fromSpec = x := by
    intro V hV hle
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp hle
    obtain ⟨z, hz, hzW⟩ := h V h1 h2
    obtain ⟨ψ, rfl⟩ := exists_eq_fromSpec hW _ z fun p =>
      ((IsLocalRing.specializes_closedPoint p).map z.continuous).mem_open W.isOpen hzW
    exact ⟨ψ, by rw [Spec.map_comp, Category.assoc, ← hz]⟩
  by_cases hO : IsField O
  · have hb : Function.Bijective (algebraMap O K) :=
      ⟨IsFractionRing.injective O K, IsFractionRing.surjective_iff_isField.mpr hO⟩
    have : IsIso (CommRingCat.ofHom (algebraMap O K)) := (ConcreteCategory.isIso_iff_bijective _).mpr hb
    exact ⟨inv (spMap (algebraMap O K)) ≫ x, IsIso.hom_inv_id_assoc _ _⟩
  obtain ⟨V₀, hV₀, hle₀⟩ := exists_discreteValuationSubring_dominating O K K hO
  obtain ⟨ψ₀, hψ₀⟩ := h' V₀ hV₀ hle₀
  set φ := ψ₀ ≫ CommRingCat.ofHom (algebraMap V₀ K) with hφ
  have hmem : ∀ b, φ.hom b ∈ (algebraMap O K).range := by
    intro b
    rw [range_algebraMap_eq_iInf_discreteValuationSubring, Subring.mem_iInf]
    rintro ⟨V, h1, h2⟩
    obtain ⟨ψ, hψ⟩ := h' V h1 h2
    rw [← hψ₀, cancel_mono] at hψ
    rw [← Spec.map_injective hψ]
    exact (ψ.hom b).2
  let e : O ≃+* (algebraMap O K).range :=
    RingEquiv.ofBijective (algebraMap O K).rangeRestrict
      ⟨fun a b hab => IsFractionRing.injective O K (congrArg Subtype.val hab),
        (algebraMap O K).rangeRestrict_surjective⟩
  let φ' : Γ(X, W) →+* O := e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)
  refine ⟨Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec, ?_⟩
  rw [← hψ₀, ← Spec.map_comp_assoc]
  congr 2
  ext b
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ.hom b, hmem b⟩)

/- English proof (translation)
Use `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩` and prove the remaining obligations. Conclude with `((RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O K)).le.trans bot_le`.
-/
theorem isDominant_spMap (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] :
    IsDominant (spMap (algebraMap O K)) := by
  refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
  exact ((RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O K)).le.trans bot_le

/- English proof (translation)
Take `⟨U, hyU, hU, hUV, hinj⟩` from `Y.exists_le_and_germ_injective y V hy`. Establish `: IsDomain Γ(Y, U)` using `hinj.isDomain _`. Use `⟨U, hyU, hUV, fun u hu => ?_⟩` and prove the remaining obligations. Establish `key : ∀ v ∈ U, hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) ⤳ v`. Introduce `v hv`.

Take `⟨q, rfl⟩ : v ∈ Set.range hU.fromSpec` from `by rw [hU.range_fromSpec]; exact hv`. Conclude with `((PrimeSpectrum.le_iff_specializes ⊥ q).mp bot_le).map hU.fromSpec.continuous`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) ∈ Set.range (Y.fromSpecStalk y) := by`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `key y hyU`.

Use `Specializes.trans ?_ (key u hu)` and prove the remaining obligations. Rewrite using `[← hq]`. Conclude with `((PrimeSpectrum.le_iff_specializes ⊥ q).mp bot_le).map (Y.fromSpecStalk y).continuous`.
-/
theorem exists_nhds_specializes {Y : Scheme.{0}} [IsLocallyNoetherian Y] (y : Y) [IsDomain (Y.presheaf.stalk y)]
    (V : Y.Opens) (hy : y ∈ V) :
    ∃ U : Y.Opens, y ∈ U ∧ U ≤ V ∧
      ∀ u ∈ U, Y.fromSpecStalk y (⊥ : PrimeSpectrum (Y.presheaf.stalk y)) ⤳ u := by
  obtain ⟨U, hyU, hU, hUV, hinj⟩ := Y.exists_le_and_germ_injective y V hy
  have : IsDomain Γ(Y, U) := hinj.isDomain _
  refine ⟨U, hyU, hUV, fun u hu => ?_⟩
  have key : ∀ v ∈ U, hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) ⤳ v := by
    intro v hv
    obtain ⟨q, rfl⟩ : v ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hv
    exact ((PrimeSpectrum.le_iff_specializes ⊥ q).mp bot_le).map hU.fromSpec.continuous
  obtain ⟨q, hq⟩ : hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) ∈ Set.range (Y.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]; exact key y hyU
  refine Specializes.trans ?_ (key u hu)
  rw [← hq]
  exact ((PrimeSpectrum.le_iff_specializes ⊥ q).mp bot_le).map (Y.fromSpecStalk y).continuous

/- English proof (translation)
Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap O K) p.asIdeal = ⊥`. Establish `hp : Ideal.IsPrime (α` using `K) p.asIdeal := p.isPrime`. Rewrite using `[Ideal.eq_bot_of_prime (K := K) p.asIdeal]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)`.
-/
theorem spMap_apply_eq_bot (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    (p : Sp K) : spMap (algebraMap O K) p = (⊥ : PrimeSpectrum O) := by
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (algebraMap O K) p.asIdeal = ⊥
  have hp : Ideal.IsPrime (α := K) p.asIdeal := p.isPrime
  rw [Ideal.eq_bot_of_prime (K := K) p.asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)

/- English proof (translation)
Set `O : Type` to `Y.presheaf.stalk y`. Set `K : Type` to `FractionRing O`. Set `j : Sp K ⟶ Spec (Y.presheaf.stalk y)` to `spMap (algebraMap O K)`. Establish `hjd : IsDominant j` using `isDominant_spMap O K`. Set `ξ : Y` to `Y.fromSpecStalk y (⊥ : PrimeSpectrum (Y.presheaf.stalk y))`.

Establish `hgen : ∀ p, (j ≫ Y.fromSpecStalk y) p = ξ` using `fun p => (Scheme.Hom.comp_apply _ _ _).trans (congrArg (Y.fromSpecStalk y) (spMap_apply_eq_bot O K p))`. Establish `hgi : ξ ∈ Set.range i`. Take `⟨U, hyU, -, hU⟩` from `exists_nhds_specializes y ⊤ trivial`. Take `⟨u, hu⟩` from `i.denseRange.exists_mem_open U.isOpen ⟨y, hyU⟩`. Conclude with `(hU _ hu).mem_open i.isOpenEmbedding.isOpen_range ⟨u, rfl⟩`.

Take `⟨x, hx⟩ : ∃ x : Sp K ⟶ Y₀, x ≫ i = j ≫ Y.fromSpecStalk y` from `⟨_, IsOpenImmersion.lift_fac i (j ≫ Y.fromSpecStalk y) (by rintro _ ⟨p, rfl⟩; rw [hgen]; exact hgi)⟩`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : Spec (Y.presheaf.stalk y) ⟶ X, j ≫ g = x ≫ t₀ := by`. Use `exists_extension_local hW O K (x ≫ t₀) fun V _ hV hloc => ?_` and prove the remaining obligations. Set `k : Sp V ⟶ Spec (Y.presheaf.stalk y)` to `spMap ((algebraMap O K).codRestrict V hV)`. Use `h V K (k ≫ Y.fromSpecStalk y) x ?_ ?_` and prove the remaining obligations.

Rewrite using `[hx, ← Category.assoc]`. Use `congr 1`. Conclude with `(Spec.map_comp _ _).symm`. Use `(Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (Y.fromSpecStalk y) ?_) (Scheme.fromSpecStalk_closedPoint (x := y)))` and prove the remaining obligations. Conclude with `IsLocalRing.comap_closedPoint ((algebraMap O K).codRestrict V hV)`.

Establish `hgτ : g ≫ τ = Y.fromSpecStalk y ≫ σ`. Use `ext_of_isDominant j ?_` and prove the remaining obligations. Rewrite using `[reassoc_of% hg, ← reassoc_of% hx, hc]`. Take `⟨U₁, hy₁, t₁, ht₁, -⟩` from `spread_out_of_isGermInjective' σ τ g hgτ`. Take `⟨U, hyU, hle, hU⟩` from `exists_nhds_specializes y U₁ hy₁`.

Use `⟨U, hyU, Y.homOfLE hle ≫ t₁, fun T a b hab => ?_⟩` and prove the remaining obligations. Establish `hw : (j ≫ U.fromSpecStalkOfMem y hyU) ≫ U.ι = x ≫ i` using `by simp [hx]`. Set `w : Sp K ⟶ pullback U.ι i` to `pullback.lift _ _ hw`. Set `p : pullback U.ι i ⟶ Y` to `pullback.fst U.ι i ≫ U.ι`. Establish `hwp : w ≫ p = j ≫ Y.fromSpecStalk y`.

Rewrite using `[← hx, ← hw]`. Conclude with `pullback.lift_fst_assoc _ _ hw _`. Establish `: IsReduced (pullback U.ι i)` using `isReduced_of_isOpenImmersion p`. Establish `: IsDominant w`. Use `⟨fun q => ?_⟩` and prove the remaining obligations.

Establish `h1 : w (IsLocalRing.closedPoint K) ⤳ q`. Establish `h0 : p (w (IsLocalRing.closedPoint K)) = ξ` using `(Scheme.Hom.comp_apply w p _).symm.trans (by rw [hwp]; exact hgen _)`. Rewrite using `[← p.isOpenEmbedding.isInducing.specializes_iff, h0]`. Conclude with `hU _ (pullback.fst U.ι i q).2`. Conclude with `h1.mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)`.

Establish `e : pullback.fst U.ι i ≫ Y.homOfLE hle ≫ t₁ = pullback.snd U.ι i ≫ t₀`. Use `ext_of_isDominant w ?_` and prove the remaining obligations. Establish `h2 : U.fromSpecStalkOfMem y hyU ≫ Y.homOfLE hle = U₁.fromSpecStalkOfMem y hy₁`. Rewrite using `[← cancel_mono U₁.ι]`. Simplify using the standard rewrite rules.

Simplify using `only [w, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc]`. Rewrite using `[reassoc_of% h2, ← ht₁, hg]`. Rewrite using `[← pullback.lift_fst a b hab, Category.assoc, e, pullback.lift_snd_assoc]`.
-/
theorem exists_extension_nhds {R : Type} [CommRing R] {Y₀ Y X : Scheme.{0}} (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R)
    (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X) [IsOpenImmersion i] [IsDominant i] [IsLocallyNoetherian Y] [IsReduced Y]
    [X.IsSeparated] [LocallyOfFiniteType τ] (hc : i ≫ σ = t₀ ≫ τ) (y : Y) [IsDomain (Y.presheaf.stalk y)]
    [IsIntegrallyClosed (Y.presheaf.stalk y)] {W : X.Opens} (hW : IsAffineOpen W)
    (h : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (y' : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i →
      y' (IsLocalRing.closedPoint V) = y →
      ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀ ∧ z (IsLocalRing.closedPoint V) ∈ W) :
    ∃ (U : Y.Opens) (_ : y ∈ U) (t : U.toScheme ⟶ X),
      ∀ (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ Y₀), a ≫ U.ι = b ≫ i → a ≫ t = b ≫ t₀ := by
  let O : Type := Y.presheaf.stalk y
  let K : Type := FractionRing O
  let j : Sp K ⟶ Spec (Y.presheaf.stalk y) := spMap (algebraMap O K)
  have hjd : IsDominant j := isDominant_spMap O K
  let ξ : Y := Y.fromSpecStalk y (⊥ : PrimeSpectrum (Y.presheaf.stalk y))
  have hgen : ∀ p, (j ≫ Y.fromSpecStalk y) p = ξ := fun p =>
    (Scheme.Hom.comp_apply _ _ _).trans (congrArg (Y.fromSpecStalk y) (spMap_apply_eq_bot O K p))
  have hgi : ξ ∈ Set.range i := by
    obtain ⟨U, hyU, -, hU⟩ := exists_nhds_specializes y ⊤ trivial
    obtain ⟨u, hu⟩ := i.denseRange.exists_mem_open U.isOpen ⟨y, hyU⟩
    exact (hU _ hu).mem_open i.isOpenEmbedding.isOpen_range ⟨u, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Sp K ⟶ Y₀, x ≫ i = j ≫ Y.fromSpecStalk y :=
    ⟨_, IsOpenImmersion.lift_fac i (j ≫ Y.fromSpecStalk y) (by rintro _ ⟨p, rfl⟩; rw [hgen]; exact hgi)⟩
  obtain ⟨g, hg⟩ : ∃ g : Spec (Y.presheaf.stalk y) ⟶ X, j ≫ g = x ≫ t₀ := by
    refine exists_extension_local hW O K (x ≫ t₀) fun V _ hV hloc => ?_
    let k : Sp V ⟶ Spec (Y.presheaf.stalk y) := spMap ((algebraMap O K).codRestrict V hV)
    refine h V K (k ≫ Y.fromSpecStalk y) x ?_ ?_
    · rw [hx, ← Category.assoc]
      congr 1
      exact (Spec.map_comp _ _).symm
    · refine (Scheme.Hom.comp_apply _ _ _).trans
        (Eq.trans (congrArg (Y.fromSpecStalk y) ?_) (Scheme.fromSpecStalk_closedPoint (x := y)))
      exact IsLocalRing.comap_closedPoint ((algebraMap O K).codRestrict V hV)
  have hgτ : g ≫ τ = Y.fromSpecStalk y ≫ σ := by
    refine ext_of_isDominant j ?_
    rw [reassoc_of% hg, ← reassoc_of% hx, hc]
  obtain ⟨U₁, hy₁, t₁, ht₁, -⟩ := spread_out_of_isGermInjective' σ τ g hgτ
  obtain ⟨U, hyU, hle, hU⟩ := exists_nhds_specializes y U₁ hy₁
  refine ⟨U, hyU, Y.homOfLE hle ≫ t₁, fun T a b hab => ?_⟩
  have hw : (j ≫ U.fromSpecStalkOfMem y hyU) ≫ U.ι = x ≫ i := by simp [hx]
  let w : Sp K ⟶ pullback U.ι i := pullback.lift _ _ hw
  let p : pullback U.ι i ⟶ Y := pullback.fst U.ι i ≫ U.ι
  have hwp : w ≫ p = j ≫ Y.fromSpecStalk y := by
    rw [← hx, ← hw]
    exact pullback.lift_fst_assoc _ _ hw _
  have : IsReduced (pullback U.ι i) := isReduced_of_isOpenImmersion p
  have : IsDominant w := by
    refine ⟨fun q => ?_⟩
    have h1 : w (IsLocalRing.closedPoint K) ⤳ q := by
      have h0 : p (w (IsLocalRing.closedPoint K)) = ξ :=
        (Scheme.Hom.comp_apply w p _).symm.trans (by rw [hwp]; exact hgen _)
      rw [← p.isOpenEmbedding.isInducing.specializes_iff, h0]
      exact hU _ (pullback.fst U.ι i q).2
    exact h1.mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)
  have e : pullback.fst U.ι i ≫ Y.homOfLE hle ≫ t₁ = pullback.snd U.ι i ≫ t₀ := by
    refine ext_of_isDominant w ?_
    have h2 : U.fromSpecStalkOfMem y hyU ≫ Y.homOfLE hle = U₁.fromSpecStalkOfMem y hy₁ := by
      rw [← cancel_mono U₁.ι]; simp
    simp only [w, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% h2, ← ht₁, hg]
  rw [← pullback.lift_fst a b hab, Category.assoc, e, pullback.lift_snd_assoc]

/- English proof (translation)
Introduce `R _ _ Y₀ Y X i σ τ t₀ hi hd hY hred hint hq hc hval hqf`. Take `⟨hsep, hlft, -⟩` from `GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver hq`. Establish `hfin` using `GlobalTheory.FiniteSubsetsInAffineOpens.of_isQProjOver hq`. Establish `: X.IsSeparated` using `⟨by rw [← terminal.comp_from τ]; infer_instance⟩`. Take `⟨t, ht⟩` from `glue i t₀ fun y => by`.

Use `hint y` as an intermediate fact. Establish `: IsDomain (Y.presheaf.stalk y)` using `GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced _ (hint y)`. Take `⟨W, hW, hSW⟩` from `hfin.exists_isAffineOpen _ (hqf y)`. Conclude with `exists_extension_nhds i σ τ t₀ hc y hW fun V K _ _ _ _ _ _ y' x hx hy => by`. Take `⟨z, hz⟩` from `hval V K y' x hx`.

Conclude with `⟨z, hz, hSW ⟨V, K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, y', z, x, hx, hz, hy, rfl⟩⟩`. Use `⟨t, ht, ext_of_isDominant i ?_⟩` and prove the remaining obligations. Rewrite using `[reassoc_of% ht, hc]`.
-/
theorem exists_extension : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y₀ Y X : Scheme.{0}) (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R) (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → IsReduced Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsQProjOver τ → i ≫ σ = t₀ ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀) → (∀ y : Y, {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∃ t : Y ⟶ X, i ≫ t = t₀ ∧ t ≫ τ = σ := by
  intro R _ _ Y₀ Y X i σ τ t₀ hi hd hY hred hint hq hc hval hqf
  obtain ⟨hsep, hlft, -⟩ := GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver hq
  have hfin := GlobalTheory.FiniteSubsetsInAffineOpens.of_isQProjOver hq
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from τ]; infer_instance⟩
  obtain ⟨t, ht⟩ := glue i t₀ fun y => by
    have := hint y
    have : IsDomain (Y.presheaf.stalk y) := GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced _ (hint y)
    obtain ⟨W, hW, hSW⟩ := hfin.exists_isAffineOpen _ (hqf y)
    exact exists_extension_nhds i σ τ t₀ hc y hW fun V K _ _ _ _ _ _ y' x hx hy => by
      obtain ⟨z, hz⟩ := hval V K y' x hx
      exact ⟨z, hz, hSW ⟨V, K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, y', z, x, hx, hz, hy, rfl⟩⟩
  refine ⟨t, ht, ext_of_isDominant i ?_⟩
  rw [reassoc_of% ht, hc]

end GlobalTheory.ExtendNormal
