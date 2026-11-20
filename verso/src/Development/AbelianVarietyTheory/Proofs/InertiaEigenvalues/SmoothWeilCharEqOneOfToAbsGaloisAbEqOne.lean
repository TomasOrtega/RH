import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalArtinHasNormGroups
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import GroundTheory.LocalFields.LocalArtinMap
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilCharKer

open GlobalTheory.LocDict GlobalTheory.HeckeGal Neutral.B1

/- English proof (translation)
Establish `: Finite (Γ ⧸ F)` using `Subgroup.quotient_finite_of_isOpen F hF`. Establish `: F.FiniteIndex` using `Subgroup.finiteIndex_of_finite_quotient`. Establish `hN : IsOpen (F.normalCore : Set Γ)` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (F.normalCore_isClosed (F.isClosed_of_isOpen hF))`. Rewrite using `[commutator, Subgroup.commutator_le]`. Introduce `g _ k _`.

Take `⟨σ, hσ⟩` from `hd g _ hN`. Take `⟨τ, hτ⟩` from `hd k _ hN`. Establish `e1 : QuotientGroup.mk' F.normalCore g = QuotientGroup.mk' F.normalCore (ψ σ)` using `QuotientGroup.eq.2 hσ`. Establish `e2 : QuotientGroup.mk' F.normalCore k = QuotientGroup.mk' F.normalCore (ψ τ)` using `QuotientGroup.eq.2 hτ`. Establish `e3 : QuotientGroup.mk' F.normalCore (ψ (σ * τ * σ⁻¹ * τ⁻¹)) = QuotientGroup.mk' F.normalCore (g * k * g⁻¹ * k⁻¹)`.

Simplify using `only [map_mul, map_inv, e1, e2]`. Establish `e4` using `F.mul_mem (hc σ τ) (F.normalCore_le (QuotientGroup.eq.1 e3))`. Rewrite `e4` using `[mul_inv_cancel_left]`. Conclude with `e4`.
-/
theorem commutator_le_of_dense {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [Group W] (ψ : W →* Γ) (hd : ∀ (g : Γ) (H : Subgroup Γ), IsOpen (H : Set Γ) → ∃ σ : W, g⁻¹ * ψ σ ∈ H)
    (F : Subgroup Γ) (hF : IsOpen (F : Set Γ)) (hc : ∀ σ τ : W, ψ (σ * τ * σ⁻¹ * τ⁻¹) ∈ F) :
    commutator Γ ≤ F := by
  have : Finite (Γ ⧸ F) := Subgroup.quotient_finite_of_isOpen F hF
  have : F.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN : IsOpen (F.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (F.normalCore_isClosed (F.isClosed_of_isOpen hF))
  rw [commutator, Subgroup.commutator_le]
  intro g _ k _
  obtain ⟨σ, hσ⟩ := hd g _ hN
  obtain ⟨τ, hτ⟩ := hd k _ hN
  have e1 : QuotientGroup.mk' F.normalCore g = QuotientGroup.mk' F.normalCore (ψ σ) := QuotientGroup.eq.2 hσ
  have e2 : QuotientGroup.mk' F.normalCore k = QuotientGroup.mk' F.normalCore (ψ τ) := QuotientGroup.eq.2 hτ
  have e3 : QuotientGroup.mk' F.normalCore (ψ (σ * τ * σ⁻¹ * τ⁻¹)) =
      QuotientGroup.mk' F.normalCore (g * k * g⁻¹ * k⁻¹) := by
    simp only [map_mul, map_inv, e1, e2]
  have e4 := F.mul_mem (hc σ τ) (F.normalCore_le (QuotientGroup.eq.1 e3))
  rw [mul_inv_cancel_left] at e4
  exact e4

/- English proof (translation)
Establish `e : normGroup K L = (GroundTheory.LocalField.normUnits K L).range` using `rfl`. Rewrite using `[e, ← GroundTheory.LocalField.ker_restrictAb_localArtinMap (Ω := AlgebraicClosure K) L, Subgroup.index_ker, MonoidHom.range_eq_top.2 (GroundTheory.LocalField.surjective_restrictAb_localArtinMap L), Subgroup.card_top]`.
-/
theorem index_normGroup {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [CharZero K] (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsAbelianGalois K L] :
    (normGroup K L).index = Nat.card (L ≃ₐ[K] L) := by
  have e : normGroup K L = (GroundTheory.LocalField.normUnits K L).range := rfl
  rw [e, ← GroundTheory.LocalField.ker_restrictAb_localArtinMap (Ω := AlgebraicClosure K) L, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (GroundTheory.LocalField.surjective_restrictAb_localArtinMap L), Subgroup.card_top]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
The claim follows from `GlobalTheory.T.globalArtin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w`.
-/
theorem art_inj {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    Function.Injective fun x : (w.adicCompletion E)ˣ => art (localIdele E w x) :=
  GlobalTheory.T.globalArtin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w

/- English proof (translation)
Take `⟨h1, h2⟩` from `GlobalTheory.LocNormGrp.art_range_weil E Ω A w h art ha`. Use `choose a ha' using h1`. Use `⟨MonoidHom.mk' a fun σ τ => art_inj ha ?_, fun y => ?_, ha'⟩` and prove the remaining obligations. Simplify using `only [map_mul, ha', Subgroup.coe_mul]`. Take `⟨τ, hτ⟩` from `h2 y`.

Conclude with `⟨τ, art_inj ha ((ha' τ).trans hτ.symm)⟩`.
-/
theorem exists_inverse (h : IsPlaceOver A w) {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧
      ∀ σ : Weil h, art (localIdele E w (a σ)) = toAb E Ω σ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LocNormGrp.art_range_weil E Ω A w h art ha
  choose a ha' using h1
  refine ⟨MonoidHom.mk' a fun σ τ => art_inj ha ?_, fun y => ?_, ha'⟩
  · simp only [map_mul, ha', Subgroup.coe_mul]
  · obtain ⟨τ, hτ⟩ := h2 y
    exact ⟨τ, art_inj ha ((ha' τ).trans hτ.symm)⟩

/- English proof (translation)
Take `⟨K, hK, hloc, hHK⟩` from `GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hfin hop`. Use `haveI : NumberField K := NumberField.of_module_finite E K`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Use `haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) K⟩`. Take `⟨W, h'⟩` from `GlobalTheory.LocNormGrp.exists_place h K`.

Take `⟨ι, hι⟩` from `GlobalTheory.LocDict.exists_isLocEmb E Ω A w h`. Take `⟨ι', hι'⟩` from `GlobalTheory.LocDict.exists_isLocEmb K Ω A W h'`. Take `⟨f, b, hf, hb1, hb2, hfE, -, -, -, hNc, hNg⟩` from `GlobalTheory.T.local_embeddings_tower_compatible E K Ω A w W h h' hloc ι ι' hι hι'`. Use `letI := f.toAlgebra`. Establish `hN` using `GlobalTheory.T.completion_embedding_compatible_closures E K w W (fun x : K => ι (algebraMap K Ω x)) f b hf hb1 (fun x => by rw [hb2, ι'.commutes, IsScalarTower.algebraMap_apply K (W.adicCompletion K)]) hfE`.

Take `⟨art, hart⟩` from `GlobalTheory.globalArtinReciprocity_holds E Ω`. Take `⟨artK, hartK⟩` from `GlobalTheory.globalArtinReciprocity_holds K Ω`. Take `⟨a, hasurj, ha⟩` from `exists_inverse h hart`. Set `N` to `Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)`. Establish `key` using `GlobalTheory.LocNormGrp.art_norm_eq_res E K Ω art artK hart hartK w W (GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h') N (Continuous.units_map _ hNc) fun z => Units.ext (hNg z)`.

Take `⟨h1, -⟩` from `GlobalTheory.LocNormGrp.art_range_weil K Ω A W h' artK hartK`. Use `set Kw := w.adicCompletion E`. Establish `: CharZero Kw` using `charZero_of_injective_algebraMap (algebraMap E Kw).injective`. Establish `: IsGalois Kw (Kbar w)` using `IsAlgClosure.isGalois Kw (Kbar w)`. Use `set L := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hL`.

Establish `hHN : H ≤ (normGroup Kw L).comap a` using `fun s hs => by`. Take `⟨τ, hτ⟩` from `GlobalTheory.T.exists_weil_of_fixes' E K Ω A w W h h' s ((hHK s).1 hs)`. Take `⟨y, hy⟩` from `h1 τ`. Rewrite using `[Subgroup.mem_comap, hN]`. Conclude with `⟨y, art_inj hart ((key y τ s hτ hy).trans (ha s).symm)⟩`.

Establish `hfd : FiniteDimensional Kw L`. Set `pb` to `Field.powerBasisOfFiniteOfSeparable E K`. Set `j : K →ₐ[E] Kbar w` to `ι.comp K.val`. Establish `hfd0 : FiniteDimensional Kw (IntermediateField.adjoin Kw {j pb.gen})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)`. Establish `hle : L ≤ IntermediateField.adjoin Kw {j pb.gen}`.

Rewrite using `[hL, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨p, rfl⟩` from `pb.exists_eq_aeval' x`. Use `show j (aeval pb.gen p) ∈ IntermediateField.adjoin Kw {j pb.gen}`. Rewrite using `[← aeval_algHom_apply, ← aeval_map_algebraMap Kw]`.

Conclude with `IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)`. Conclude with `FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective`. Take `⟨θ, hθ, -, hl⟩` from `GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι`. Set `ψ : Weil h →* GalLoc w` to `θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))`. Establish `hψ : ∀ s : Weil h, Lifts ι (ψ s) (s : G E Ω)` using `fun s => hl _`.

Establish `hψ' : ∀ (s : Weil h) (g : GalLoc w), Lifts ι g s → ψ s = g` using `fun s g hg => by`. Establish `e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) s`. Use `hl (θ.symm g)` as an intermediate fact. Rewrite `this` using `[θ.apply_symm_apply]`. Conclude with `Subtype.ext (this.eq hg)`.

Use `show θ _ = g`. Rewrite using `[← e, θ.apply_symm_apply]`. Establish `hHL : ∀ s : Weil h, s ∈ H ↔ ψ s ∈ L.fixingSubgroup` using `fun s => by`. Rewrite using `[hHK, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, hL, IntermediateField.adjoin_le_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `hs _ ⟨x, rfl⟩`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`. Introduce `g hg`. Use `(Subgroup.zpowers_le (H := MulAction.stabilizer (GalLoc w) (ι (algebraMap K Ω x)))).2 ?_ hg` and prove the remaining obligations. Use `show ψ s (ι x) = ι x`.

Rewrite using `[hψ, hs]`. Introduce `hs x`. Use `(IntermediateField.mem_fixedField_iff _ _).1 (hs ⟨x, rfl⟩) _ (Subgroup.mem_zpowers _)` as an intermediate fact. Rewrite `this` using `[hψ]`. Conclude with `ι.toRingHom.injective this`.

Establish `hLo : IsOpen (L.fixingSubgroup : Set (GalLoc w))` using `L.fixingSubgroup_isOpen`. Establish `hcl : commutator (GalLoc w) ≤ L.fixingSubgroup` using `commutator_le_of_dense ψ (fun g U hU => by`. Take `⟨s, g', h1, h2⟩` from `GlobalTheory.LocDec.exists_lifts_mul_mem A w h ι θ hθ hl g U hU`. Conclude with `⟨s, by rwa [hψ' s g' h1]⟩) _ hLo fun s t => (hHL _).1 (hcomm s t)`. Establish `hnorm : L.fixingSubgroup.Normal` using `Subgroup.Normal.of_commutator_le _ hcl`.

Establish `hgal : IsGalois Kw L` using `(InfiniteGalois.normal_iff_isGalois L).1 hnorm`. Establish `hab : IsAbelianGalois Kw L` using `GroundTheory.LocalField.isAbelianGalois_of_le_maximalAbelianExtension L (by`. Rewrite using `[GroundTheory.LocalField.maximalAbelianExtension, IntermediateField.le_iff_le]`. Conclude with `Subgroup.topologicalClosure_minimal _ hcl (Subgroup.isClosed_of_isOpen _ hLo))`. Establish `hHker : H = ((AlgEquiv.restrictNormalHom L).comp ψ).ker`.

Use extensionality with `s`. Rewrite using `[hHL, ← IntermediateField.restrictNormalHom_ker]`. Both sides reduce to the same expression. Establish `i1 : H.index ≤ Nat.card (L ≃ₐ[Kw] L)`. Rewrite using `[hHker, Subgroup.index_ker]`.

Conclude with `Subgroup.card_le_card_group _`. Establish `i2 : ((normGroup Kw L).comap a).index = Nat.card (L ≃ₐ[Kw] L)`. Rewrite using `[Subgroup.index_comap_of_surjective _ hasurj, index_normGroup]`. Establish `i3` using `Subgroup.relIndex_mul_index hHN`. Establish `i4 : H.relIndex ((normGroup Kw L).comap a) = 1`.

Use `hfin.index_ne_zero` as an intermediate fact. Rewrite `i3` using `[i2]`. Establish `hp : 0 < Nat.card (L ≃ₐ[Kw] L)` using `Nat.card_pos`. Generalize the expression as in `H.relIndex ((normGroup Kw L).comap a) = r at i3`. Break down `r with _ | _ | r` into its components or cases.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Use the polynomial consequences of the given equalities and inequalities. Use `Subgroup.relIndex_eq_one.1 i4 ?_` and prove the remaining obligations. Establish `: a σ = 1` using `art_inj hart (by simp only [ha, hσ, map_one])`.

Rewrite using `[Subgroup.mem_comap, this]`. Conclude with `Subgroup.one_mem _`.
-/
theorem mem_of_toAb_eq_one (h : IsPlaceOver A w) (H : Subgroup (Weil h)) (hfin : H.FiniteIndex)
    (hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H}) (hcomm : ∀ σ τ : Weil h, σ * τ * σ⁻¹ * τ⁻¹ ∈ H)
    (σ : Weil h) (hσ : toAb E Ω σ = 1) : σ ∈ H := by
  obtain ⟨K, hK, hloc, hHK⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hfin hop
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  obtain ⟨W, h'⟩ := GlobalTheory.LocNormGrp.exists_place h K
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb E Ω A w h
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb K Ω A W h'
  obtain ⟨f, b, hf, hb1, hb2, hfE, -, -, -, hNc, hNg⟩ := GlobalTheory.T.local_embeddings_tower_compatible E K Ω A w W h h' hloc ι ι' hι hι'
  letI := f.toAlgebra
  have hN := GlobalTheory.T.completion_embedding_compatible_closures E K w W (fun x : K => ι (algebraMap K Ω x)) f b hf hb1
    (fun x => by rw [hb2, ι'.commutes, IsScalarTower.algebraMap_apply K (W.adicCompletion K)]) hfE
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds E Ω
  obtain ⟨artK, hartK⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  obtain ⟨a, hasurj, ha⟩ := exists_inverse h hart
  let N := Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)
  have key := GlobalTheory.LocNormGrp.art_norm_eq_res E K Ω art artK hart hartK w W
    (GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h') N (Continuous.units_map _ hNc) fun z => Units.ext (hNg z)
  obtain ⟨h1, -⟩ := GlobalTheory.LocNormGrp.art_range_weil K Ω A W h' artK hartK
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set L := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hL

  have hHN : H ≤ (normGroup Kw L).comap a := fun s hs => by
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_weil_of_fixes' E K Ω A w W h h' s ((hHK s).1 hs)
    obtain ⟨y, hy⟩ := h1 τ
    rw [Subgroup.mem_comap, hN]
    exact ⟨y, art_inj hart ((key y τ s hτ hy).trans (ha s).symm)⟩

  have hfd : FiniteDimensional Kw L := by
    let pb := Field.powerBasisOfFiniteOfSeparable E K
    let j : K →ₐ[E] Kbar w := ι.comp K.val
    have hfd0 : FiniteDimensional Kw (IntermediateField.adjoin Kw {j pb.gen}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    have hle : L ≤ IntermediateField.adjoin Kw {j pb.gen} := by
      rw [hL, IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      obtain ⟨p, rfl⟩ := pb.exists_eq_aeval' x
      show j (aeval pb.gen p) ∈ IntermediateField.adjoin Kw {j pb.gen}
      rw [← aeval_algHom_apply, ← aeval_map_algebraMap Kw]
      exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  obtain ⟨θ, hθ, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hψ : ∀ s : Weil h, Lifts ι (ψ s) (s : G E Ω) := fun s => hl _
  have hψ' : ∀ (s : Weil h) (g : GalLoc w), Lifts ι g s → ψ s = g := fun s g hg => by
    have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) s := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    show θ _ = g
    rw [← e, θ.apply_symm_apply]
  have hHL : ∀ s : Weil h, s ∈ H ↔ ψ s ∈ L.fixingSubgroup := fun s => by
    rw [hHK, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, hL, IntermediateField.adjoin_le_iff]
    constructor
    · rintro hs _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      refine (Subgroup.zpowers_le (H := MulAction.stabilizer (GalLoc w) (ι (algebraMap K Ω x)))).2 ?_ hg
      show ψ s (ι x) = ι x
      rw [hψ, hs]
    · intro hs x
      have := (IntermediateField.mem_fixedField_iff _ _).1 (hs ⟨x, rfl⟩) _ (Subgroup.mem_zpowers _)
      rw [hψ] at this
      exact ι.toRingHom.injective this
  have hLo : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := L.fixingSubgroup_isOpen
  have hcl : commutator (GalLoc w) ≤ L.fixingSubgroup :=
    commutator_le_of_dense ψ (fun g U hU => by
      obtain ⟨s, g', h1, h2⟩ := GlobalTheory.LocDec.exists_lifts_mul_mem A w h ι θ hθ hl g U hU
      exact ⟨s, by rwa [hψ' s g' h1]⟩) _ hLo fun s t => (hHL _).1 (hcomm s t)
  have hnorm : L.fixingSubgroup.Normal := Subgroup.Normal.of_commutator_le _ hcl
  have hgal : IsGalois Kw L := (InfiniteGalois.normal_iff_isGalois L).1 hnorm
  have hab : IsAbelianGalois Kw L := GroundTheory.LocalField.isAbelianGalois_of_le_maximalAbelianExtension L (by
    rw [GroundTheory.LocalField.maximalAbelianExtension, IntermediateField.le_iff_le]
    exact Subgroup.topologicalClosure_minimal _ hcl (Subgroup.isClosed_of_isOpen _ hLo))

  have hHker : H = ((AlgEquiv.restrictNormalHom L).comp ψ).ker := by
    ext s
    rw [hHL, ← IntermediateField.restrictNormalHom_ker]; rfl
  have i1 : H.index ≤ Nat.card (L ≃ₐ[Kw] L) := by
    rw [hHker, Subgroup.index_ker]
    exact Subgroup.card_le_card_group _
  have i2 : ((normGroup Kw L).comap a).index = Nat.card (L ≃ₐ[Kw] L) := by
    rw [Subgroup.index_comap_of_surjective _ hasurj, index_normGroup]
  have i3 := Subgroup.relIndex_mul_index hHN
  have i4 : H.relIndex ((normGroup Kw L).comap a) = 1 := by
    have := hfin.index_ne_zero
    rw [i2] at i3
    have hp : 0 < Nat.card (L ≃ₐ[Kw] L) := Nat.card_pos
    generalize H.relIndex ((normGroup Kw L).comap a) = r at i3
    rcases r with _ | _ | r
    · omega
    · rfl
    · nlinarith
  refine Subgroup.relIndex_eq_one.1 i4 ?_
  have : a σ = 1 := art_inj hart (by simp only [ha, hσ, map_one])
  rw [Subgroup.mem_comap, this]
  exact Subgroup.one_mem _

/- English proof (translation)
Set `n` to `(deg σ).natAbs + 1`. Set `r : Weil h →* Multiplicative (ZMod n)` to `(AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp (degHom h)`. Establish `hr : ∀ s, s ∈ r.ker ↔ (n : ℤ) ∣ deg s` using `fun s => by`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Both sides reduce to the same expression.

Use `mem_of_toAb_eq_one h r.ker inferInstance (by simp [hr]) (fun s t => by simp [hr]) σ hσ` as an intermediate fact. Rewrite `this` using `[hr]`. Conclude with `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by simp only [Int.natAbs_natCast]; omega)`.
-/
theorem deg_eq_zero_of_toAb_eq_one (h : IsPlaceOver A w) (σ : Weil h) (hσ : toAb E Ω σ = 1) : deg σ = 0 := by
  let n := (deg σ).natAbs + 1
  let r : Weil h →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp (degHom h)
  have hr : ∀ s, s ∈ r.ker ↔ (n : ℤ) ∣ deg s := fun s => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; rfl
  have := mem_of_toAb_eq_one h r.ker inferInstance
    (by simp [hr]) (fun s t => by simp [hr]) σ hσ
  rw [hr] at this
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by simp only [Int.natAbs_natCast]; omega)

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h ξ hξ σ hσ`. Set `ξ' : Weil h →* ℂˣ` to `ξ * unrChar h (ξ (frob h))⁻¹`. Establish `h0 : ∀ s, deg s = 0 → ξ' s = ξ s` using `fun s hs => by simp [ξ', hs]`. Establish `h1 : ξ' (frob h) = 1` using `by simp [ξ']`. Establish `hop : IsOpen {s : Ine (F` using `E) A | ineIncl h s ∈ ξ'.ker} := by`.

Simplify using `only [MonoidHom.mem_ker, h0 _ (deg_ineIncl _)]`. Conclude with `hξ`. Use `compactSpace_Ine (E := E) A` as an intermediate fact. Establish `hq : Finite (Ine (F` using `E) A ⧸ (ξ'.comp (ineIncl h)).ker) := Subgroup.quotient_finite_of_isOpen _ hop`. Establish `hr : Finite (ξ'.comp (ineIncl h)).range` using `Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).toEquiv`.

Establish `hle : ξ'.range ≤ (ξ'.comp (ineIncl h)).range`. Introduce and unpack `_ ⟨s, rfl⟩`. Take `⟨t, ht⟩` from `exists_eq_zpow_mul (deg_frob (h := h)) s`. Use `⟨t, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [ht, map_mul, map_zpow, h1, _root_.one_zpow, one_mul]`.

Both sides reduce to the same expression. Establish `hr' : Finite ξ'.range` using `Finite.of_injective _ (Subgroup.inclusion_injective hle)`. Use `mem_of_toAb_eq_one h ξ'.ker inferInstance hop (fun s t => by` as an intermediate fact. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `only [map_mul, map_inv]`.

Rewrite using `[mul_comm (ξ' s) (ξ' t)]`. Use the proof step `group) σ hσ`. Rewrite using `[← h0 σ (deg_eq_zero_of_toAb_eq_one h σ hσ)]`. Conclude with `this`.
-/
theorem apply_eq_one_of_toAb_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ξ : Weil h →* ℂˣ), GlobalTheory.WeilDeligne.IsSmooth ξ → ∀ σ : Weil h, GlobalTheory.HeckeGal.toAb E Ω σ = 1 → ξ σ = 1 := by
  intro E Ω _ _ _ _ _ A w h ξ hξ σ hσ
  let ξ' : Weil h →* ℂˣ := ξ * unrChar h (ξ (frob h))⁻¹
  have h0 : ∀ s, deg s = 0 → ξ' s = ξ s := fun s hs => by simp [ξ', hs]
  have h1 : ξ' (frob h) = 1 := by simp [ξ']
  have hop : IsOpen {s : Ine (F := E) A | ineIncl h s ∈ ξ'.ker} := by
    simp only [MonoidHom.mem_ker, h0 _ (deg_ineIncl _)]
    exact hξ
  have := compactSpace_Ine (E := E) A
  have hq : Finite (Ine (F := E) A ⧸ (ξ'.comp (ineIncl h)).ker) := Subgroup.quotient_finite_of_isOpen _ hop
  have hr : Finite (ξ'.comp (ineIncl h)).range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).toEquiv
  have hle : ξ'.range ≤ (ξ'.comp (ineIncl h)).range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
    refine ⟨t, ?_⟩
    conv_rhs => rw [ht, map_mul, map_zpow, h1, _root_.one_zpow, one_mul]
    rfl
  have hr' : Finite ξ'.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have := mem_of_toAb_eq_one h ξ'.ker inferInstance hop (fun s t => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (ξ' s) (ξ' t)]
    group) σ hσ
  rw [← h0 σ (deg_eq_zero_of_toAb_eq_one h σ hσ)]
  exact this

end GlobalTheory.WeilCharKer

end
