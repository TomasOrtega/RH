import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyAltAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalOfGenericFibrePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagExtend

/- English proof (translation)
Use `hB.isQuasicoherent` as an intermediate fact. Use `Scheme.Modules.hom_ext _ _ fun W => ?_` and prove the remaining obligations. Use extensionality with `s`. Use `choose U e _ hx hle he using fun x : W => hB.exists_affine x.2`. Use `Twist.sec_ext_of_cover U hle (fun x hxW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx _⟩) fun x => ?_` and prove the remaining obligations.

Establish `h0 : QCoh.pullbackSections j B (le_refl (j ⁻¹ᵁ U x)) (φ.app (U x) (Twist.resM A (hle x) s)) = 0`. Rewrite using `[← QCoh.pullback_map_app_pullbackSections, h]`. Both sides reduce to the same expression. Establish `h1 : φ.app (U x) (Twist.resM A (hle x) s) = 0`. Use `((he x).basis le_rfl).repr.injective (Finsupp.ext fun i => ?_)` and prove the remaining obligations.

Establish `h2` using `(he x).pullback_basis_repr j le_rfl (le_refl (j ⁻¹ᵁ U x)) (φ.app (U x) (Twist.resM A (hle x) s)) i`. Rewrite `h2` using `[h0, map_zero, Finsupp.zero_apply, ← Scheme.Hom.app_eq_appLE]`. Rewrite using `[map_zero, Finsupp.zero_apply]`. Conclude with `j.app_injective (U x) (h2.symm.trans (map_zero _).symm)`. Conclude with `((Twist.app_resM φ (hle x) s).symm.trans h1).trans (map_zero _).symm`.
-/
theorem eq_zero_of_pullback_map {X G : Scheme.{0}} (j : G ⟶ X) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {A B : X.Modules} {r : ℕ} (hB : IsVB B r) (φ : A ⟶ B) (h : (Scheme.Modules.pullback j).map φ = 0) : φ = 0 := by
  have := hB.isQuasicoherent
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  choose U e _ hx hle he using fun x : W => hB.exists_affine x.2
  refine Twist.sec_ext_of_cover U hle (fun x hxW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx _⟩) fun x => ?_
  have h0 : QCoh.pullbackSections j B (le_refl (j ⁻¹ᵁ U x)) (φ.app (U x) (Twist.resM A (hle x) s)) = 0 := by
    rw [← QCoh.pullback_map_app_pullbackSections, h]
    rfl
  have h1 : φ.app (U x) (Twist.resM A (hle x) s) = 0 := by
    refine ((he x).basis le_rfl).repr.injective (Finsupp.ext fun i => ?_)
    have h2 := (he x).pullback_basis_repr j le_rfl (le_refl (j ⁻¹ᵁ U x)) (φ.app (U x) (Twist.resM A (hle x) s)) i
    rw [h0, map_zero, Finsupp.zero_apply, ← Scheme.Hom.app_eq_appLE] at h2
    rw [map_zero, Finsupp.zero_apply]
    exact j.app_injective (U x) (h2.symm.trans (map_zero _).symm)
  exact ((Twist.app_resM φ (hle x) s).symm.trans h1).trans (map_zero _).symm

/- English proof (translation)
Introduce `i` and use `by obtain ⟨t, ht⟩ : ∃ t : (Scheme.Modules.pullback j).obj (a.F i) ⟶ (Scheme.Modules.pullback j).obj (b.F i), t ≫ (Scheme.Modules.pullback j).map (b.ι i) = (Scheme.Modules.pullback j).map (a.ι i) ≫ (Scheme.Modules.pullback j).map u := h i have h0 : (a.ι i ≫ u) ≫ cokernel.π (b.ι i) …`.
-/
theorem compat_of_pull {X G : Scheme.{0}} (j : G ⟶ X) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {E E' : X.Modules} {r : ℕ} {u : E ⟶ E'} {a : Vert.Flag E r} {b : Vert.Flag E' r}
    (h : Compat ((Scheme.Modules.pullback j).map u) (a.pull j) (b.pull j)) : Compat u a b := fun i => by
  obtain ⟨t, ht⟩ : ∃ t : (Scheme.Modules.pullback j).obj (a.F i) ⟶ (Scheme.Modules.pullback j).obj (b.F i),
      t ≫ (Scheme.Modules.pullback j).map (b.ι i) =
        (Scheme.Modules.pullback j).map (a.ι i) ≫ (Scheme.Modules.pullback j).map u := h i
  have h0 : (a.ι i ≫ u) ≫ cokernel.π (b.ι i) = 0 := by
    refine eq_zero_of_pullback_map j (b.isVB_cokernel i) _ ?_
    rw [Functor.map_comp, Functor.map_comp, ← ht, Category.assoc, ← Functor.map_comp, cokernel.condition,
      Functor.map_zero, comp_zero]
  exact ⟨Abelian.monoLift _ _ h0, Abelian.monoLift_comp _ _ _⟩

/- English proof (translation)
Set `ε : Scheme.Modules.pullback (ν ≫ π) ⋙ Scheme.Modules.pullback j ≅ Scheme.Modules.pullback ((j ≫ ν) ≫ π)` to `Scheme.Modules.pullbackComp j (ν ≫ π) ≪≫ Scheme.Modules.pullbackCongr (Category.assoc j ν π).symm`. Establish `key : (Scheme.Modules.pullbackComp j ν).inv.app ((Scheme.Modules.pullback π).obj E) ≫ (Scheme.Modules.pullback j).map ((Scheme.Modules.pullbackComp ν π).hom.app E) ≫ ε.hom.app E = (Scheme.Modules.pullbackComp (j ≫ ν) π).hom.app E`. Establish `h` using `NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity j ν π) E`. Simplify using `only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at h`. Establish `e : ε.hom.app E = (Scheme.Modules.pullbackComp j (ν ≫ π)).hom.app E ≫ eqToHom (by simp)`.

Simplify using `[ε, Scheme.Modules.pullbackCongr]`. Rewrite using `[e, ← h]`. Simplify using `only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]`. Simplify using the standard rewrite rules. Use `⟨ε.hom.app A ≫ t ≫ (Scheme.Modules.pullbackComp j ν).inv.app B, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_mono (ε.hom.app E)]`. Use `Eq.trans ?_ (ε.hom.naturality c).symm` and prove the remaining obligations. Rewrite using `[← ht, ← key, (Scheme.Modules.pullbackComp j ν).inv.naturality_assoc]`. Simplify using the standard rewrite rules.
-/
theorem exists_fac_comp {G X P Y : Scheme.{0}} (j : G ⟶ X) (ν : X ⟶ P) (π : P ⟶ Y) {A E : Y.Modules} (c : A ⟶ E)
    {B : P.Modules} (b : B ⟶ (Scheme.Modules.pullback π).obj E)
    (t : (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).obj A ⟶ (Scheme.Modules.pullback (j ≫ ν)).obj B)
    (ht : t ≫ (Scheme.Modules.pullback (j ≫ ν)).map b ≫ (Scheme.Modules.pullbackComp (j ≫ ν) π).hom.app E =
      (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).map c) :
    ∃ t' : (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (ν ≫ π)).obj A) ⟶
        (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ν).obj B),
      t' ≫ (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback ν).map b ≫
          (Scheme.Modules.pullbackComp ν π).hom.app E) =
        (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback (ν ≫ π)).map c) := by
  let ε : Scheme.Modules.pullback (ν ≫ π) ⋙ Scheme.Modules.pullback j ≅ Scheme.Modules.pullback ((j ≫ ν) ≫ π) :=
    Scheme.Modules.pullbackComp j (ν ≫ π) ≪≫ Scheme.Modules.pullbackCongr (Category.assoc j ν π).symm
  have key : (Scheme.Modules.pullbackComp j ν).inv.app ((Scheme.Modules.pullback π).obj E) ≫
      (Scheme.Modules.pullback j).map ((Scheme.Modules.pullbackComp ν π).hom.app E) ≫ ε.hom.app E =
      (Scheme.Modules.pullbackComp (j ≫ ν) π).hom.app E := by
    have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity j ν π) E
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at h
    have e : ε.hom.app E = (Scheme.Modules.pullbackComp j (ν ≫ π)).hom.app E ≫ eqToHom (by simp) := by
      simp [ε, Scheme.Modules.pullbackCongr]
    rw [e, ← h]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    simp
  refine ⟨ε.hom.app A ≫ t ≫ (Scheme.Modules.pullbackComp j ν).inv.app B, ?_⟩
  rw [← cancel_mono (ε.hom.app E)]
  refine Eq.trans ?_ (ε.hom.naturality c).symm
  rw [← ht, ← key, (Scheme.Modules.pullbackComp j ν).inv.naturality_assoc]
  simp

/- English proof (translation)
Establish `hpp : IsProper p` using `CommonModel.isProper_of_isProjOver hp.isProjOver`. Establish `hπp : IsProper (π ≫ p)` using `CommonModel.isProper_of_isProjOver hP`. Establish `hπ : IsSeparated π` using `IsSeparated.of_comp π p`. Establish `hb : IsPreimmersion (spMap (algebraMap (𝓞 F) F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))`. Establish `hbf : Flat (spMap (algebraMap (𝓞 F) F))`.

Rewrite using `[Flat.SpecMap_iff]`. Conclude with `RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))`. Establish `hj : IsPreimmersion jY` using `MorphismProperty.of_isPullback (P := @IsPreimmersion) pb.flip hb`. Establish `hjf : Flat jY` using `MorphismProperty.of_isPullback (P := @Flat) pb.flip hbf`. Establish `hja : IsAffineHom jY` using `MorphismProperty.of_isPullback (P := @IsAffineHom) pb.flip inferInstance`.

Establish `hs : IsProper s` using `MorphismProperty.of_isPullback (P := @IsProper) pb hpp`. Establish `hη : genericPoint Y ∈ Set.range jY`. Establish `hx : (p (genericPoint Y)).asIdeal = ⊥`. Use `hp.flat` as an intermediate fact. Establish `h0` using `RatFibreDeg.apply_genericPoint_of_flat (p ≫ spMap (Int.castRingHom (𝓞 F)))`.

Rewrite `h0` using `[genericPoint_eq_bot_of_affine]`. Establish `h' : Ideal.comap (algebraMap ℤ (𝓞 F)) (p (genericPoint Y)).asIdeal = ⊥` using `congrArg PrimeSpectrum.asIdeal h0`. Conclude with `Ideal.eq_bot_of_comap_eq_bot h'`. Rewrite using `[← pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, pb.isoPullback.hom.surjective.range_eq, Set.image_univ, Scheme.Pullback.range_fst]`. Use `⟨(⊥ : PrimeSpectrum F), PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩` and prove the remaining obligations.

Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)`. Establish `hGi : IsIntegral Gs`. Establish `: IsReduced (pullback p (spMap (algebraMap (𝓞 F) F)))` using `CurveClosure.isReduced_pullback_localization (𝓞 F) F (nonZeroDivisors (𝓞 F)) _ _`. Establish `: IsReduced Gs` using `isReduced_of_isOpenImmersion pb.isoPullback.hom`. Take `⟨z, hz⟩` from `hη`.

Establish `: IrreducibleSpace Gs`. Establish `hc : closure {z} = Set.univ`. Rewrite using `[jY.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hz, (genericPoint_spec Y).def, Set.preimage_univ]`. Conclude with `(irreducibleSpace_def _).2 (by`. Use `isIrreducible_singleton (x := z).closure` as an intermediate fact.

Rewrite using `[hc] at this)` and apply the resulting hypothesis. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced Gs`. Establish `hGn : GlobalTheory.IsNormalScheme Gs` using `.of_pred (GlobalTheory.FlagCls.isNormalScheme_of_isPullback_fractionField (𝓞 F) F Y Gs p jY s pb hn)`. Set `g' : Gs ⟶ pullback π jY` to `pullback.lift g (𝟙 _) (by rw [hg, Category.id_comp])`. Establish `h₁ : g' ≫ pullback.snd π jY = 𝟙 _` using `pullback.lift_snd ..`.

Establish `h₂ : g = g' ≫ pullback.fst π jY` using `(pullback.lift_fst ..).symm`. Establish `hc : IsClosedImmersion g'`. Establish `: IsClosedImmersion (g' ≫ pullback.snd π jY)` using `by rw [h₁]; infer_instance`. Conclude with `IsClosedImmersion.of_comp g' (pullback.snd π jY)`. Establish `hq : QuasiCompact g` using `by rw [h₂]; infer_instance`.

Establish `hq' : QuasiSeparated g` using `by rw [h₂]; infer_instance`. Establish `pbP : IsPullback (pullback.fst π jY) (pullback.snd π jY ≫ s) (π ≫ p) (spMap (algebraMap (𝓞 F) F))` using `(IsPullback.of_hasPullback π jY).paste_vert pb`. Use `PreservesNormalization.of_isPullback_localization (nonZeroDivisors (𝓞 F)) pbP` as an intermediate fact. Use `isPreimmersion_of_isPullback_localization (nonZeroDivisors (𝓞 F)) pbP` as an intermediate fact. Establish `pbX : IsPullback g.toNormalization s ((g.fromNormalization ≫ π) ≫ p) (spMap (algebraMap (𝓞 F) F))`.

Use `(isPullback_toNormalization_of_mono g' (pullback.fst π jY) g h₂).paste_vert pbP` as an intermediate fact. Rewrite `this` using `[reassoc_of% h₁, ← Category.assoc]`. Then use the resulting hypothesis. Establish `hfin : IsFinite g.fromNormalization` using `isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) g (π ≫ p) F s (by rw [reassoc_of% hg, pb.w])`. Establish `hXn : GlobalTheory.IsNormalScheme g.normalization` using `GlobalTheory.IsNormalScheme.normalization_of_isIntegral g`. Establish `hXi : IsIntegral g.normalization` using `inferInstance`.

Establish `hjX : Flat g.toNormalization` using `MorphismProperty.of_isPullback (P := @Flat) pbX.flip hbf`. Establish `e : g.toNormalization ≫ g.fromNormalization ≫ π = jY`. Rewrite using `[g.toNormalization_fromNormalization_assoc, hg]`. Establish `hgen` using `RatFibreDeg.apply_genericPoint_of_flat g.toNormalization`. Establish `hgen' : (g.fromNormalization ≫ π) (genericPoint _) = genericPoint Y`.

Rewrite using `[← hgen, ← Scheme.Hom.comp_apply, e, RatFibreDeg.apply_genericPoint_of_flat]`. Establish `hdeg : (g.fromNormalization ≫ π).residueDegree (genericPoint _) ≠ 0`. Introduce `h0`. Establish `h1` using `CurveDegreesCompare.residueDegree_comp g.toNormalization (g.fromNormalization ≫ π) (genericPoint _)`. Rewrite `h1` using `[e, RatFibreDeg.residueDegree_of_surjectiveOnStalks, hgen, h0, zero_mul]`.

Conclude with `one_ne_zero h1`. Establish `hproj : IsProjOver ((g.fromNormalization ≫ π) ≫ p)`. Rewrite using `[Category.assoc]`. Conclude with `isProjOver_comp_of_isFinite _ hP`. Establish `hflat : Flat (((g.fromNormalization ≫ π) ≫ p) ≫ spMap (Int.castRingHom (𝓞 F)))`.

Establish `: CharZero Γ(Gs, ⊤)` using `charZero_of_injective_ringHom (s.appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom : F →+* Γ(Gs, ⊤)).injective`. Conclude with `(flat_int_iff_charZero _).2 g.toNormalization.appTop.hom.charZero`. Conclude with `⟨g.normalization, hXi, g.fromNormalization, g.toNormalization, g.toNormalization_fromNormalization, inferInstance, inferInstance, pbX, ⟨⟨hp.isDomain, hp.finite, hXi, hproj, hflat, DimCover.topologicalKrullDim_eq _ Y _ p _ d hp hproj hflat _ rfl hgen' hdeg⟩, hgen', hdeg⟩, GlobalTh …`.
-/
theorem normalization_lift {F : Type} [Field F] [NumberField F] {Y P Gs : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp (𝓞 F)}
    {d : ℕ} (hp : IsArithVar p d) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) (π : P ⟶ Y) (hP : IsProjOver (π ≫ p))
    {jY : Gs ⟶ Y} {s : Gs ⟶ Sp F} (pb : IsPullback jY s p (spMap (algebraMap (𝓞 F) F))) (g : Gs ⟶ P)
    (hg : g ≫ π = jY) :
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (ν : X ⟶ P) (j : Gs ⟶ X), j ≫ ν = g ∧ QuasiCompact j ∧
      IsSchemeTheoreticallyDominant j ∧ IsPullback j s ((ν ≫ π) ≫ p) (spMap (algebraMap (𝓞 F) F)) ∧
      FlagChain.IsCov p d (ν ≫ π) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by
  have hpp : IsProper p := CommonModel.isProper_of_isProjOver hp.isProjOver
  have hπp : IsProper (π ≫ p) := CommonModel.isProper_of_isProjOver hP
  have hπ : IsSeparated π := IsSeparated.of_comp π p
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have hbf : Flat (spMap (algebraMap (𝓞 F) F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  have hj : IsPreimmersion jY := MorphismProperty.of_isPullback (P := @IsPreimmersion) pb.flip hb
  have hjf : Flat jY := MorphismProperty.of_isPullback (P := @Flat) pb.flip hbf
  have hja : IsAffineHom jY := MorphismProperty.of_isPullback (P := @IsAffineHom) pb.flip inferInstance
  have hs : IsProper s := MorphismProperty.of_isPullback (P := @IsProper) pb hpp

  have hη : genericPoint Y ∈ Set.range jY := by
    have hx : (p (genericPoint Y)).asIdeal = ⊥ := by
      have := hp.flat
      have h0 := RatFibreDeg.apply_genericPoint_of_flat (p ≫ spMap (Int.castRingHom (𝓞 F)))
      rw [genericPoint_eq_bot_of_affine] at h0
      have h' : Ideal.comap (algebraMap ℤ (𝓞 F)) (p (genericPoint Y)).asIdeal = ⊥ :=
        congrArg PrimeSpectrum.asIdeal h0
      exact Ideal.eq_bot_of_comap_eq_bot h'
    rw [← pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      pb.isoPullback.hom.surjective.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
    refine ⟨(⊥ : PrimeSpectrum F), PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have hGi : IsIntegral Gs := by
    have : IsReduced (pullback p (spMap (algebraMap (𝓞 F) F))) :=
      CurveClosure.isReduced_pullback_localization (𝓞 F) F (nonZeroDivisors (𝓞 F)) _ _
    have : IsReduced Gs := isReduced_of_isOpenImmersion pb.isoPullback.hom
    obtain ⟨z, hz⟩ := hη
    have : IrreducibleSpace Gs := by
      have hc : closure {z} = Set.univ := by
        rw [jY.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hz,
          (genericPoint_spec Y).def, Set.preimage_univ]
      exact (irreducibleSpace_def _).2 (by
        have := isIrreducible_singleton (x := z).closure
        rwa [hc] at this)
    exact isIntegral_of_irreducibleSpace_of_isReduced Gs
  have hGn : GlobalTheory.IsNormalScheme Gs :=
    .of_pred (GlobalTheory.FlagCls.isNormalScheme_of_isPullback_fractionField (𝓞 F) F Y Gs p jY s pb hn)

  let g' : Gs ⟶ pullback π jY := pullback.lift g (𝟙 _) (by rw [hg, Category.id_comp])
  have h₁ : g' ≫ pullback.snd π jY = 𝟙 _ := pullback.lift_snd ..
  have h₂ : g = g' ≫ pullback.fst π jY := (pullback.lift_fst ..).symm
  have hc : IsClosedImmersion g' := by
    have : IsClosedImmersion (g' ≫ pullback.snd π jY) := by rw [h₁]; infer_instance
    exact IsClosedImmersion.of_comp g' (pullback.snd π jY)
  have hq : QuasiCompact g := by rw [h₂]; infer_instance
  have hq' : QuasiSeparated g := by rw [h₂]; infer_instance
  have pbP : IsPullback (pullback.fst π jY) (pullback.snd π jY ≫ s) (π ≫ p) (spMap (algebraMap (𝓞 F) F)) :=
    (IsPullback.of_hasPullback π jY).paste_vert pb
  have := PreservesNormalization.of_isPullback_localization (nonZeroDivisors (𝓞 F)) pbP
  have := isPreimmersion_of_isPullback_localization (nonZeroDivisors (𝓞 F)) pbP
  have pbX : IsPullback g.toNormalization s ((g.fromNormalization ≫ π) ≫ p) (spMap (algebraMap (𝓞 F) F)) := by
    have := (isPullback_toNormalization_of_mono g' (pullback.fst π jY) g h₂).paste_vert pbP
    rwa [reassoc_of% h₁, ← Category.assoc] at this
  have hfin : IsFinite g.fromNormalization :=
    isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) g (π ≫ p) F s (by rw [reassoc_of% hg, pb.w])
  have hXn : GlobalTheory.IsNormalScheme g.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral g
  have hXi : IsIntegral g.normalization := inferInstance
  have hjX : Flat g.toNormalization := MorphismProperty.of_isPullback (P := @Flat) pbX.flip hbf
  have e : g.toNormalization ≫ g.fromNormalization ≫ π = jY := by
    rw [g.toNormalization_fromNormalization_assoc, hg]
  have hgen := RatFibreDeg.apply_genericPoint_of_flat g.toNormalization
  have hgen' : (g.fromNormalization ≫ π) (genericPoint _) = genericPoint Y := by
    rw [← hgen, ← Scheme.Hom.comp_apply, e, RatFibreDeg.apply_genericPoint_of_flat]
  have hdeg : (g.fromNormalization ≫ π).residueDegree (genericPoint _) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp g.toNormalization (g.fromNormalization ≫ π) (genericPoint _)
    rw [e, RatFibreDeg.residueDegree_of_surjectiveOnStalks, hgen, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hproj : IsProjOver ((g.fromNormalization ≫ π) ≫ p) := by
    rw [Category.assoc]
    exact isProjOver_comp_of_isFinite _ hP
  have hflat : Flat (((g.fromNormalization ≫ π) ≫ p) ≫ spMap (Int.castRingHom (𝓞 F))) := by
    have : CharZero Γ(Gs, ⊤) :=
      charZero_of_injective_ringHom (s.appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom : F →+* Γ(Gs, ⊤)).injective
    exact (flat_int_iff_charZero _).2 g.toNormalization.appTop.hom.charZero
  exact ⟨g.normalization, hXi, g.fromNormalization, g.toNormalization, g.toNormalization_fromNormalization,
    inferInstance, inferInstance, pbX, ⟨⟨hp.isDomain, hp.finite, hXi, hproj, hflat,
      DimCover.topologicalKrullDim_eq _ Y _ p _ d hp hproj hflat _ rfl hgen' hdeg⟩, hgen', hdeg⟩,
    GlobalTheory.IsNormalScheme.pred _⟩

/- English proof (translation)
Introduce `F _ _ Y _ p d hp hn ι _ N N' n hN' u fl Gs jY s pb hu`. Take `⟨P, _, π, fu, hfb, hP, -⟩` from `GlobalTheory.FlagEx.main (𝓞 F) Y p d hp hn ι N' n hN'`. Take `⟨g, ⟨hg, hfl⟩, -⟩` from `hfb Gs jY fun a => ((fl a).pull jY).ofIso (asIso ((Scheme.Modules.pullback jY).map (u a)))`. Take `⟨X, _, ν, j, rfl, _, _, h₁, h₂, h₃⟩` from `normalization_lift hp hn π hP.isProjOver pb g hg`. Substitute `hg` using the available equality.

Use `⟨X, inferInstance, ν ≫ π, fun a => ((fu a).pull ν).ofIso ((Scheme.Modules.pullbackComp ν π).app (N' a)), j, (Category.assoc ..).symm, h₁, h₂, h₃, fun a => compat_of_pull j fun i => ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩ : ∃ e : (Scheme.Modules.pullback (j ≫ ν)).obj ((fu a).F i) ≅ (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).obj ((fl a).F i), e.hom ≫ (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).map ((fl a).ι i) ≫ (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).map (u a) = (Scheme.Modules.pullback (j ≫ ν)). …` from `hfl a i`. Take `⟨t, ht⟩` from `exists_fac_comp j ν π ((fl a).ι i ≫ u a) ((fu a).ι i) e.inv (by`. Rewrite using `[Iso.inv_comp_eq, Functor.map_comp]`. Rewrite using `[he]`.

Simplify using `[Scheme.Modules.pullbackCongr])`. Use `⟨t, ht.trans ?_⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp, Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp (𝓞 F)) (d : ℕ), IsArithVar p d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ (ι : Type) [Fintype ι] (N N' : ι → Y.Modules) (n : ι → ℕ),
    (∀ a, IsVB (N' a) (n a)) → ∀ (u : ∀ a, N a ⟶ N' a) (fl : ∀ a, Vert.Flag (N a) (n a))
      (Gs : Scheme.{0}) (jY : Gs ⟶ Y) (s : Gs ⟶ Sp F), IsPullback jY s p (spMap (algebraMap (𝓞 F) F)) →
    (∀ a, IsIso ((Scheme.Modules.pullback jY).map (u a))) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (ρ : X ⟶ Y) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback ρ).obj (N' a)) (n a)) (j : Gs ⟶ X),
      j ≫ ρ = jY ∧ IsPullback j s (ρ ≫ p) (spMap (algebraMap (𝓞 F) F)) ∧ FlagChain.IsCov p d ρ ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∀ a, Compat ((Scheme.Modules.pullback ρ).map (u a)) ((fl a).pull ρ) (fl' a) := by
  intro F _ _ Y _ p d hp hn ι _ N N' n hN' u fl Gs jY s pb hu
  obtain ⟨P, _, π, fu, hfb, hP, -⟩ := GlobalTheory.FlagEx.main (𝓞 F) Y p d hp hn ι N' n hN'
  obtain ⟨g, ⟨hg, hfl⟩, -⟩ := hfb Gs jY fun a =>
    ((fl a).pull jY).ofIso (asIso ((Scheme.Modules.pullback jY).map (u a)))
  obtain ⟨X, _, ν, j, rfl, _, _, h₁, h₂, h₃⟩ := normalization_lift hp hn π hP.isProjOver pb g hg
  subst hg
  refine ⟨X, inferInstance, ν ≫ π, fun a => ((fu a).pull ν).ofIso ((Scheme.Modules.pullbackComp ν π).app (N' a)), j,
    (Category.assoc ..).symm, h₁, h₂, h₃, fun a => compat_of_pull j fun i => ?_⟩
  obtain ⟨e, he⟩ : ∃ e : (Scheme.Modules.pullback (j ≫ ν)).obj ((fu a).F i) ≅
      (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).obj ((fl a).F i),
      e.hom ≫ (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).map ((fl a).ι i) ≫
          (Scheme.Modules.pullback ((j ≫ ν) ≫ π)).map (u a) =
        (Scheme.Modules.pullback (j ≫ ν)).map ((fu a).ι i) ≫ (Scheme.Modules.pullbackComp (j ≫ ν) π).hom.app (N' a) ≫
          (Scheme.Modules.pullbackCongr rfl).hom.app (N' a) := hfl a i
  obtain ⟨t, ht⟩ := exists_fac_comp j ν π ((fl a).ι i ≫ u a) ((fu a).ι i) e.inv (by
    rw [Iso.inv_comp_eq, Functor.map_comp]
    rw [he]
    simp [Scheme.Modules.pullbackCongr])
  refine ⟨t, ht.trans ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  rfl

end GlobalTheory.FlagExtend
