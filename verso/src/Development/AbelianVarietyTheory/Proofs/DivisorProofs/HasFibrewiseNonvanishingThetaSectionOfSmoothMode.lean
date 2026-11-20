import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaOfStalk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InjectiveOfFlatLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNZOfPolAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoveringAndSmoothnessIffOfSeparableSplitting
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarized
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily

open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.ThetaNormal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models
open scoped CategoryTheory.Obj

/- English proof (translation)
Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial`. Set `ι` to `pullback.fst G.hom hU.fromSpec`.

Set `f` to `pullback.snd G.hom hU.fromSpec`. Set `gm : Γ(X, U) →+* R` to `ψ.comp (X.presheaf.germ U x hx).hom`. Establish `hξ : spMap gm ≫ hU.fromSpec = spMap ψ ≫ X.fromSpecStalk x`. Rewrite using `[← hU.fromSpecStalk_eq_fromSpecStalk hx]`. Use `show Spec.map (CommRingCat.ofHom (X.presheaf.germ U x hx).hom ≫ CommRingCat.ofHom ψ) ≫ _ = _`.

Rewrite using `[Spec.map_comp, Category.assoc]`. Both sides reduce to the same expression. Set `π : G'.left ⟶ pullback G.hom hU.fromSpec` to `pullback.lift φ (G'.hom ≫ spMap gm) (by rw [Category.assoc, hξ, hφ.w])`. Establish `hπ : π ≫ ι = φ` using `pullback.lift_fst _ _ _`. Establish `hP : IsPullback π G'.hom f (spMap gm)` using `IsPullback.of_right (by rw [hπ, hξ]; exact hφ) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)`.

Establish `: CompactSpace (pullback G.hom hU.fromSpec : Scheme.{0})` using `QuasiCompact.compactSpace_of_compactSpace f`. Establish `: QuasiSeparatedSpace (pullback G.hom hU.fromSpec : Scheme.{0})` using `quasiSeparatedSpace_of_quasiSeparated f`. Establish `hflat : gm.Flat`. Establish `h₀ : (X.presheaf.germ U x hx).hom.Flat`. Use `letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)`.

Use `hU.isLocalization_stalk ⟨x, hx⟩` as an intermediate fact. Conclude with `RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)`. Conclude with `RingHom.Flat.comp h₀ hψ`. Establish `hM` using `pull_isLB hL ι`. Take `⟨w, hw'⟩ : LBIso ((L.pull ι).pull π) (L'.pull (𝟙 _))` from `LBIso.chartPull (chartPullLinComb L ι (fun _ : PUnit => π) (fun _ => φ) (fun _ => 1) (𝟙 _) fun _ => hπ.trans (Category.id_comp _).symm) (Geo.Tor.chartPullPull L' _ _ rfl) hw.symm`.

Take `⟨θ', hθ'⟩` from `hθ`. Take `⟨σ, hσ⟩` from `ThetaLocal.exists_sec_pull hL' (pull_isLB hM π) (𝟙 _) w hw' (O := ⊤) le_top _ (SecSpread.res_mem_secOn θ' ⊤)`. Take `⟨z, i, hz, hi⟩` from `hθ' (IsLocalRing.closedPoint _)`. Take `⟨k, hk⟩` from `hσ z i ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, G'.left.basicOpen_le _ hi⟩, hi⟩)`. Take `⟨k, rfl⟩ : ∃ j, k = fun _ => j` from `⟨k PUnit.unit, rfl⟩`.

Establish `hk₁` using `G'.left.basicOpen_le _ hk`. Establish `hk₂ : π z ∈ (L.pull ι).U k` using `mem_pull.1 hk₁`. Take `⟨n, a, u, hu⟩` from `FlatSec.exists_comb_of_flat _ _ gm hflat _ f _ π G'.hom hP _ hM σ`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, π z ∈ Scheme.basicOpen _ ((u j).f k) := by`. Assume the negation of the conclusion as `hn`.

Establish `h₁` using `(AbLocusPull.isUnit_gs_iff (𝟙 _) z _ hk₁ _).2 hk`. Rewrite `h₁` using `[hu z k hk₂]`. Use `(IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_) h₁` and prove the remaining obligations. Conclude with `fun h₂ => hn ⟨j, (AbLocusPull.isUnit_gs_iff π z _ hk₂ _).1 h₂⟩`. Set `V : X.Opens` to `⟨(ι ≫ G.hom) '' Scheme.basicOpen _ ((u j).f k), (ι ≫ G.hom).isOpenMap _ (Scheme.basicOpen _ ((u j).f k)).isOpen⟩`.

Establish `hr : G.hom ⁻¹ᵁ V ≤ ι.opensRange`. Introduce and unpack `g ⟨y, -, e⟩`. Take `⟨q, hq, -⟩` from `Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback G.hom hU.fromSpec) g (f y) (e.symm.trans (congrArg (fun r : pullback G.hom hU.fromSpec ⟶ X => r y) pullback.condition))`. Conclude with `⟨q, hq⟩`. Take `⟨θ, hθ, hb⟩` from `ThetaLocal.exists_secOn_push hL hM (lbIso_refl hM) hr le_top (SecSpread.res_mem_secOn (u j) ⊤)`.

Use `⟨V, ⟨π z, hj, ?_⟩, θ, hθ, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Category.assoc, hπ, hφ.w, Scheme.Hom.comp_apply, hz] show X.fromSpecStalk x (spMap ψ (IsLocalRing.closedPoint R)) = x`. Establish `hc : spMap ψ (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint _` using `IsLocalRing.comap_closedPoint ψ`. Rewrite using `[hc]`. Conclude with `Scheme.fromSpecStalk_closedPoint`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨i', hi'⟩` from `exists_chart hL (ι y)`. Conclude with `⟨ι y, i', rfl, hb y ⟨y, hy, rfl⟩ i' k hi' ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, Scheme.basicOpen_le _ _ hy⟩, hy⟩)⟩`.
-/
theorem exists_theta_of_flat {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsSemiAbelian G) {L : LB G.left}
    (hL : L.IsLB) (x : X) {R : Type} [CommRing R] [IsLocalRing R] (ψ : X.presheaf.stalk x →+* R) (hψ : ψ.Flat)
    [IsLocalHom ψ] {G' : Over (Sp R)} {φ : G'.left ⟶ G.left}
    (hφ : IsPullback φ G'.hom G.hom (spMap ψ ≫ X.fromSpecStalk x)) {L' : LB G'.left} (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hθ : LN.ThetaNZ G' L') :
    ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i) := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let ι := pullback.fst G.hom hU.fromSpec
  let f := pullback.snd G.hom hU.fromSpec
  let gm : Γ(X, U) →+* R := ψ.comp (X.presheaf.germ U x hx).hom
  have hξ : spMap gm ≫ hU.fromSpec = spMap ψ ≫ X.fromSpecStalk x := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    show Spec.map (CommRingCat.ofHom (X.presheaf.germ U x hx).hom ≫ CommRingCat.ofHom ψ) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    rfl
  let π : G'.left ⟶ pullback G.hom hU.fromSpec := pullback.lift φ (G'.hom ≫ spMap gm)
    (by rw [Category.assoc, hξ, hφ.w])
  have hπ : π ≫ ι = φ := pullback.lift_fst _ _ _
  have hP : IsPullback π G'.hom f (spMap gm) :=
    IsPullback.of_right (by rw [hπ, hξ]; exact hφ) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have : CompactSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace (pullback G.hom hU.fromSpec : Scheme.{0}) := quasiSeparatedSpace_of_quasiSeparated f
  have hflat : gm.Flat := by
    have h₀ : (X.presheaf.germ U x hx).hom.Flat := by
      letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
      have := hU.isLocalization_stalk ⟨x, hx⟩
      exact RingHom.flat_algebraMap_iff.2
        (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    exact RingHom.Flat.comp h₀ hψ
  have hM := pull_isLB hL ι
  obtain ⟨w, hw'⟩ : LBIso ((L.pull ι).pull π) (L'.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullLinComb L ι (fun _ : PUnit => π) (fun _ => φ) (fun _ => 1) (𝟙 _)
      fun _ => hπ.trans (Category.id_comp _).symm) (Geo.Tor.chartPullPull L' _ _ rfl) hw.symm
  obtain ⟨θ', hθ'⟩ := hθ
  obtain ⟨σ, hσ⟩ := ThetaLocal.exists_sec_pull hL' (pull_isLB hM π) (𝟙 _) w hw' (O := ⊤) le_top _
    (SecSpread.res_mem_secOn θ' ⊤)
  obtain ⟨z, i, hz, hi⟩ := hθ' (IsLocalRing.closedPoint _)
  obtain ⟨k, hk⟩ := hσ z i ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, G'.left.basicOpen_le _ hi⟩, hi⟩)
  obtain ⟨k, rfl⟩ : ∃ j, k = fun _ => j := ⟨k PUnit.unit, rfl⟩
  have hk₁ := G'.left.basicOpen_le _ hk
  have hk₂ : π z ∈ (L.pull ι).U k := mem_pull.1 hk₁
  obtain ⟨n, a, u, hu⟩ := FlatSec.exists_comb_of_flat _ _ gm hflat _ f _ π G'.hom hP _ hM σ
  obtain ⟨j, hj⟩ : ∃ j, π z ∈ Scheme.basicOpen _ ((u j).f k) := by
    by_contra hn
    have h₁ := (AbLocusPull.isUnit_gs_iff (𝟙 _) z _ hk₁ _).2 hk
    rw [hu z k hk₂] at h₁
    refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_) h₁
    exact fun h₂ => hn ⟨j, (AbLocusPull.isUnit_gs_iff π z _ hk₂ _).1 h₂⟩
  let V : X.Opens := ⟨(ι ≫ G.hom) '' Scheme.basicOpen _ ((u j).f k),
    (ι ≫ G.hom).isOpenMap _ (Scheme.basicOpen _ ((u j).f k)).isOpen⟩
  have hr : G.hom ⁻¹ᵁ V ≤ ι.opensRange := by
    rintro g ⟨y, -, e⟩
    obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback G.hom hU.fromSpec) g (f y)
      (e.symm.trans (congrArg (fun r : pullback G.hom hU.fromSpec ⟶ X => r y) pullback.condition))
    exact ⟨q, hq⟩
  obtain ⟨θ, hθ, hb⟩ := ThetaLocal.exists_secOn_push hL hM (lbIso_refl hM) hr le_top
    (SecSpread.res_mem_secOn (u j) ⊤)
  refine ⟨V, ⟨π z, hj, ?_⟩, θ, hθ, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hπ, hφ.w, Scheme.Hom.comp_apply, hz]
    show X.fromSpecStalk x (spMap ψ (IsLocalRing.closedPoint R)) = x
    have hc : spMap ψ (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint ψ
    rw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i', hi'⟩ := exists_chart hL (ι y)
    exact ⟨ι y, i', rfl, hb y ⟨y, hy, rfl⟩ i' k hi'
      ((ThetaLocal.mem_basicOpen_resG _ _ _).2 ⟨⟨trivial, Scheme.basicOpen_le _ _ hy⟩, hy⟩)⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw _ l Xo c Y hsm x`. Establish `: Smooth Y.s` using `SmoothOfRelativeDimension.smooth Dw.dim _`. Use `haveI hAr : IsRegularRing (Y.X.presheaf.stalk x) := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth c.F Y.s x`. Use `haveI : IsRegularLocalRing (Y.X.presheaf.stalk x) := IsRegularLocalRing.of_isRegularRing_of_isLocalRing _`. Use `haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) := RegularCompletion.isRegularLocalRing_adicCompletion _`.

Take `⟨hdC, hnC⟩` from `isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))`. Use `haveI hκ : CharZero (Y.X.residueField x) := by`. Set `φ : c.F →+* Y.X.residueField x` to `(Y.X.evaluation ⊤ x trivial).hom.comp (GlobalTheory.QCoh.structureRingHom Y.s)`. Conclude with `charZero_of_injective_ringHom φ.injective`. Take `⟨k, _, _, hk, S', hS'⟩` from `CoveringCompare.exists_finite_splitOver Y.t.G Y.t.semi x`.

Use `haveI : Algebra.IsSeparable (Y.X.residueField x) k := inferInstance`. Take `⟨R, _, _, _, _, j, _, _, hj⟩` from `LocM.Bdy.exists_etale_local (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (Y.X.residueField x) k (ResidueField.map (algebraMap (Y.X.presheaf.stalk x) (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))`. Establish `: IsLocalization.AtPrime R (maximalIdeal R)` using `IsLocalization.self fun a ha => by_contra fun h => ha h`. Take `⟨hd, hn⟩` from `isDomain_and_isIntegrallyClosed_atPrime_of_etale (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (maximalIdeal R) R`. Establish `hNR : IsNoetherianRing R` using `IsNoetherianRing.of_finite (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R`.

Establish `hc` using `CompleteFiniteExtension.isAdicComplete_of_finite_local (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R`. Establish `f₁` using `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.X.presheaf.stalk x) (B := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))`. Establish `f₂` using `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (B := R)`. Set `ψ : Y.X.presheaf.stalk x →+* R` to `(algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R).comp (algebraMap (Y.X.presheaf.stalk x) (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)))`. Establish `hinj : Function.Injective ψ` using `(FaithfulSMul.algebraMap_injective _ _).comp (FaithfulSMul.algebraMap_injective _ _)`.

Use `haveI : CharZero (ResidueField (Y.X.presheaf.stalk x)) := hκ`. Use `haveI : CharZero (Y.X.presheaf.stalk x) := RingHom.charZero (residue (Y.X.presheaf.stalk x))`. Use `haveI : CharZero R := charZero_of_injective_ringHom hinj`. Establish `hadm` using `isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hNR hn hc`. Establish `hψf : ψ.Flat` using `RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) (RingHom.flat_algebraMap_iff.2 inferInstance)`.

Use `haveI : IsLocalHom ψ := inferInstance`. Take `⟨t, ⟨m⟩⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab (spMap ψ ≫ Y.X.fromSpecStalk x) Y.t`. Use `haveI : IsProper Y.s := ProperFamily.isProper_of_isProjOver Y.proj`. Use `haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s`. Use `haveI : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s`.

Use `haveI : IsNoetherian Y.X := {}`. Establish `hjo` using `GenFan.Tri.isOpenImmersion_j_id Y`. Establish `hopen : IsOpen (Set.range Y.j)` using `Y.j.isOpenEmbedding.isOpen_range`. Establish `hdense : Dense (Set.range Y.j)`. Establish `: IsIso (pullback.fst Y.s (spMap (RingHom.id c.F)))`.

Establish `: IsIso (spMap (RingHom.id c.F))` using `by show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))`. Rewrite using `[show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]`. Use `infer_instance`. Use `infer_instance`. Establish `e : Set.range Y.j = (pullback.fst Y.s (spMap (RingHom.id c.F))) '' Set.range Y.jQ`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Conclude with `⟨Y.jQ w, ⟨w, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Introduce and unpack `⟨_, ⟨w, rfl⟩, rfl⟩`.

Conclude with `⟨w, Scheme.Hom.comp_apply _ _ _⟩`. Rewrite using `[e]`. Conclude with `((pullback.fst Y.s (spMap (RingHom.id c.F))).surjective.denseRange).dense_image (pullback.fst Y.s (spMap (RingHom.id c.F))).continuous Y.jQ_dense`. Set `ξ : Sp R` to `(⊥ : PrimeSpectrum R)`. Establish `hgen : (spMap ψ ≫ Y.X.fromSpecStalk x) ξ ∈ Set.range Y.j` using `LocM.SharedLaws.mem_of_maximal (fun y hy => LocM.Bdy.generic_image x ψ hinj ξ rfl y hy) hopen hdense`.

Establish `hr : Set.range (jK R ≫ spMap ψ ≫ Y.X.fromSpecStalk x) ⊆ Set.range Y.j`. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `LN.GenericPoint.jK_mem (U := (spMap ψ ≫ Y.X.fromSpecStalk x) ⁻¹' Set.range Y.j) (hopen.preimage (Scheme.Hom.continuous _)) ⟨ξ, hgen⟩ q`. Establish `hpol : LN.PolAt t (jK R)` using `GoodTrait.polAt_of_point Y m (jK R) (IsOpenImmersion.lift Y.j _ hr) (IsOpenImmersion.lift_fac _ _ _)`.

Establish `h₁` using `LocM.Bdy.residue_comp (R := R) x`. Establish `e : spMap (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R) ≫ fromSpecCompletedStalk Y.X x = spMap ψ ≫ Y.X.fromSpecStalk x`. Rewrite using `[spMap_comp, Category.assoc]`. Both sides reduce to the same expression. Establish `h₂ : spMap j ≫ spMap (algebraMap (Y.X.residueField x) k) = spMap ((ResidueField.map (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R)).comp (ResidueField.map (algebraMap (Y.X.presheaf.stalk x) (AdicCompletion (maximalIdeal (Y.X.presheaf. …` using `(spMap_comp _ _).symm.trans (congrArg spMap hj)`.

Take `⟨S₁, hS₁⟩` from `LocM.Bdy.split_pull _ hS' j (ι := spMap ψ ≫ Y.X.fromSpecStalk x) (by`. Rewrite using `[← Category.assoc]`. Use `(congrArg (· ≫ Y.X.fromSpecResidueField x) h₂).trans ?_` and prove the remaining obligations. Conclude with `h₁.trans (congrArg (spMap (residue R) ≫ ·) e)) m`. Establish `hsplit : LN.SplitOver t.G (maximalIdeal R)` using `⟨S₁, hS₁⟩`.

Establish `hθ` using `thetaNZ_of_polAt E H R hadm t hpol hsplit`. Conclude with `exists_theta_of_flat Y.t.semi Y.t.PP.isLB x ψ hψf m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1) hθ`.
-/
theorem hasTheta_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := by
  intro E _ _ _ H Dw _ l Xo c Y hsm x
  have : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  haveI hAr : IsRegularRing (Y.X.presheaf.stalk x) :=
    ExtendRig.isRegularRing_stalk isRegularRing_of_smooth c.F Y.s x
  haveI : IsRegularLocalRing (Y.X.presheaf.stalk x) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) :=
    RegularCompletion.isRegularLocalRing_adicCompletion _
  obtain ⟨hdC, hnC⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))

  haveI hκ : CharZero (Y.X.residueField x) := by
    let φ : c.F →+* Y.X.residueField x := (Y.X.evaluation ⊤ x trivial).hom.comp (GlobalTheory.QCoh.structureRingHom Y.s)
    exact charZero_of_injective_ringHom φ.injective
  obtain ⟨k, _, _, hk, S', hS'⟩ := CoveringCompare.exists_finite_splitOver Y.t.G Y.t.semi x

  haveI : Algebra.IsSeparable (Y.X.residueField x) k := inferInstance
  obtain ⟨R, _, _, _, _, j, _, _, hj⟩ := LocM.Bdy.exists_etale_local
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (Y.X.residueField x) k
    (ResidueField.map (algebraMap (Y.X.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))
  have : IsLocalization.AtPrime R (maximalIdeal R) :=
    IsLocalization.self fun a ha => by_contra fun h => ha h
  obtain ⟨hd, hn⟩ := isDomain_and_isIntegrallyClosed_atPrime_of_etale
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (maximalIdeal R) R
  have hNR : IsNoetherianRing R :=
    IsNoetherianRing.of_finite (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local
    (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R
  have f₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.X.presheaf.stalk x)
    (B := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))
  have f₂ := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) (B := R)
  let ψ : Y.X.presheaf.stalk x →+* R := (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x))
    (Y.X.presheaf.stalk x)) R).comp (algebraMap (Y.X.presheaf.stalk x) (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)))
  have hinj : Function.Injective ψ :=
    (FaithfulSMul.algebraMap_injective _ _).comp (FaithfulSMul.algebraMap_injective _ _)
  haveI : CharZero (ResidueField (Y.X.presheaf.stalk x)) := hκ
  haveI : CharZero (Y.X.presheaf.stalk x) := RingHom.charZero (residue (Y.X.presheaf.stalk x))
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hadm := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hNR hn hc
  have hψf : ψ.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : IsLocalHom ψ := inferInstance

  obtain ⟨t, ⟨m⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sab (spMap ψ ≫ Y.X.fromSpecStalk x) Y.t
  haveI : IsProper Y.s := ProperFamily.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  haveI : IsNoetherian Y.X := {}
  have hjo := GenFan.Tri.isOpenImmersion_j_id Y
  have hopen : IsOpen (Set.range Y.j) := Y.j.isOpenEmbedding.isOpen_range
  have hdense : Dense (Set.range Y.j) := by
    have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
      have : IsIso (spMap (RingHom.id c.F)) := by
        show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
        rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
        infer_instance
      infer_instance
    have e : Set.range Y.j = (pullback.fst Y.s (spMap (RingHom.id c.F))) '' Set.range Y.jQ := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨Y.jQ w, ⟨w, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        exact ⟨w, Scheme.Hom.comp_apply _ _ _⟩
    rw [e]
    exact ((pullback.fst Y.s (spMap (RingHom.id c.F))).surjective.denseRange).dense_image
      (pullback.fst Y.s (spMap (RingHom.id c.F))).continuous Y.jQ_dense
  let ξ : Sp R := (⊥ : PrimeSpectrum R)
  have hgen : (spMap ψ ≫ Y.X.fromSpecStalk x) ξ ∈ Set.range Y.j :=
    LocM.SharedLaws.mem_of_maximal (fun y hy => LocM.Bdy.generic_image x ψ hinj ξ rfl y hy) hopen hdense
  have hr : Set.range (jK R ≫ spMap ψ ≫ Y.X.fromSpecStalk x) ⊆ Set.range Y.j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact LN.GenericPoint.jK_mem (U := (spMap ψ ≫ Y.X.fromSpecStalk x) ⁻¹' Set.range Y.j)
      (hopen.preimage (Scheme.Hom.continuous _)) ⟨ξ, hgen⟩ q
  have hpol : LN.PolAt t (jK R) :=
    GoodTrait.polAt_of_point Y m (jK R) (IsOpenImmersion.lift Y.j _ hr) (IsOpenImmersion.lift_fac _ _ _)
  have h₁ := LocM.Bdy.residue_comp (R := R) x
  have e : spMap (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x)) R) ≫
      fromSpecCompletedStalk Y.X x = spMap ψ ≫ Y.X.fromSpecStalk x := by
    rw [spMap_comp, Category.assoc]; rfl
  have h₂ : spMap j ≫ spMap (algebraMap (Y.X.residueField x) k) =
      spMap ((ResidueField.map (algebraMap (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x))
        (Y.X.presheaf.stalk x)) R)).comp (ResidueField.map (algebraMap (Y.X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (Y.X.presheaf.stalk x)) (Y.X.presheaf.stalk x))))) :=
    (spMap_comp _ _).symm.trans (congrArg spMap hj)
  obtain ⟨S₁, hS₁⟩ := LocM.Bdy.split_pull _ hS' j (ι := spMap ψ ≫ Y.X.fromSpecStalk x) (by
    rw [← Category.assoc]
    refine (congrArg (· ≫ Y.X.fromSpecResidueField x) h₂).trans ?_
    exact h₁.trans (congrArg (spMap (residue R) ≫ ·) e)) m
  have hsplit : LN.SplitOver t.G (maximalIdeal R) := ⟨S₁, hS₁⟩
  have hθ := thetaNZ_of_polAt E H R hadm t hpol hsplit
  exact exists_theta_of_flat Y.t.semi Y.t.PP.isLB x ψ hψf m.cart.1 t.PP.isLB (m.lin.imp fun _ h => h.1) hθ

end GlobalTheory.ThetaNormal
