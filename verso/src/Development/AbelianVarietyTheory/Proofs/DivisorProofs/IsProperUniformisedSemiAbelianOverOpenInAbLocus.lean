import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusIsOpenOfOpenImmersionCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfChartPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsEllipticCurveTwoAdic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnifProperOpen

/- English proof (translation)
Introduce `V _ _ _ hV A G _ _ hG φ hφ hab`. Use `haveI := hV.1`. Use `haveI := hV.2.2`. Take `⟨l₁, l₂, -⟩` from `GlobalTheory.firstFiveLaws`. Take `⟨e, he, -⟩` from `grpPullback_iso (isGrpPullback_pullback G (jK V)) hφ`.

Take `⟨L, hL⟩` from `GlobalTheory.UU.polarisation_extends l₁ V A G hG e he`. Take `⟨P, rfl⟩` from `GlobalTheory.CubicalPackage.exists_package l₁ V hV A G hG e he L hL`. Take `⟨w, hw⟩` from `hL`. Establish `hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal`. Rewrite using `[zero_add, pow_one]`.

Use `infer_instance`. Establish `hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1))` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax`. Establish `p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))`. Use `letI := hF.toField`. Conclude with `(default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))`.

Establish `h0 : IsAbelianScheme (thickObj V (maximalIdeal V) 0 G)`. Establish `h₂` using `IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG`. Use `letI := hF.toField`. Conclude with `⟨h₂.comm, h₂.smooth, GlobalTheory.ArcNotAbelian.isProper_fibre G hG _ _ p (hab _), h₂.geomConnected⟩`. Take `⟨P₀, h₀⟩` from `GlobalTheory.UU.exists_isLevelCP (maximalIdeal V) 0 P`.

Set `s : GlobalTheory.UU.HidaSetting V A G` to `⟨hV, hG, e, he, P, w, hw, PUnit, GlobalTheory.UU.TQ.abelian _ h0 PUnit, P₀, h₀, GlobalTheory.UU.SettingConsistentExample.ab_even h0 PUnit P₀⟩`. Take `⟨D, U, -, -, -⟩` from `GlobalTheory.uniformisation_dvr_unconditional V A G s`. Set `g` to `U.gt 0`. Establish `: Mono g.i` using `⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩`. Establish `hs` using `GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus G hG _ hF (thick V (maximalIdeal V) 0) p (hab _) D.toPre.X g.i g.i_hom`.

Conclude with `(GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hV.2.1 D A G hG U hs).proper`.
-/
theorem isProper_of_polGeneric_of_abLocus : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.UU.CDVR V →
    ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ φ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) φ → (∀ x, x ∈ abLocus G) → IsProper G.hom := by
  intro V _ _ _ hV A G _ _ hG φ hφ hab
  haveI := hV.1
  haveI := hV.2.2
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hφ
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends l₁ V A G hG e he
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package l₁ V hV A G hG e he L hL
  obtain ⟨w, hw⟩ := hL
  have hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))
  have h0 : IsAbelianScheme (thickObj V (maximalIdeal V) 0 G) := by
    have h₂ := IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG
    letI := hF.toField
    exact ⟨h₂.comm, h₂.smooth, GlobalTheory.ArcNotAbelian.isProper_fibre G hG _ _ p (hab _), h₂.geomConnected⟩
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V) 0 P
  let s : GlobalTheory.UU.HidaSetting V A G := ⟨hV, hG, e, he, P, w, hw, PUnit, GlobalTheory.UU.TQ.abelian _ h0 PUnit, P₀, h₀,
    GlobalTheory.UU.SettingConsistentExample.ab_even h0 PUnit P₀⟩
  obtain ⟨D, U, -, -, -⟩ := GlobalTheory.uniformisation_dvr_unconditional V A G s
  let g := U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus G hG _ hF (thick V (maximalIdeal V) 0) p (hab _)
    D.toPre.X g.i g.i_hom
  exact (GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hV.2.1 D A G hG U hs).proper

/- English proof (translation)
Introduce `R _ _ A G _ gen hgen V _ _ φ hφ`. Establish `hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ)` using `(IsFractionRing.injective V (FractionRing V)).comp hφ`. Set `ψ : FractionRing R →+* FractionRing V` to `IsFractionRing.lift hinj'`. Establish `hg : spMap ψ ≫ jK R = jK V ≫ spMap φ`. Simplify using `only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use extensionality with `r`. Simplify using `[ψ, IsFractionRing.lift_algebraMap]`. Take `⟨A', eA, heA, -⟩` from `GlobalTheory.GoodReductionUnif.exists_baseChange GlobalTheory.polBaseChange_holds (spMap ψ) A`. Establish `h₁` using `GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (spMap ψ) A.A eA heA`.

Establish `h₂` using `GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G gen hgen`. Establish `h₃` using `h₁.comp h₂`. Use `⟨A', pullback.lift ((eA.inv.left ≫ pullback.fst A.A.hom (spMap ψ)) ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)) (A'.A.hom ≫ jK V) (by rw [h₃.1.w, hg, Category.assoc]), ?_⟩` and prove the remaining obligations. Conclude with `(isGrpPullback_pullback G (spMap φ)).cancel (h₃.congr hg (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)`.
-/
theorem exists_polGeneric_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
    (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V),
    Function.Injective φ → ∃ (A' : PolAV (Sp (FractionRing V))) (ψ : A'.A.left ⟶ ((Over.pullback (spMap φ)).obj G).left),
    IsGrpPullback A'.A ((Over.pullback (spMap φ)).obj G) (jK V) ψ := by
  intro R _ _ A G _ gen hgen V _ _ φ hφ
  have hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hφ
  let ψ : FractionRing R →+* FractionRing V := IsFractionRing.lift hinj'
  have hg : spMap ψ ≫ jK R = jK V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [ψ, IsFractionRing.lift_algebraMap]
  obtain ⟨A', eA, heA, -⟩ := GlobalTheory.GoodReductionUnif.exists_baseChange GlobalTheory.polBaseChange_holds (spMap ψ) A
  have h₁ := GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (spMap ψ) A.A eA heA
  have h₂ := GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G gen hgen
  have h₃ := h₁.comp h₂
  refine ⟨A', pullback.lift ((eA.inv.left ≫ pullback.fst A.A.hom (spMap ψ)) ≫ gen.inv.left ≫
    pullback.fst G.hom (jK R)) (A'.A.hom ≫ jK V) (by rw [h₃.1.w, hg, Category.assoc]), ?_⟩
  exact (isGrpPullback_pullback G (spMap φ)).cancel (h₃.congr hg (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)

/- English proof (translation)
Establish `e : ⇑(spMap (algebraMap R (Localization.Away f))) = PrimeSpectrum.comap (algebraMap R (Localization.Away f))`. Use extensionality with `x : 1`. Simplify using `[spMap, Spec.map_base]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `PrimeSpectrum.localization_away_comap_range _ f`.
-/
theorem range_spMap_away (R : Type) [CommRing R] (f : R) :
    Set.range (spMap (algebraMap R (Localization.Away f))) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  have e : ⇑(spMap (algebraMap R (Localization.Away f))) = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) := by
    ext x : 1
    simp [spMap, Spec.map_base]
    rfl
  rw [e]
  exact PrimeSpectrum.localization_away_comap_range _ f

/- English proof (translation)
Use `haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)`. Use `haveI : IsNoetherianRing (Localization.Away f) := IsLocalization.isNoetherianRing (Submonoid.powers f) _ inferInstance`. Use `set j := spMap (algebraMap R (Localization.Away f)) with hj`. Set `Gf` to `(Over.pullback j).obj G`. Use `haveI hGf : IsSemiAbelian Gf := IsSemiAbelian.pullback j G hG`.

Use `haveI := hGf.separated`. Use `haveI := hGf.quasiCompact`. Use `haveI := hGf.smooth`. Use `haveI : IsIntegral Gf.left := GlobalTheory.isIntegral_left_of_isSemiAbelian Gf`. Express the relevant statement in the definitionally equal form `IsProper Gf.hom`.

Use `GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint (Localization.Away f) Gf.left Gf.hom ?_` and prove the remaining obligations. Introduce `V K _ _ _ _ _ _ _ x y hx hxy`. Take `⟨φ, hφ⟩ : ∃ φ : R →+* V, spMap φ = y ≫ j` from `⟨(Spec.preimage (y ≫ j)).hom, by simp [spMap]⟩`. Set `p₀ : Sp K` to `(⊥ : PrimeSpectrum K)`. Establish `h₁ : x p₀ = genericPoint Gf.left` using `hx ⟨p₀, rfl⟩`.

Establish `h₂ : (x ≫ Gf.hom ≫ j) p₀ = (⊥ : PrimeSpectrum R)`. Rewrite using `[Scheme.Hom.comp_apply, h₁, GlobalTheory.ProperOfAbelianFibres.apply_genericPoint_of_flat]`. Conclude with `genericPoint_eq_bot_of_affine (CommRingCat.of R)`. Rewrite `h₂` using `[← Category.assoc, hxy, Category.assoc, ← hφ]`. Establish `h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥` using `congrArg PrimeSpectrum.asIdeal h₂`.

Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `: a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K))` using `by simp [ha]`. Rewrite `this` using `[h₃]`.

Simplify using `using this`. Use `haveI : CharZero V := charZero_of_injective_ringHom hinj`. Set `GV` to `(Over.pullback (spMap φ)).obj G`. Establish `hGV : IsSemiAbelian GV` using `IsSemiAbelian.pullback (spMap φ) G hG`. Establish `habV : ∀ z, z ∈ abLocus GV` using `fun z => (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (spMap φ)) z).1 (hab _ ⟨y z, by rw [hφ, Scheme.Hom.comp_apply]⟩)`.

Take `⟨A', ψ, hψ⟩` from `exists_polGeneric_pullback R A G gen hgen V φ hinj`. Establish `hpV : IsProper GV.hom` using `isProper_of_polGeneric_of_abLocus V ⟨inferInstance, inferInstance, inferInstance⟩ A' GV hGV ψ hψ habV`. Set `xV : Sp K ⟶ GV.left` to `pullback.lift (x ≫ pullback.fst G.hom j) (spMap (algebraMap V K)) (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Use `erw [hxy]`.

Rewrite using `[Category.assoc, hφ])`. Establish `hE : ValuativeCriterion.Existence GV.hom`. Establish `h : UniversallyClosed GV.hom` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.

Set `S : ValuativeCommSq GV.hom` to `{ R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩ }`. Take `⟨l⟩` from `(hE S).exists_lift`. Establish `e₁ : spMap (algebraMap V K) ≫ l.l = xV` using `l.fac_left`. Establish `e₂ : l.l ≫ GV.hom = 𝟙 _` using `l.fac_right`. Use `⟨pullback.lift (l.l ≫ pullback.fst G.hom (spMap φ)) y ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc] erw [e₂]`. Rewrite using `[Category.id_comp, hφ]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.lift_fst, ← Category.assoc, e₁]`. Conclude with `pullback.lift_fst _ _ _`.

Rewrite using `[Category.assoc, pullback.lift_snd]`. Conclude with `hxy.symm`.
-/
theorem isProper_away (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R]
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) (hgen : IsMonHom gen.hom) (f : R) (hf : f ≠ 0)
    (hab : ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ abLocus G) :
    IsProper (pullback.snd G.hom (spMap (algebraMap R (Localization.Away f)))) := by
  haveI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : IsNoetherianRing (Localization.Away f) := IsLocalization.isNoetherianRing (Submonoid.powers f) _ inferInstance
  set j := spMap (algebraMap R (Localization.Away f)) with hj
  let Gf := (Over.pullback j).obj G
  haveI hGf : IsSemiAbelian Gf := IsSemiAbelian.pullback j G hG
  haveI := hGf.separated
  haveI := hGf.quasiCompact
  haveI := hGf.smooth
  haveI : IsIntegral Gf.left := GlobalTheory.isIntegral_left_of_isSemiAbelian Gf
  change IsProper Gf.hom
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint (Localization.Away f) Gf.left Gf.hom ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+* V, spMap φ = y ≫ j := ⟨(Spec.preimage (y ≫ j)).hom, by simp [spMap]⟩
  let p₀ : Sp K := (⊥ : PrimeSpectrum K)
  have h₁ : x p₀ = genericPoint Gf.left := hx ⟨p₀, rfl⟩
  have h₂ : (x ≫ Gf.hom ≫ j) p₀ = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, h₁, GlobalTheory.ProperOfAbelianFibres.apply_genericPoint_of_flat]
    exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
  rw [← Category.assoc, hxy, Category.assoc, ← hφ] at h₂
  have h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥ := congrArg PrimeSpectrum.asIdeal h₂
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) := by simp [ha]
    rw [h₃] at this
    simpa using this
  haveI : CharZero V := charZero_of_injective_ringHom hinj
  let GV := (Over.pullback (spMap φ)).obj G
  have hGV : IsSemiAbelian GV := IsSemiAbelian.pullback (spMap φ) G hG
  have habV : ∀ z, z ∈ abLocus GV := fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (spMap φ)) z).1
      (hab _ ⟨y z, by rw [hφ, Scheme.Hom.comp_apply]⟩)
  obtain ⟨A', ψ, hψ⟩ := exists_polGeneric_pullback R A G gen hgen V φ hinj
  have hpV : IsProper GV.hom := isProper_of_polGeneric_of_abLocus V ⟨inferInstance, inferInstance, inferInstance⟩ A' GV hGV ψ hψ habV
  let xV : Sp K ⟶ GV.left := pullback.lift (x ≫ pullback.fst G.hom j) (spMap (algebraMap V K)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hxy]
    rw [Category.assoc, hφ])
  have hE : ValuativeCriterion.Existence GV.hom := by
    have h : UniversallyClosed GV.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq GV.hom :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  have e₁ : spMap (algebraMap V K) ≫ l.l = xV := l.fac_left
  have e₂ : l.l ≫ GV.hom = 𝟙 _ := l.fac_right
  refine ⟨pullback.lift (l.l ≫ pullback.fst G.hom (spMap φ)) y ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [e₂]
    rw [Category.id_comp, hφ]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, e₁]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, pullback.lift_snd]
      exact hxy.symm

/- English proof (translation)
Introduce `R _ _ _ hR D A G _ _ hG U W hW`. Take `⟨⟨hN, -, -, -⟩, hc⟩` from `hR`. Use `haveI := hN`. Use `haveI := hc`. Set `I` to `{f : R // f ≠ 0 ∧ ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ W}`.

Use `GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom (I := I) (fun i => spMap (algebraMap R (Localization.Away i.1))) (fun i => pullback.snd G.hom _) (fun i => pullback.fst G.hom _) (fun i => IsPullback.of_hasPullback _ _) (fun _ => ⊤) (fun i => ?_) W (fun i => ?_) (fun z h …` and prove the remaining obligations. Conclude with `IsZariskiLocalAtTarget.restrict (isProper_away R A G hG U.gen U.gen_hom i.1 i.2.1 fun z hz => hW (i.2.2 z hz)) ⊤`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `i.2.2 _ ⟨_, rfl⟩`.

Take `⟨_, ⟨f, rfl⟩, hzf, hfW⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen`. Establish `hr` using `range_spMap_away R f`. Establish `hzf' : z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))` using `hzf`. Establish `hfW' : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ (W : Set (Sp R))` using `hfW`. Establish `hf : f ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hzf' (zero_mem _)`. Use `⟨⟨f, hf, fun z' hz' => hfW' (by rw [hr] at hz'; exact hz')⟩, ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩ : z ∈ Set.range (spMap (algebraMap R (Localization.Away f)))` from `by rw [hr]; exact hzf'`. Conclude with `⟨⟨a, trivial⟩, ha⟩`.
-/
theorem isProper_restrict : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G →
    IsProper (G.hom ∣_ W) := by
  intro R _ _ _ hR D A G _ _ hG U W hW
  obtain ⟨⟨hN, -, -, -⟩, hc⟩ := hR
  haveI := hN
  haveI := hc
  let I := {f : R // f ≠ 0 ∧ ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ W}
  refine GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom (I := I)
    (fun i => spMap (algebraMap R (Localization.Away i.1))) (fun i => pullback.snd G.hom _)
    (fun i => pullback.fst G.hom _) (fun i => IsPullback.of_hasPullback _ _) (fun _ => ⊤) (fun i => ?_) W
    (fun i => ?_) (fun z hz => ?_)
  · exact IsZariskiLocalAtTarget.restrict
      (isProper_away R A G hG U.gen U.gen_hom i.1 i.2.1 fun z hz => hW (i.2.2 z hz)) ⊤
  · rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact i.2.2 _ ⟨_, rfl⟩
  · obtain ⟨_, ⟨f, rfl⟩, hzf, hfW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen
    have hr := range_spMap_away R f
    have hzf' : z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hzf
    have hfW' : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ (W : Set (Sp R)) := hfW
    have hf : f ≠ 0 := by
      rintro rfl
      exact hzf' (zero_mem _)
    refine ⟨⟨f, hf, fun z' hz' => hfW' (by rw [hr] at hz'; exact hz')⟩, ?_⟩
    obtain ⟨a, ha⟩ : z ∈ Set.range (spMap (algebraMap R (Localization.Away f))) := by rw [hr]; exact hzf'
    exact ⟨⟨a, trivial⟩, ha⟩

end GlobalTheory.UnifProperOpen
