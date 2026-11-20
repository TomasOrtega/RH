import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameGenericProjectiveCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverOpenImmersionNormalisedThetaClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFirstFactorThetaModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliIntegralNormalLocallyNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantBundlePowEightIsoDetHodgePowFourStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemNormalLevelModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapEighthPowerSiegelModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveToricMinorModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverImageOpenFiniteOverModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeExtensionThroughFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaMapDeepLevelFiniteFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantPowEqUnitMulSymmetricFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaConstantsEqThetaMapCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalisationProjectiveQuasiFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOverProjectiveSpaceProjectiveAmpleTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralAnyBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResGInjectiveOfTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePowerIsoMinimalSiegelCompactification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegMinTop

/- English proof (translation)
Introduce `R o' _ _ _ β S' X Z s' z π i U c hs' hβ hz hc hUπ hi hπz`. Use `GlobalTheory.ProperFamily.isProper_of_isProjOver hs'` as an intermediate fact. Use `GlobalTheory.ProperFamily.isProper_of_isProjOver hz` as an intermediate fact. Use `haveI : IsFinite (spMap β) := (IsFinite.SpecMap_iff _).2 hβ`. Use `haveI : IsProper (π ≫ z) := by rw [hπz]; infer_instance`.

Use `haveI : IsProper π := IsProper.of_comp π z`. Use `⟨⟨?_⟩, inferInstance, ?_⟩` and prove the remaining obligations. Establish `hcl : IsClosed (Set.range π)` using `π.isClosedMap.isClosed_range`. Establish `hsub : Set.range i ⊆ Set.range π`. Introduce and unpack `_ ⟨x, rfl⟩`.

Take `⟨u, rfl⟩` from `c.surjective x`. Conclude with `⟨U.ι u, by rw [← Scheme.Hom.comp_apply, hUπ, Scheme.Hom.comp_apply]⟩`. Establish `h` using `hi.closure_eq ▸ closure_minimal hsub hcl`. Conclude with `fun y => h (Set.mem_univ y)`. Establish `: IsLocallyNoetherian Z` using `LocallyOfFiniteType.isLocallyNoetherian z`.

Establish `: CompactSpace Z` using `QuasiCompact.compactSpace_of_compactSpace z`. Conclude with `{}`.
-/
theorem lemProper : ∀ (R o' : Type) [CommRing R] [IsNoetherianRing R] [CommRing o'] (β : R →+* o') (S' X Z : Scheme.{0}) (s' : S' ⟶ Sp o') (z : Z ⟶ Sp R) (π : S' ⟶ Z) (i : X ⟶ Z) (U : S'.Opens) (c : U.toScheme ⟶ X), IsProjOver s' → β.Finite → IsProjOver z → Surjective c → U.ι ≫ π = c ≫ i → Dense (Set.range i) → π ≫ z = s' ≫ spMap β → Surjective π ∧ IsProper π ∧ AlgebraicGeometry.IsNoetherian Z := by
  intro R o' _ _ _ β S' X Z s' z π i U c hs' hβ hz hc hUπ hi hπz
  have := GlobalTheory.ProperFamily.isProper_of_isProjOver hs'
  have := GlobalTheory.ProperFamily.isProper_of_isProjOver hz
  haveI : IsFinite (spMap β) := (IsFinite.SpecMap_iff _).2 hβ
  haveI : IsProper (π ≫ z) := by rw [hπz]; infer_instance
  haveI : IsProper π := IsProper.of_comp π z
  refine ⟨⟨?_⟩, inferInstance, ?_⟩
  · have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hsub : Set.range i ⊆ Set.range π := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := c.surjective x
      exact ⟨U.ι u, by rw [← Scheme.Hom.comp_apply, hUπ, Scheme.Hom.comp_apply]⟩
    have h := hi.closure_eq ▸ closure_minimal hsub hcl
    exact fun y => h (Set.mem_univ y)
  · have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace z
    exact {}

/- English proof (translation)
Introduce `o Ω _ _ _ M U _`. Take `⟨⟨y₀, hy₀⟩⟩` from `‹Nonempty U›`. Establish `hsub : Set.range M.pt ⊆ Set.range U.ι`. Rewrite using `[M.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]`. Conclude with `(genericPoint_specializes y₀).mem_open U.isOpen hy₀`.

Establish `hg : U.ι (genericPoint U.toScheme) = genericPoint M.Z`. Establish `h1` using `(genericPoint_spec U.toScheme).image U.ι.continuous`. Rewrite `h1` using `[Set.image_univ, Scheme.Opens.range_ι, (U.isOpen.dense ⟨y₀, hy₀⟩).closure_eq]`. Conclude with `h1.eq (genericPoint_spec M.Z)`. Use `set x := IsOpenImmersion.lift U.ι M.pt hsub with hx`.

Establish `hxU : x ≫ U.ι = M.pt` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hxa : ∀ a, x a = genericPoint U.toScheme` using `fun a => by`. Apply `U.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[hg, ← M.pt_apply a, ← hxU, Scheme.Hom.comp_apply]`. Use `⟨x, hxU, Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint Ω, hxa _⟩, ?_⟩⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `hxa a`.
-/
theorem lemGen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens) [Nonempty U], ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt ∧ Set.range x = {genericPoint U.toScheme} := by
  intro o Ω _ _ _ M U _
  obtain ⟨⟨y₀, hy₀⟩⟩ := ‹Nonempty U›
  have hsub : Set.range M.pt ⊆ Set.range U.ι := by
    rw [M.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact (genericPoint_specializes y₀).mem_open U.isOpen hy₀
  have hg : U.ι (genericPoint U.toScheme) = genericPoint M.Z := by
    have h1 := (genericPoint_spec U.toScheme).image U.ι.continuous
    rw [Set.image_univ, Scheme.Opens.range_ι, (U.isOpen.dense ⟨y₀, hy₀⟩).closure_eq] at h1
    exact h1.eq (genericPoint_spec M.Z)
  set x := IsOpenImmersion.lift U.ι M.pt hsub with hx
  have hxU : x ≫ U.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxa : ∀ a, x a = genericPoint U.toScheme := fun a => by
    apply U.ι.isOpenEmbedding.injective
    rw [hg, ← M.pt_apply a, ← hxU, Scheme.Hom.comp_apply]
  refine ⟨x, hxU, Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint Ω, hxa _⟩, ?_⟩⟩
  rintro _ ⟨a, rfl⟩
  exact hxa a

/- English proof (translation)
Introduce `g hg n hn ho F`. Take `⟨ℓ, hℓ, hℓn⟩` from `Nat.exists_prime_and_dvd (show n ≠ 1 by omega)`. Establish `hℓo : Odd ℓ` using `Odd.of_dvd_nat ho hℓn`. Take `⟨W, hW, hbas⟩` from `GlobalTheory.ZM.exists_isE8_isSharpBasis`. Take `⟨hXi, hXn, -⟩` from `GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn ho F`.

Take `⟨P, rig, hPg, hPs, hrig, -⟩` from `GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli g n hg hn ho F W hW`. Take `⟨j₀, hj₀⟩` from `GlobalTheory.T.siegelThetaMap_deepLevel_finite_fibres ℓ hℓ hℓo g`. Establish `hmo : Odd (ℓ ^ (j₀ + 1))` using `hℓo.pow`. Establish `hm3 : 3 ≤ ℓ ^ (j₀ + 1)`. Establish `h2` using `hℓ.two_le`.

Establish `h1 : ℓ ≤ ℓ ^ (j₀ + 1)` using `Nat.le_self_pow (by omega) ℓ`. Take `⟨k, hk⟩` from `hℓo`. Use linear arithmetic over natural numbers and integers. Establish `hmu : IsUnit ((ℓ ^ (j₀ + 1) : ℕ) : cycAway n)`. Take `⟨k, hk⟩` from `hℓn`.

Establish `hu` using `isUnit_natCast (n := n) (by omega)`. Establish `e : ((n : ℕ) : cycAway n) = (ℓ : cycAway n) * (k : cycAway n)`. Rewrite using `[← Nat.cast_mul, ← hk]`. Rewrite `hu` using `[e]`. Rewrite using `[Nat.cast_pow]`.

Conclude with `(isUnit_of_mul_isUnit_left hu).pow _`. Take `⟨N, f, hf⟩` from `GlobalTheory.T.exists_thetaMap_eighthPower_siegelModuli g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) hPg hPs hrig hmo hm3 hmu`. Establish `hq : QFin f` using `hj₀ (j₀ + 1) (by omega) n hg hn ho F W hW hℓn P rig N f hf`. Use `haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n`. Use `haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n`.

Establish `hfs : f ≫ PSpace.str (cycAway n) N = F.s` using `hf.2.2.2.2.2.2.2.1`. Establish `hlft : LocallyOfFiniteType F.s` using `GlobalTheory.SiegUnram.locallyOfFiniteType_of_isQProjOver F.qproj`. Establish `hqc : QuasiCompact F.s` using `GlobalTheory.SiegelFamilyBaseChange.quasiCompact_of_isQProjOver F.qproj`. Take `⟨Z, p, i, hpf, hio, hip, hZn, hZi, hid⟩` from `GlobalTheory.T.exists_finite_normalisation_projective_quasiFinite (cycAway n) N F.X F.s f hXi hXn hlft hqc F.isSeparated hfs hq`. Take `⟨hzproj, hOZlb, hOZamp, -⟩` from `GlobalTheory.T.finite_over_projectiveSpace_projective_ample_twist (cycAway n) N 8 Z p (by norm_num) hpf`.

Take `⟨o, Ω, _, _, _, _, β, S, ρ, u, Y, q, hsys, hlev, hbig, hfin⟩` from `GlobalTheory.T.exists_realisedThetaSystem_normalLevelModel ℓ hℓ hℓo j₀ g n hg hn ho F W hW hℓn (hbas g)`. Take `⟨X, M, U₀, EE, fM, Xab, Zh, hmin, hab, habeq⟩` from `GlobalTheory.T.exists_normal_projective_toric_minor_model o Ω S ρ hbig hfin`. Establish `hXnm : X.IsNm S.th` using `hmin.1`. Establish `hXnorm : Geo.Tor.IsNormalScheme X.Z` using `hmin.2.2.1`. Establish `hover : S.Over₀ M U₀` using `hmin.2.2.2.1`.

Take `⟨d, hd, hdo⟩` from `GlobalTheory.T.levelCover_openImmersion_normalisedThetaClosure g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys hq Y X q hlev hXnm hXnorm`. Take `⟨U, c, hUc, -⟩` from `GlobalTheory.T.level_cover_image_open_finite_over_moduli g n hg hn ho F W hW o Ω β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin habeq hd hdo`. Take `⟨G, _, e, _, hGs, hGsm, hGpb, hGh⟩` from `GlobalTheory.T.eighth_power_first_factor_theta_model g n hg hn ho F W hW o Ω β S ρ u hsys M U₀ EE Zh U c hover hUc`. Take `⟨eS, hSymE, hcrd⟩` from `GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys`. Establish `hMn : Geo.Tor.IsNormalScheme M.Z` using `hover.normal`.

Establish `hscale` using `GlobalTheory.T.thetaConstant_pow_eq_unit_mul_symmetricFunction g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys M eS hMn hover.div hSymE`. Establish `hediv : M.HasDiv eS` using `fun z' => by`. Take `⟨i', hi'⟩` from `hover.div z'`. Take `⟨j', hj', -⟩` from `hscale z' i' hi'`. Conclude with `⟨j', hj'⟩`.

Take `⟨h, hhs, hhc⟩` from `GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor o Ω (cycAway n) β M N eS hediv`. Use `haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩`. Take `⟨δ, t, hδ, htop, -, hsec⟩` from `GlobalTheory.TupleBundle.exists_lb_of_hasDiv o Ω M S.Gam S.th hover.div`. Establish `hhb` using `GlobalTheory.T.pull_O1_section_coordinates_power o Ω (cycAway n) M S.Gam S.th δ t N (N + 1).factorial eS h hδ htop hsec hhc hscale`. Establish `hSg : S.g = 8 * g` using `hsys.2.2.1`.

Establish `hkey` using `GlobalTheory.T.thetaConstantBundle_pow_eight_iso_detHodge_pow_four o Ω S ρ M U₀ EE Zh (by omega) hover hab δ t hδ htop hsec`. Use `haveI : Nonempty U := ⟨⟨_, hUc.1.some_mem⟩⟩`. Take `⟨x, hxU, hxg⟩` from `lemGen o Ω M U`. Establish `hUh : U.ι ≫ h = c ≫ f` using `GlobalTheory.T.eq_of_same_generic_projective_coords (cycAway n) N U.toScheme (c ≫ F.s) (U.ι ≫ h) (c ≫ f) Ω x eS (by rw [Category.assoc, hhs, hUc.2.2.2.1]) (by rw [Category.assoc, hfs]) hxg (by rw [← Category.assoc, hxU]; exact hhc) (by rw [← Category.assoc, hUc.2.2.2.2 x hxU, Cat …`. Use `haveI : Surjective c := hUc.2.2.1`.

Establish `hUd : Dense (U : Set M.Z)` using `U.isOpen.dense hUc.1`. Take `⟨π, hπU, hπp⟩` from `GlobalTheory.T.normal_scheme_extension_through_finite_cover (cycAway n) N M.Z F.X Z U c i p h inferInstance hMn hZi hUd inferInstance hpf hio hid (by rw [hUh, hip])`. Establish `hss : π ≫ p ≫ PSpace.str (cycAway n) N = M.s ≫ spMap β` using `by rw [← Category.assoc, hπp, hhs]`. Take `⟨hπs, hπpr, hZno⟩` from `lemProper (cycAway n) o β M.Z F.X Z M.s (p ≫ PSpace.str (cycAway n) N) π i U c hover.proj hsys.1 hzproj hUc.2.2.1 hπU hid hss`. Establish `hTI : GlobalTheory.Poinc.ThetaInt F W i`.

Establish `h0` using `GlobalTheory.T.siegelThetaConstants_projectively_integral_anyBase g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf`. Rewrite `h0` using `[← hip]`. Introduce `o' Ω' _ _ _ _ S' ρ' u' hsh hgen M' π' hM' hpt`. Conclude with `h0 o' Ω' S' ρ' u' hsh hgen M' (π' ≫ p) hM' (by rw [← Category.assoc, hpt]; simp only [Category.assoc])`. Establish `hiz : i ≫ p ≫ PSpace.str (cycAway n) N = F.s` using `by rw [← Category.assoc, hip, hfs]`.

Use `haveI : IsSeparated G.hom := hGs.separated`. Use `haveI : IsSeparated Zh.G.hom := Zh.semi.separated`. Use `haveI := hGsm`. Use `haveI := Zh.dim`. Establish `hH2 : (hodge G g).IsLB` using `(GlobalTheory.LieVB.isVB_omega G g).isLB_det`.

Establish `hH1 : (hodge Zh.G S.g).IsLB` using `(GlobalTheory.LieVB.isVB_omega Zh.G S.g).isLB_det`. Establish `hO` using `GlobalTheory.ProjSpace.O1_isLB (cycAway n) N`. Establish `hLB : LBIso ((lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8).pull π) (lbPow (hodge G g) (32 * (N + 1).factorial))`. Establish `e1` using `(GlobalTheory.CechPic.cls_eq_iff (pull_isLB hO h) (isLB_lbPow hδ _)).2 hhb`. Establish `e2` using `(GlobalTheory.CechPic.cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hH1 4)).2 hkey`.

Establish `e3` using `(GlobalTheory.CechPic.cls_eq_iff hH1 (isLB_lbPow hH2 8)).2 hGh`. Rewrite `e1` using `[GlobalTheory.CechPic.cls_pull hO, GlobalTheory.CechPic.cls_lbPow hδ]`. Rewrite `e2` using `[GlobalTheory.CechPic.cls_lbPow hδ, GlobalTheory.CechPic.cls_lbPow hH1]`. Rewrite `e3` using `[GlobalTheory.CechPic.cls_lbPow hH2]`. Use `(GlobalTheory.CechPic.cls_eq_iff (pull_isLB hOZlb π) (isLB_lbPow hH2 _)).1 ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.CechPic.cls_pull hOZlb, GlobalTheory.CechPic.cls_lbPow (pull_isLB hO p), GlobalTheory.CechPic.cls_pull hO, GlobalTheory.CechPic.cls_lbPow hH2, map_nsmul, ← GlobalTheory.CechPic.pull_comp, hπp, e1, smul_comm 8, e2, e3, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Z, p ≫ PSpace.str (cycAway n) N, i, lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8, o, inferInstance, β, M.Z, M.s, U, c, π, G, inferInstance, e, inferInstance, 32 * (N + 1).factorial, ⟨⟨hzproj, GlobalTheory.IsNormalScheme.of_pred hZn, hio, hiz, hid, W, hW, hTI⟩, hzpr …` and prove the remaining obligations.
-/
theorem minSt5 : GlobalTheory.SiegJoin.MinSt5 := by
  intro g hg n hn ho F
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hℓo : Odd ℓ := Odd.of_dvd_nat ho hℓn
  obtain ⟨W, hW, hbas⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨hXi, hXn, -⟩ := GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn ho F
  obtain ⟨P, rig, hPg, hPs, hrig, -⟩ := GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli g n hg hn ho F W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.siegelThetaMap_deepLevel_finite_fibres ℓ hℓ hℓo g
  have hmo : Odd (ℓ ^ (j₀ + 1)) := hℓo.pow
  have hm3 : 3 ≤ ℓ ^ (j₀ + 1) := by
    have h2 := hℓ.two_le
    have h1 : ℓ ≤ ℓ ^ (j₀ + 1) := Nat.le_self_pow (by omega) ℓ
    obtain ⟨k, hk⟩ := hℓo
    omega
  have hmu : IsUnit ((ℓ ^ (j₀ + 1) : ℕ) : cycAway n) := by
    obtain ⟨k, hk⟩ := hℓn
    have hu := isUnit_natCast (n := n) (by omega)
    have e : ((n : ℕ) : cycAway n) = (ℓ : cycAway n) * (k : cycAway n) := by
      rw [← Nat.cast_mul, ← hk]
    rw [e] at hu
    rw [Nat.cast_pow]
    exact (isUnit_of_mul_isUnit_left hu).pow _
  obtain ⟨N, f, hf⟩ := GlobalTheory.T.exists_thetaMap_eighthPower_siegelModuli g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) hPg hPs hrig hmo hm3 hmu
  have hq : QFin f := hj₀ (j₀ + 1) (by omega) n hg hn ho F W hW hℓn P rig N f hf
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  have hfs : f ≫ PSpace.str (cycAway n) N = F.s := hf.2.2.2.2.2.2.2.1
  have hlft : LocallyOfFiniteType F.s := GlobalTheory.SiegUnram.locallyOfFiniteType_of_isQProjOver F.qproj
  have hqc : QuasiCompact F.s := GlobalTheory.SiegelFamilyBaseChange.quasiCompact_of_isQProjOver F.qproj
  obtain ⟨Z, p, i, hpf, hio, hip, hZn, hZi, hid⟩ :=
    GlobalTheory.T.exists_finite_normalisation_projective_quasiFinite (cycAway n) N F.X F.s f hXi hXn hlft hqc F.isSeparated hfs hq
  obtain ⟨hzproj, hOZlb, hOZamp, -⟩ := GlobalTheory.T.finite_over_projectiveSpace_projective_ample_twist (cycAway n) N 8 Z p (by norm_num) hpf
  obtain ⟨o, Ω, _, _, _, _, β, S, ρ, u, Y, q, hsys, hlev, hbig, hfin⟩ :=
    GlobalTheory.T.exists_realisedThetaSystem_normalLevelModel ℓ hℓ hℓo j₀ g n hg hn ho F W hW hℓn (hbas g)
  obtain ⟨X, M, U₀, EE, fM, Xab, Zh, hmin, hab, habeq⟩ := GlobalTheory.T.exists_normal_projective_toric_minor_model o Ω S ρ hbig hfin
  have hXnm : X.IsNm S.th := hmin.1
  have hXnorm : Geo.Tor.IsNormalScheme X.Z := hmin.2.2.1
  have hover : S.Over₀ M U₀ := hmin.2.2.2.1
  obtain ⟨d, hd, hdo⟩ :=
    GlobalTheory.T.levelCover_openImmersion_normalisedThetaClosure g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys hq Y X q hlev hXnm hXnorm
  obtain ⟨U, c, hUc, -⟩ :=
    GlobalTheory.T.level_cover_image_open_finite_over_moduli g n hg hn ho F W hW o Ω β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin habeq hd hdo
  obtain ⟨G, _, e, _, hGs, hGsm, hGpb, hGh⟩ :=
    GlobalTheory.T.eighth_power_first_factor_theta_model g n hg hn ho F W hW o Ω β S ρ u hsys M U₀ EE Zh U c hover hUc
  obtain ⟨eS, hSymE, hcrd⟩ := GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys
  have hMn : Geo.Tor.IsNormalScheme M.Z := hover.normal
  have hscale := GlobalTheory.T.thetaConstant_pow_eq_unit_mul_symmetricFunction g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys M eS hMn
    hover.div hSymE
  have hediv : M.HasDiv eS := fun z' => by
    obtain ⟨i', hi'⟩ := hover.div z'
    obtain ⟨j', hj', -⟩ := hscale z' i' hi'
    exact ⟨j', hj'⟩
  obtain ⟨h, hhs, hhc⟩ := GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor o Ω (cycAway n) β M N eS hediv
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  obtain ⟨δ, t, hδ, htop, -, hsec⟩ := GlobalTheory.TupleBundle.exists_lb_of_hasDiv o Ω M S.Gam S.th hover.div
  have hhb := GlobalTheory.T.pull_O1_section_coordinates_power o Ω (cycAway n) M S.Gam S.th δ t N (N + 1).factorial eS h hδ htop hsec hhc hscale
  have hSg : S.g = 8 * g := hsys.2.2.1
  have hkey := GlobalTheory.T.thetaConstantBundle_pow_eight_iso_detHodge_pow_four o Ω S ρ M U₀ EE Zh (by omega) hover hab δ t hδ htop hsec
  haveI : Nonempty U := ⟨⟨_, hUc.1.some_mem⟩⟩
  obtain ⟨x, hxU, hxg⟩ := lemGen o Ω M U
  have hUh : U.ι ≫ h = c ≫ f := GlobalTheory.T.eq_of_same_generic_projective_coords (cycAway n) N U.toScheme (c ≫ F.s) (U.ι ≫ h) (c ≫ f) Ω x eS
    (by rw [Category.assoc, hhs, hUc.2.2.2.1]) (by rw [Category.assoc, hfs]) hxg
    (by rw [← Category.assoc, hxU]; exact hhc)
    (by rw [← Category.assoc, hUc.2.2.2.2 x hxU, Category.assoc]; exact hcrd _ rfl)
  haveI : Surjective c := hUc.2.2.1
  have hUd : Dense (U : Set M.Z) := U.isOpen.dense hUc.1
  obtain ⟨π, hπU, hπp⟩ := GlobalTheory.T.normal_scheme_extension_through_finite_cover (cycAway n) N M.Z F.X Z U c i p h inferInstance hMn hZi hUd
    inferInstance hpf hio hid (by rw [hUh, hip])
  have hss : π ≫ p ≫ PSpace.str (cycAway n) N = M.s ≫ spMap β := by rw [← Category.assoc, hπp, hhs]
  obtain ⟨hπs, hπpr, hZno⟩ := lemProper (cycAway n) o β M.Z F.X Z M.s (p ≫ PSpace.str (cycAway n) N) π i U c
    hover.proj hsys.1 hzproj hUc.2.2.1 hπU hid hss
  have hTI : GlobalTheory.Poinc.ThetaInt F W i := by
    have h0 := GlobalTheory.T.siegelThetaConstants_projectively_integral_anyBase g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf
    rw [← hip] at h0
    intro o' Ω' _ _ _ _ S' ρ' u' hsh hgen M' π' hM' hpt
    exact h0 o' Ω' S' ρ' u' hsh hgen M' (π' ≫ p) hM' (by rw [← Category.assoc, hpt]; simp only [Category.assoc])
  have hiz : i ≫ p ≫ PSpace.str (cycAway n) N = F.s := by rw [← Category.assoc, hip, hfs]

  haveI : IsSeparated G.hom := hGs.separated
  haveI : IsSeparated Zh.G.hom := Zh.semi.separated
  haveI := hGsm
  haveI := Zh.dim
  have hH2 : (hodge G g).IsLB := (GlobalTheory.LieVB.isVB_omega G g).isLB_det
  have hH1 : (hodge Zh.G S.g).IsLB := (GlobalTheory.LieVB.isVB_omega Zh.G S.g).isLB_det
  have hO := GlobalTheory.ProjSpace.O1_isLB (cycAway n) N
  have hLB : LBIso ((lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8).pull π)
      (lbPow (hodge G g) (32 * (N + 1).factorial)) := by
    have e1 := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hO h) (isLB_lbPow hδ _)).2 hhb
    have e2 := (GlobalTheory.CechPic.cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hH1 4)).2 hkey
    have e3 := (GlobalTheory.CechPic.cls_eq_iff hH1 (isLB_lbPow hH2 8)).2 hGh
    rw [GlobalTheory.CechPic.cls_pull hO, GlobalTheory.CechPic.cls_lbPow hδ] at e1
    rw [GlobalTheory.CechPic.cls_lbPow hδ, GlobalTheory.CechPic.cls_lbPow hH1] at e2
    rw [GlobalTheory.CechPic.cls_lbPow hH2] at e3
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hOZlb π) (isLB_lbPow hH2 _)).1 ?_
    rw [GlobalTheory.CechPic.cls_pull hOZlb, GlobalTheory.CechPic.cls_lbPow (pull_isLB hO p), GlobalTheory.CechPic.cls_pull hO,
      GlobalTheory.CechPic.cls_lbPow hH2, map_nsmul, ← GlobalTheory.CechPic.pull_comp, hπp, e1, smul_comm 8, e2, e3, smul_smul,
      smul_smul]
    congr 1
    ring
  refine ⟨Z, p ≫ PSpace.str (cycAway n) N, i, lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8, o, inferInstance, β,
    M.Z, M.s, U, c, π, G, inferInstance, e, inferInstance, 32 * (N + 1).factorial,
    ⟨⟨hzproj, GlobalTheory.IsNormalScheme.of_pred hZn, hio, hiz, hid, W, hW, hTI⟩, hzproj, GlobalTheory.IsNormalScheme.of_pred hZn,
      hiz, hid, hOZlb, hOZamp⟩,
    ⟨hsys.1, hsys.2.1, hover.proj, GlobalTheory.IsNormalScheme.of_pred hMn, hUd, hUc.2.1, hUc.2.2.1, hπU, hss, hπs, hπpr, hZno⟩,
    ⟨hGs, hGsm, hGpb⟩, by have := Nat.factorial_pos (N + 1); omega, hLB⟩

end GlobalTheory.SiegMinTop
