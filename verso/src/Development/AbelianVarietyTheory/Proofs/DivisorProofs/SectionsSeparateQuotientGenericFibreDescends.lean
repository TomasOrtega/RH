import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushSectionsCanonicalModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAdjointNefSeparateEtaleFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsDimPullbackLeGenericallyFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlobalSectionsDimNefPowTensorAmpleIsBiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedStr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsFiniteSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinrankLineBundleSectionsFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResolvedModification
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QuotSep

open Filter

open GlobalTheory.ThickeningDetermines (secIdeal)

/- English proof (translation)
Use `letI := algebraΓAlong k i`. Take `⟨n, e, he, hs⟩` from `hp`. Conclude with `⟨n, i ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom (appTop_algebraMap_along k i)]⟩`.
-/
theorem isProjOver_along {k : Type} [Field k] {X Z : Scheme.{0}} [Algebra k Γ(X, ⊤)] (hp : IsProjOver (strHom k X))
    (i : Z ⟶ X) [IsClosedImmersion i] : letI := algebraΓAlong k i; IsProjOver (strHom k Z) := by
  letI := algebraΓAlong k i
  obtain ⟨n, e, he, hs⟩ := hp
  exact ⟨n, i ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom (appTop_algebraMap_along k i)]⟩

section Cut

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

/- English proof (translation)
Use `(mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)` as an intermediate fact. Use `le_of_eq_of_le ?_ (suppDim_cut_le (structureModule _) hL t (d := d) (by rwa [QCoh.suppDim_structureModule]))` and prove the remaining obligations. Rewrite using `[QCoh.suppDim, support_cut_eq_inter, QCoh.support_structureModule, Set.univ_inter]`. Conclude with `(topologicalKrullDim_eq_of_isEmbedding (secIdeal hL t).subschemeι.isClosedEmbedding.isEmbedding (secIdeal hL t).range_subschemeι).symm`.
-/
theorem dim_zeroScheme_le [IsIntegral X] [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) {t : L.Sec} (ht : t ≠ 0) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) : topologicalKrullDim (secIdeal hL t).subscheme ≤ d := by
  have := (mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)
  refine le_of_eq_of_le ?_ (suppDim_cut_le (structureModule _) hL t (d := d) (by rwa [QCoh.suppDim_structureModule]))
  rw [QCoh.suppDim, support_cut_eq_inter, QCoh.support_structureModule, Set.univ_inter]
  exact (topologicalKrullDim_eq_of_isEmbedding (secIdeal hL t).subschemeι.isClosedEmbedding.isEmbedding
    (secIdeal hL t).range_subschemeι).symm

/- English proof (translation)
Use `letI := algebraΓAlong k (secIdeal hL t).subschemeι`. Use `isNoetherian_of_isProjOver hp` as an intermediate fact. Use `(mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)` as an intermediate fact. Establish `hF` using `finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp`. Establish `h` using `hdim₂_le k (Twist.shortExact_map hB (shortExact_cutComplex (structureModule X) hL t)) 0 ((hF.twist (Twist.isLB_lbZPow hL (-1)) _ hB).finite 0) ((hF.cut hL t _ hB).finite 0)`.

Take `⟨e₁⟩` from `nonempty_twist_twist_iso_of_cls_eq (structureModule X) (Twist.isLB_lbZPow hL (-1)) hB (LB.isLB_div hB hL) (by rw [cls_div hB hL, cls_lbZPow hL]; abel)`. Take `⟨e₂, -⟩` from `exists_cut_structureModule_iso hL t`. Use `Twist.isQuasicoherent_twist (F := structureModule _) (LB.isLB_pull hB (secIdeal hL t).subschemeι)` as an intermediate fact. Use `h.trans_eq (congrArg₂ (· + ·) (hdim_congr k 0 e₁) ((hdim_congr k 0 ((twistFunctor B).mapIso e₂)).trans ((hdim_congr k 0 (Twist.projIso B _ _)).symm.trans ?_)))` and prove the remaining obligations. Conclude with `hdim_pushforward k (appTop_algebraMap_along k _) _ 0`.
-/
theorem globalSections_dim_le_div_add_restriction [IsIntegral X] (hp : IsProjOver (strHom k X)) {L B : LB X} (hL : L.IsLB) (hB : B.IsLB) {t : L.Sec}
    (ht : t ≠ 0) : letI := algebraΓAlong k (secIdeal hL t).subschemeι
    lbH0 k B ≤ lbH0 k (LB.div B L) + lbH0 k (B.pull (secIdeal hL t).subschemeι) := by
  letI := algebraΓAlong k (secIdeal hL t).subschemeι
  have := isNoetherian_of_isProjOver hp
  have := (mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)
  have hF := finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp
  have h := hdim₂_le k (Twist.shortExact_map hB (shortExact_cutComplex (structureModule X) hL t)) 0
    ((hF.twist (Twist.isLB_lbZPow hL (-1)) _ hB).finite 0) ((hF.cut hL t _ hB).finite 0)
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) (Twist.isLB_lbZPow hL (-1)) hB
    (LB.isLB_div hB hL) (by rw [cls_div hB hL, cls_lbZPow hL]; abel)
  obtain ⟨e₂, -⟩ := exists_cut_structureModule_iso hL t
  have := Twist.isQuasicoherent_twist (F := structureModule _) (LB.isLB_pull hB (secIdeal hL t).subschemeι)
  refine h.trans_eq (congrArg₂ (· + ·) (hdim_congr k 0 e₁) ((hdim_congr k 0 ((twistFunctor B).mapIso e₂)).trans
    ((hdim_congr k 0 (Twist.projIso B _ _)).symm.trans ?_)))
  exact hdim_pushforward k (appTop_algebraMap_along k _) _ 0

end Cut

/- English proof (translation)
Use `letI := algebraΓOfHom pX`. Use `letI := algebraΓOfHom pY`. Take `⟨hpp, A, hA⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB pX).1 hX`. Take `⟨B, hB⟩` from `exists_isAmpleLB_of_isProjOver hY`. Establish `: IsProper (strHom F X)` using `by rw [strHom_eq (f := pX) fun _ => rfl]; exact hpp`.

Conclude with `NefFieldExt.isNef_pull hN hL hA hB g`.
-/
theorem nef_pull (hN : GlobalTheory.Published.NefNumerics) {F E : Type} [Field F] [Field E] {X Y : Scheme.{0}} (pX : X ⟶ Sp F)
    (pY : Y ⟶ Sp E) (g : Y ⟶ X) (hX : IsProjOver pX) (hY : IsProjOver pY) (L : LB X)
    (hL : letI := algebraΓOfHom pX; IsNef F L) : letI := algebraΓOfHom pY; IsNef E (L.pull g) := by
  letI := algebraΓOfHom pX
  letI := algebraΓOfHom pY
  obtain ⟨hpp, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB pX).1 hX
  obtain ⟨B, hB⟩ := exists_isAmpleLB_of_isProjOver hY
  have : IsProper (strHom F X) := by rw [strHom_eq (f := pX) fun _ => rfl]; exact hpp
  exact NefFieldExt.isNef_pull hN hL hA hB g

/- English proof (translation)
Use `BigPull.isBig_pull F X M.X sX M.σ M.proj ?_ ?_ δ h` and prove the remaining obligations. Rewrite using `[HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance, HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth M.str n inferInstance]`. Use `M.iso` as an intermediate fact. Use `(U.isOpen.dense hU).mono fun x hx => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `(M.σ ∣_ U).surjective ⟨x, hx⟩`.

Conclude with `⟨y.1, (morphismRestrict_base_coe M.σ U y).symm.trans (congrArg Subtype.val hy)⟩`.
-/
theorem big_pull_modif {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) (hU : (U : Set X).Nonempty) [IsIntegral M.X]
    (δ : LB X) (h : letI := algebraΓOfHom sX; IsBig F δ) : letI := algebraΓOfHom M.str; IsBig F (δ.pull M.σ) := by
  refine BigPull.isBig_pull F X M.X sX M.σ M.proj ?_ ?_ δ h
  · rw [HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance,
      HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth M.str n inferInstance]
  · have := M.iso
    refine (U.isOpen.dense hU).mono fun x hx => ?_
    obtain ⟨y, hy⟩ := (M.σ ∣_ U).surjective ⟨x, hx⟩
    exact ⟨y.1, (morphismRestrict_base_coe M.σ U y).symm.trans (congrArg Subtype.val hy)⟩

/- English proof (translation)
Use `isNoetherian_of_isProjOver hp` as an intermediate fact. Take `⟨q, hq, hg⟩` from `hA.exists_isGenerated_pow`. Establish `hP : (lbPow (lbPow A q) 2).IsLB` using `isLB_lbPow hg.isLB 2`. Take `⟨t, ht⟩ : HasNonzeroSec (lbPow (lbPow A q) 2)` from `hg.hasNonzeroSec.pow hg.isLB 2`. Set `ι` to `(secIdeal hP t).subschemeι`.

Use `letI := algebraΓAlong F ι`. Take `⟨C, hC⟩` from `GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim hN F _ n (isProjOver_along hp ι) (dim_zeroScheme_le hP ht hd.le) (L.pull ι) (A.pull ι) (hL.pull_of_isClosedImmersion ι (appTop_algebraMap_along F ι)) (hA.pull_of_isClosedImmersion ι)`. Establish `hlt : ∀ᶠ m : ℕ in atTop, C < c * (m : ℝ)` using `(tendsto_natCast_atTop_atTop.const_mul_atTop hc).eventually_gt_atTop C`. Take `⟨m, h₁, h₂, h₃, h₄⟩` from `(h.and_eventually (hC.and (hlt.and (eventually_ge_atTop 1)))).exists`. Establish `hB : (tens (lbPow L m) A).IsLB` using `isLB_tens (isLB_lbPow hL.isLB m) hA.isLB`.

Establish `e₁` using `globalSections_dim_le_div_add_restriction hp hP hB ht`. Establish `hLι` using `LB.isLB_pull hL.isLB ι`. Establish `hAι` using `LB.isLB_pull hA.isLB ι`. Establish `e₂ : lbH0 F ((tens (lbPow L m) A).pull ι) = lbH0 F (tens (lbPow (L.pull ι) m) (A.pull ι))` using `lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull hB ι) (isLB_tens (isLB_lbPow hLι m) hAι) (by`. Rewrite using `[cls_pull hB, cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hL.isLB, cls_tens (isLB_lbPow hLι m) hAι, cls_lbPow hLι, cls_pull hL.isLB, cls_pull hA.isLB, map_add, map_nsmul])`.

Establish `hm : (0 : ℝ) < (m : ℝ) ^ n` using `by positivity`. Establish `hpos : 0 < lbH0 F (LB.div (tens (lbPow L m) A) (lbPow (lbPow A q) 2))`. Assume the negation of the conclusion as `h0`. Rewrite `h0` using `[Nat.pos_iff_ne_zero, not_not]`. Rewrite `e₁` using `[h0, zero_add]`.

Establish `e₃ : (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ lbH0 F (tens (lbPow (L.pull ι) m) (A.pull ι))`. Rewrite using `[← e₂]`. Conclude with `e₁` after adjusting the coercions. Use `mul_lt_mul_of_pos_right h₃ hm` as an intermediate fact. Rewrite `h₁` using `[pow_succ]`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨q', rfl⟩` from `Nat.exists_eq_add_of_le' hq`. Establish `hA' : IsAmpleLB (lbPow A (2 * q' + 1))` using `(isAmpleLB_pow_iff hA.isLB (by omega)).2 hA`. Establish `hD` using `Semi.LB.isLB_div (isLB_lbPow hL.isLB m) hA'.isLB`. Take `⟨s, hs⟩` from `hasNonzeroSec_iff.1 ((lineBundleHasNonzeroSection_of_globalSectionsDim_pos hpos).of_cls_eq hD (Semi.LB.isLB_div hB hP) (by`.

Rewrite using `[cls_div (isLB_lbPow hL.isLB m) hA'.isLB, cls_div hB hP, cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hg.isLB, cls_lbPow hA.isLB, cls_lbPow hA.isLB]`. Use the proof step `module))`. Conclude with `⟨m, _, s, h₄, hA'.isLB, hA', hs⟩`.
-/
theorem ampleAt_generic (hN : GlobalTheory.Published.NefNumerics) {F : Type} [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    [Algebra F Γ(Y, ⊤)] (hp : IsProjOver (strHom F Y)) {n : ℕ} (hd : topologicalKrullDim Y = (n + 1 : ℕ))
    {L A : LB Y} (hL : IsNef F L) (hA : IsAmpleLB A) {c : ℝ} (hc : 0 < c)
    (h : ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ (n + 1) ≤ lbH0 F (tens (lbPow L m) A)) : AmpleAt L (genericPoint Y) := by
  have := isNoetherian_of_isProjOver hp
  obtain ⟨q, hq, hg⟩ := hA.exists_isGenerated_pow
  have hP : (lbPow (lbPow A q) 2).IsLB := isLB_lbPow hg.isLB 2
  obtain ⟨t, ht⟩ : HasNonzeroSec (lbPow (lbPow A q) 2) := hg.hasNonzeroSec.pow hg.isLB 2
  let ι := (secIdeal hP t).subschemeι
  letI := algebraΓAlong F ι
  obtain ⟨C, hC⟩ := GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim hN F _ n (isProjOver_along hp ι) (dim_zeroScheme_le hP ht hd.le)
    (L.pull ι) (A.pull ι) (hL.pull_of_isClosedImmersion ι (appTop_algebraMap_along F ι))
    (hA.pull_of_isClosedImmersion ι)
  have hlt : ∀ᶠ m : ℕ in atTop, C < c * (m : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hc).eventually_gt_atTop C
  obtain ⟨m, h₁, h₂, h₃, h₄⟩ := (h.and_eventually (hC.and (hlt.and (eventually_ge_atTop 1)))).exists
  have hB : (tens (lbPow L m) A).IsLB := isLB_tens (isLB_lbPow hL.isLB m) hA.isLB
  have e₁ := globalSections_dim_le_div_add_restriction hp hP hB ht
  have hLι := LB.isLB_pull hL.isLB ι
  have hAι := LB.isLB_pull hA.isLB ι
  have e₂ : lbH0 F ((tens (lbPow L m) A).pull ι) = lbH0 F (tens (lbPow (L.pull ι) m) (A.pull ι)) :=
    lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull hB ι) (isLB_tens (isLB_lbPow hLι m) hAι) (by
      rw [cls_pull hB, cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hL.isLB,
        cls_tens (isLB_lbPow hLι m) hAι, cls_lbPow hLι, cls_pull hL.isLB, cls_pull hA.isLB, map_add, map_nsmul])
  have hm : (0 : ℝ) < (m : ℝ) ^ n := by positivity
  have hpos : 0 < lbH0 F (LB.div (tens (lbPow L m) A) (lbPow (lbPow A q) 2)) := by
    by_contra h0
    rw [Nat.pos_iff_ne_zero, not_not] at h0
    rw [h0, zero_add] at e₁
    have e₃ : (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ lbH0 F (tens (lbPow (L.pull ι) m) (A.pull ι)) := by
      rw [← e₂]; exact_mod_cast e₁
    have := mul_lt_mul_of_pos_right h₃ hm
    rw [pow_succ] at h₁
    nlinarith
  obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le' hq
  have hA' : IsAmpleLB (lbPow A (2 * q' + 1)) := (isAmpleLB_pow_iff hA.isLB (by omega)).2 hA
  have hD := Semi.LB.isLB_div (isLB_lbPow hL.isLB m) hA'.isLB
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 ((lineBundleHasNonzeroSection_of_globalSectionsDim_pos hpos).of_cls_eq hD (Semi.LB.isLB_div hB hP) (by
    rw [cls_div (isLB_lbPow hL.isLB m) hA'.isLB, cls_div hB hP, cls_tens (isLB_lbPow hL.isLB m) hA.isLB,
      cls_lbPow hg.isLB, cls_lbPow hA.isLB, cls_lbPow hA.isLB]
    module))
  exact ⟨m, _, s, h₄, hA'.isLB, hA', hs⟩

/- English proof (translation)
Use `letI := algebraΓOfHom p`. Use `letI := algebraΓOfHom (f ≫ p)`. Take `⟨n, rfl⟩` from `Nat.exists_eq_add_of_le' hn`. Take `⟨r, A, hA, hle⟩` from `GlobalTheory.T.exists_ample_sections_pullback_bound_of_genFinite F M W p f hp hq hf hr`. Take `⟨-, c, hc, hm⟩` from `(isBig_iff (fun _ => rfl) hq hdM).1 hb`.

Use `ampleAt_generic hN (by rwa [strHom_eq (f := p) fun _ => rfl]) hdW hL hA (c := c / (r + 1)) (by positivity) (hm.mono fun m hm => ?_)` and prove the remaining obligations. Establish `hB` using `isLB_lbPow hL.isLB m`. Establish `hL'` using `isLB_lbPow (LB.isLB_pull hL.isLB f) m`. Rewrite `hm` using `[lineBundleGlobalSectionsDim_congr_picardClass hL' (LB.isLB_pull hB f) ((cls_eq_iff hL' (LB.isLB_pull hB f)).2 (lbIso_lbPow_pull hL.isLB f m))]`. Establish `h₁ : (lbH0 F ((lbPow L m).pull f) : ℝ) ≤ r * lbH0 F (tens (lbPow L m) A)` using `by exact_mod_cast hle _ hB`.

Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Establish `: (0 : ℝ) ≤ lbH0 F (tens (lbPow L m) A)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ampleAt_of_isBig_pull (hN : GlobalTheory.Published.NefNumerics) {F : Type} [Field F] {M W : Scheme.{0}} [IsIntegral M]
    [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) {n : ℕ} (hn : 1 ≤ n) (hdW : topologicalKrullDim W = n)
    (hdM : topologicalKrullDim M = n) (hp : IsProjOver p) (hq : IsProjOver (f ≫ p)) (hf : Surjective f)
    (hr : f.residueDegree (genericPoint M) ≠ 0) {L : LB W} (hL : letI := algebraΓOfHom p; IsNef F L)
    (hb : letI := algebraΓOfHom (f ≫ p); IsBig F (L.pull f)) : AmpleAt L (genericPoint W) := by
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨r, A, hA, hle⟩ := GlobalTheory.T.exists_ample_sections_pullback_bound_of_genFinite F M W p f hp hq hf hr
  obtain ⟨-, c, hc, hm⟩ := (isBig_iff (fun _ => rfl) hq hdM).1 hb
  refine ampleAt_generic hN (by rwa [strHom_eq (f := p) fun _ => rfl]) hdW hL hA (c := c / (r + 1))
    (by positivity) (hm.mono fun m hm => ?_)
  have hB := isLB_lbPow hL.isLB m
  have hL' := isLB_lbPow (LB.isLB_pull hL.isLB f) m
  rw [lineBundleGlobalSectionsDim_congr_picardClass hL' (LB.isLB_pull hB f) ((cls_eq_iff hL' (LB.isLB_pull hB f)).2 (lbIso_lbPow_pull hL.isLB f m))] at hm
  have h₁ : (lbH0 F ((lbPow L m).pull f) : ℝ) ≤ r * lbH0 F (tens (lbPow L m) A) := by exact_mod_cast hle _ hB
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ lbH0 F (tens (lbPow L m) A) := by positivity
  nlinarith

/- English proof (translation)
Establish `: IsLocallyNoetherian W` using `LocallyOfFiniteType.isLocallyNoetherian p`. Use `letI := algebraΓOfHom p`. Establish `: CharZero Γ(W, ⊤)` using `charZero_of_injective_algebraMap (algebraMap F Γ(W, ⊤)).injective`. Establish `hη : f (genericPoint M) = genericPoint W`. Establish `h` using `(genericPoint_spec M).image f.continuous`.

Rewrite `h` using `[Set.image_univ, f.surjective.range_eq, closure_univ]`. Conclude with `h.eq (genericPoint_spec W)`. Take `⟨U, -, hU, hη', hU', -, hE, -⟩` from `GenFiniteEtale.exists_finite_etale_of_isProper f hη hr ⊤ trivial`. Use `⟨U, hη', ?_⟩` and prove the remaining obligations. Use `haveI : IsAffine U := hU`.

Use `haveI : IsAffine (f ⁻¹ᵁ U) := hU'`. Rewrite using `[HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]`. Establish `key : ∀ V : W.Opens, V = U → (f.app V).hom.Etale` using `fun V e => e ▸ hE`. Conclude with `(RingHom.Etale.respectsIso.cancel_right_isIso _ _).2 (key _ U.ι_image_top)`.
-/
theorem exists_etale_restrict {F : Type} [Field F] [CharZero F] {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W]
    (p : W ⟶ Sp F) [LocallyOfFiniteType p] (f : M ⟶ W) [IsProper f] [Surjective f]
    (hr : f.residueDegree (genericPoint M) ≠ 0) : ∃ U : W.Opens, genericPoint W ∈ U ∧ Etale (f ∣_ U) := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian p
  letI := algebraΓOfHom p
  have : CharZero Γ(W, ⊤) := charZero_of_injective_algebraMap (algebraMap F Γ(W, ⊤)).injective
  have hη : f (genericPoint M) = genericPoint W := by
    have h := (genericPoint_spec M).image f.continuous
    rw [Set.image_univ, f.surjective.range_eq, closure_univ] at h
    exact h.eq (genericPoint_spec W)
  obtain ⟨U, -, hU, hη', hU', -, hE, -⟩ :=
    GenFiniteEtale.exists_finite_etale_of_isProper f hη hr ⊤ trivial
  refine ⟨U, hη', ?_⟩
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hU'
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
  have key : ∀ V : W.Opens, V = U → (f.app V).hom.Etale := fun V e => e ▸ hE
  exact (RingHom.Etale.respectsIso.cancel_right_isIso _ _).2 (key _ U.ι_image_top)

section Descent

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

/- English proof (translation)
Set `Z : Scheme.{0}` to `pullback p (spMap (algebraMap F ℂ))`. Set `π : Z ⟶ Y` to `pullback.fst p (spMap (algebraMap F ℂ))`. Set `q : Z ⟶ Sp ℂ` to `pullback.snd p (spMap (algebraMap F ℂ))`. Set `S : LinSys F` to `⟨Y, p, n, T, hT, 0, Fin.elim0⟩`. Use `letI := algebraΓOfHom q`.

Take `⟨N, b, hb⟩ : ∃ (N : ℕ) (b : Fin N → T.Sec), ∀ t : (T.pull π).Sec, ∃ u : Fin N → ℂ, ∑ i, algebraMap ℂ Γ(Z, ⊤) (u i) • secPull (b i) π = t` from `SectionsFieldChange.exists_pullSecs_spanning F ℂ S ⟨inferInstance, hp, hc, hn⟩`. Take `⟨t, rfl⟩` from `(bijective_ofSec_top (p := q) (B := T.pull π)).2 g`. Take `⟨u, hu⟩` from `hb t`. Establish `e (c : ℂ) : algebraMap ℂ Γ(Z, ⊤) c = algX q ⊤ c`. Express the relevant statement in the definitionally equal form `q.appTop _ = _`.

Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Establish `ht : t = ∑ i, algX q ⊤ (u i) • secPull (b i) π`. Rewrite using `[← hu]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [e]`.

Establish `hx' : ∀ j, x j ≫ q = spMap (RingHom.id ℂ)` using `fun j => (hx j).trans (Spec.map_id (CommRingCat.of ℂ)).symm`. Establish `hv : ∀ j i, val (x j) (pIdx T π (k j)) le_top (hk' j) (ofSec q ⊤ (secPull (b i) π)) = val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i))` using `fun j i => by`. Use `(val_ofSec (p := q) (O := ⊤) (x j) _ le_top (hk' j) _).trans (Eq.trans ?_ (val_ofSec (p := p) (O := ⊤) (x j ≫ π) _ le_top (hk j) _).symm)` and prove the remaining obligations. Conclude with `congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom ((b i).f (k j))) (Scheme.Hom.appLE_comp_appLE (x j) π (T.U (k j)) _ ⊤ ((chartPullPull T π).le (pIdx T π (k j))) (hk' j))`. Establish `hs : ∀ j, val (x j) (pIdx T π (k j)) le_top (hk' j) (ofSec q ⊤ t) = ∑ i, u i * val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i))` using `fun j => by`.

Rewrite using `[ht, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ofSec_smul]`. Conclude with `(H0.val_smul (O := ⊤) (x j) (hx' j) _ le_top (hk' j) _ _).trans (congrArg (u i * ·) (hv j i))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hs j, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Use `_ = 0 := by`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, h, mul_zero]`.
-/
theorem sum_val_pull_eq_zero {F : Type} [Field F] [Algebra F ℂ] {Y : Scheme.{0}} (p : Y ⟶ Sp F) (n : ℕ)
    [SmoothOfRelativeDimension n p] (hp : IsProjOver p) (hc : GeometricallyConnected p) (hn : 1 ≤ n) {T : LB Y}
    (hT : T.IsLB) {J : Type} [Fintype J] (x : J → (Sp ℂ ⟶ pullback p (spMap (algebraMap F ℂ))))
    (hx : ∀ j, x j ≫ pullback.snd _ _ = 𝟙 _) (k : J → T.ι)
    (hk : ∀ j, ⊤ ≤ (x j ≫ pullback.fst _ _) ⁻¹ᵁ T.U (k j))
    (hk' : ∀ j, ⊤ ≤ x j ⁻¹ᵁ (T.pull (pullback.fst _ _)).U (pIdx T _ (k j))) (a : J → ℂ)
    (h : ∀ g : H0 p T ⊤, ∑ j, a j * val (x j ≫ pullback.fst _ _) (k j) le_top (hk j) g = 0)
    (g : H0 (pullback.snd p (spMap (algebraMap F ℂ))) (T.pull (pullback.fst _ _)) ⊤) :
    ∑ j, a j * val (x j) (pIdx T _ (k j)) le_top (hk' j) g = 0 := by
  let Z : Scheme.{0} := pullback p (spMap (algebraMap F ℂ))
  let π : Z ⟶ Y := pullback.fst p (spMap (algebraMap F ℂ))
  let q : Z ⟶ Sp ℂ := pullback.snd p (spMap (algebraMap F ℂ))
  let S : LinSys F := ⟨Y, p, n, T, hT, 0, Fin.elim0⟩
  letI := algebraΓOfHom q
  obtain ⟨N, b, hb⟩ : ∃ (N : ℕ) (b : Fin N → T.Sec), ∀ t : (T.pull π).Sec, ∃ u : Fin N → ℂ,
      ∑ i, algebraMap ℂ Γ(Z, ⊤) (u i) • secPull (b i) π = t :=
    SectionsFieldChange.exists_pullSecs_spanning F ℂ S ⟨inferInstance, hp, hc, hn⟩
  obtain ⟨t, rfl⟩ := (bijective_ofSec_top (p := q) (B := T.pull π)).2 g
  obtain ⟨u, hu⟩ := hb t
  have e (c : ℂ) : algebraMap ℂ Γ(Z, ⊤) c = algX q ⊤ c := by
    change q.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have ht : t = ∑ i, algX q ⊤ (u i) • secPull (b i) π := by
    rw [← hu]
    exact Finset.sum_congr rfl fun i _ => by rw [e]
  have hx' : ∀ j, x j ≫ q = spMap (RingHom.id ℂ) := fun j =>
    (hx j).trans (Spec.map_id (CommRingCat.of ℂ)).symm
  have hv : ∀ j i, val (x j) (pIdx T π (k j)) le_top (hk' j) (ofSec q ⊤ (secPull (b i) π)) =
      val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i)) := fun j i => by
    refine (val_ofSec (p := q) (O := ⊤) (x j) _ le_top (hk' j) _).trans
      (Eq.trans ?_ (val_ofSec (p := p) (O := ⊤) (x j ≫ π) _ le_top (hk j) _).symm)
    exact congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom ((b i).f (k j)))
      (Scheme.Hom.appLE_comp_appLE (x j) π (T.U (k j)) _ ⊤ ((chartPullPull T π).le (pIdx T π (k j))) (hk' j))
  have hs : ∀ j, val (x j) (pIdx T π (k j)) le_top (hk' j) (ofSec q ⊤ t) =
      ∑ i, u i * val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i)) := fun j => by
    rw [ht, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofSec_smul]
    exact (H0.val_smul (O := ⊤) (x j) (hx' j) _ le_top (hk' j) _ _).trans (congrArg (u i * ·) (hv j i))
  calc _ = ∑ j, ∑ i, u i * (a j * val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i))) :=
        Finset.sum_congr rfl fun j _ => by
          rw [hs j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, h, mul_zero]

abbrev tensPullChart {X Y : Scheme.{0}} {K B : LB Y} (π : X ⟶ Y) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.triv X) (tens (K.pull π) (B.pull π)) ((tens K B).pull π) where
  isLB₁ := LB.isLB_triv X
  isLB₂ := isLB_tens (LB.isLB_pull hK π) (LB.isLB_pull hB π)
  isLB₃ := LB.isLB_pull (isLB_tens hK hB) π
  τ := K.ι × B.ι
  a _ := PUnit.unit
  b t := (pIdx K π t.1, pIdx B π t.2)
  c t := pIdx (tens K B) π t
  cover x := by
    obtain ⟨j, hj⟩ := exists_chart hK (π x)
    obtain ⟨l, hl⟩ := exists_chart hB (π x)
    exact ⟨(j, l), trivial, ⟨mem_pIdx.2 hj, mem_pIdx.2 hl⟩, mem_pIdx.2 ⟨hj, hl⟩⟩
  rule x t t' e e' := by
    have h1 : tr (LB.triv X) x PUnit.unit PUnit.unit = 1 := map_one _
    rw [h1, one_mul, tr_tens _ _ x e.2.1 e'.2.1, tr_pull _ π x e.2.2 e'.2.2, tr_pull _ π x e.2.1.1 e'.2.1.1,
      tr_pull _ π x e.2.1.2 e'.2.1.2, tr_tens _ _ (π x) (mem_pull.1 e.2.2) (mem_pull.1 e'.2.2), map_mul]
    rfl

/- English proof (translation)
Set `one : (LB.triv X).Sec` to `⟨fun _ => 1, fun _ _ => by simp⟩`. Use `⟨(tensPullChart π hK hB).mul (ofSec q ⊤ one) g, fun x t h h' => ?_⟩` and prove the remaining obligations. Establish `e` using `(tensPullChart π hK hB).val_mul (ofSec q ⊤ one) g t x le_top le_top h h'`. Establish `e₁ : val x PUnit.unit le_top le_top (ofSec q ⊤ one) = 1` using `(val_ofSec (p := q) (O := ⊤) x _ le_top le_top one).trans (map_one _)`. Conclude with `e.trans ((congrArg (· * _) e₁).trans (one_mul _))`.
-/
theorem exists_val_eq_tens_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} (q : X ⟶ Sp k) {K B : LB Y} (π : X ⟶ Y)
    (hK : K.IsLB) (hB : B.IsLB) (g : H0 q (tens (K.pull π) (B.pull π)) ⊤) :
    ∃ g' : H0 q ((tens K B).pull π) ⊤, ∀ (x : Sp ℂ ⟶ X) (t : (tens K B).ι)
      (h : ⊤ ≤ x ⁻¹ᵁ (tens (K.pull π) (B.pull π)).U (pIdx K π t.1, pIdx B π t.2))
      (h' : ⊤ ≤ x ⁻¹ᵁ ((tens K B).pull π).U (pIdx (tens K B) π t)),
      val x (pIdx (tens K B) π t) le_top h' g' = val x (pIdx K π t.1, pIdx B π t.2) le_top h g := by
  let one : (LB.triv X).Sec := ⟨fun _ => 1, fun _ _ => by simp⟩
  refine ⟨(tensPullChart π hK hB).mul (ofSec q ⊤ one) g, fun x t h h' => ?_⟩
  have e := (tensPullChart π hK hB).val_mul (ofSec q ⊤ one) g t x le_top le_top h h'
  have e₁ : val x PUnit.unit le_top le_top (ofSec q ⊤ one) = 1 :=
    (val_ofSec (p := q) (O := ⊤) x _ le_top le_top one).trans (map_one _)
  exact e.trans ((congrArg (· * _) e₁).trans (one_mul _))

end Descent

/- English proof (translation)
Establish `H₁` using `(isPullback_morphismRestrict f' (b ⁻¹ᵁ U)).flip.paste_horiz H`. Establish `H₂` using `(isPullback_morphismRestrict f U).flip`. Rewrite `H₁` using `[← morphismRestrict_ι b U]`. Establish `H₃` using `IsPullback.of_right (h₁₁ := H₂.lift _ _ (H₁.w.trans (Category.assoc _ _ _).symm)) (by rwa [H₂.lift_fst]) (H₂.lift_snd _ _ _) H₂`. Conclude with `MorphismProperty.of_isPullback (P := @Etale) H₃ hU`.
-/
theorem etale_restrict_of_isPullback {M W M' W' : Scheme.{0}} {a : M' ⟶ M} {f' : M' ⟶ W'} {f : M ⟶ W} {b : W' ⟶ W}
    (H : IsPullback a f' f b) (U : W.Opens) (hU : Etale (f ∣_ U)) : Etale (f' ∣_ (b ⁻¹ᵁ U)) := by
  have H₁ := (isPullback_morphismRestrict f' (b ⁻¹ᵁ U)).flip.paste_horiz H
  have H₂ := (isPullback_morphismRestrict f U).flip
  rw [← morphismRestrict_ι b U] at H₁
  have H₃ := IsPullback.of_right (h₁₁ := H₂.lift _ _ (H₁.w.trans (Category.assoc _ _ _).symm))
    (by rwa [H₂.lift_fst]) (H₂.lift_snd _ _ _) H₂
  exact MorphismProperty.of_isPullback (P := @Etale) H₃ hU

/- English proof (translation)
Break down `isEmpty_or_nonempty J with hJ | ⟨⟨j₀⟩⟩` into its components or cases. Conclude with `Subsingleton.elim _ _`. Use `letI : Algebra F ℂ := σ.toAlgebra`. Set `πW` to `pullback.fst p (spMap (algebraMap F ℂ))`. Set `pC` to `pullback.snd p (spMap (algebraMap F ℂ))`.

Set `πM` to `pullback.fst (f ≫ p) (spMap (algebraMap F ℂ))`. Set `qM` to `pullback.snd (f ≫ p) (spMap (algebraMap F ℂ))`. Establish `HW : IsPullback πW pC p (spMap (algebraMap F ℂ))` using `IsPullback.of_hasPullback _ _`. Establish `HM : IsPullback πM qM (f ≫ p) (spMap (algebraMap F ℂ))` using `IsPullback.of_hasPullback _ _`. Set `fC` to `HW.lift (πM ≫ f) qM (by rw [Category.assoc, HM.w])`.

Establish `hf₁ : fC ≫ πW = πM ≫ f` using `HW.lift_fst _ _ _`. Establish `hf₂ : fC ≫ pC = qM` using `HW.lift_snd _ _ _`. Establish `HM' : IsPullback πM (fC ≫ pC) (f ≫ p) (spMap (algebraMap F ℂ))` using `hf₂.symm ▸ HM`. Establish `Hf : IsPullback πM fC f πW` using `IsPullback.of_bot HM' hf₁.symm HW`. Take `⟨hWi, -, hWs, hWq, -⟩` from `BaseChangeVariety.baseChange_props F ℂ W _ p pC πW n HW hWp hWc`.

Take `⟨hMi, -, hMs, hMq, -⟩` from `BaseChangeVariety.baseChange_props F ℂ M _ (f ≫ p) (fC ≫ pC) πM n HM' hMp hMc`. Use `haveI := hWi`. Use `haveI := hMi`. Use `haveI := hWs`. Use `haveI := hMs`.

Use `haveI : Surjective fC := MorphismProperty.of_isPullback (P := @Surjective) Hf inferInstance`. Use `haveI : IsAffineHom πW := MorphismProperty.of_isPullback (P := @IsAffineHom) HW.flip inferInstance`. Set `zC : J → (Sp ℂ ⟶ pullback (f ≫ p) (spMap (algebraMap F ℂ)))` to `fun j => HM.lift (z j) (𝟙 _) (by rw [hzp j, Category.id_comp])`. Establish `hz₁ : ∀ j, zC j ≫ πM = z j` using `fun j => HM.lift_fst _ _ _`. Establish `hz₂ : ∀ j, zC j ≫ qM = 𝟙 _` using `fun j => HM.lift_snd _ _ _`.

Set `x` to `zC j₀ ≫ fC`. Establish `hxW : ∀ j, (zC j ≫ fC) ≫ πW = z j ≫ f` using `fun j => by`. Rewrite using `[Category.assoc, hf₁, ← Category.assoc, hz₁]`. Establish `hxp : ∀ j, (zC j ≫ fC) ≫ pC = 𝟙 _` using `fun j => by rw [Category.assoc, hf₂, hz₂]`. Establish `hzx : ∀ j, zC j ≫ fC = x` using `fun j => HW.hom_ext (by rw [hxW, hxW, hzf j j₀]) (by rw [hxp, hxp])`.

Establish `hπx : ∀ s, πW (x s) = (z j₀ ≫ f) s` using `fun s => congrArg (fun g => g s) (hxW j₀)`. Take `⟨s₀⟩ : Nonempty (Sp ℂ)` from `inferInstance`. Use `letI := algebraΓOfHom pC`. Use `letI := algebraΓOfHom (fC ≫ pC)`. Establish `hNC` using `LB.isLB_pull hN πW`.

Establish `hAx : AmpleAt (N.pull πW) (x s₀)` using `AmplePull.ampleAt_pull W _ πW N hN (x s₀) (by rw [hπx]; exact (hzU j₀ s₀).2)`. Establish `hNnC : IsNef ℂ (N.pull πW)` using `nef_pull hNN p pC πW hWp hWq N hNn`. Establish `hc : 1 • cls (N.pull πW) hNC = cls (N.pull πW) hNC + cls (LB.triv _) (LB.isLB_triv _)`. Rewrite using `[one_smul, cls_triv, add_zero]`. Establish `hbig : IsBig ℂ (N.pull πW)` using `isBig_of_smul_cls_eq_add_ampleAt hNN ℂ _ pC hWq _ _ _ hNC hNC (LB.isLB_triv _) 1 (x s₀) hNnC one_pos hc hAx (isNef_triv ℂ _)`.

Establish `hpos` using `GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive hNN ℂ _ pC hWq _ _ _ hNC hNC (LB.isLB_triv _) 1 (x s₀) hNnC one_pos hc hAx (isNef_triv ℂ _)`. Establish `hbig' : IsBig ℂ ((N.pull πW).pull fC)` using `BigPull.isBig_pull ℂ _ _ pC fC hMq (by rw [HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth pC n hWs, HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (fC ≫ pC) n hMs]) fC.surjective.denseRange _ hbig`. Establish `hUC : Etale (fC ∣_ (πW ⁻¹ᵁ U))` using `etale_restrict_of_isPullback Hf U hU`. Establish `hcB : cls (B.pull πM) (LB.isLB_pull hB πM) = m • CechPic.pull fC (cls (N.pull πW) hNC) + cls (N'.pull πM) (LB.isLB_pull hN' πM)`. Rewrite using `[cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add, map_nsmul, ← pull_comp, ← pull_comp, hf₁]`.

Establish `hpt : ∀ (Y : Scheme.{0}) (y : Sp ℂ ⟶ Y) (O : Y.Opens), y s₀ ∈ O → ⊤ ≤ y ⁻¹ᵁ O`. Introduce `Y y O hs t _`. Rewrite using `[Subsingleton.elim t s₀]`. Conclude with `hs`. Establish `hkM : ∀ j, ⊤ ≤ (zC j ≫ πM) ⁻¹ᵁ (tens K.bundle B).U (k j)` using `fun j => by rw [hz₁]; exact hk j`.

Establish `hk₁ : ∀ j, ⊤ ≤ zC j ⁻¹ᵁ (tens (K.bundle.pull πM) (B.pull πM)).U (pIdx _ πM (k j).1, pIdx B πM (k j).2)` using `fun j => hpt _ _ _ ⟨mem_pIdx.2 (hkM j trivial).1, mem_pIdx.2 (hkM j trivial).2⟩`. Establish `hk₂ : ∀ j, ⊤ ≤ zC j ⁻¹ᵁ ((tens K.bundle B).pull πM).U (pIdx _ πM (k j))` using `fun j => hpt _ _ _ (mem_pIdx.2 (hkM j trivial))`. Use `GlobalTheory.T.sections_adjointNef_separate_etaleFibre hK hNN _ _ pC fC n hWq hMq hn (CanonLB.baseChange HM' K) (N.pull πW) hNC (N'.pull πM) (B.pull πM) (LB.isLB_pull hN' πM) (LB.isLB_pull hB πM) m x (πW ⁻¹ᵁ U) hNnC hbig (nef_pull hNN pC (fC ≫ pC) fC hWq hMq _ hNnC) hbig' (nef_pu …` and prove the remaining obligations. Take `⟨g', hg'⟩` from `exists_val_eq_tens_pull qM πM K.isLB hB g`. Establish `key` using `sum_val_pull_eq_zero (f ≫ p) n hMp hMc hn (isLB_tens K.isLB hB) zC hz₂ k hkM hk₂ a (fun g => by`.

Rewrite using `[← h g]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hv : ∀ {y y' : Sp ℂ ⟶ M} (_ : y = y') (hy : ⊤ ≤ y ⁻¹ᵁ (tens K.bundle B).U (k j)) (hy' : ⊤ ≤ y' ⁻¹ᵁ (tens K.bundle B).U (k j)), H0.val y (k j) le_top hy g = H0.val y' (k j) le_top hy' g`. Introduce and unpack `y _ rfl _ _`. Both sides reduce to the same expression.

Conclude with `congrArg (a j * ·) (hv (hz₁ j) (hkM j) (hk j))) g'`. Rewrite using `[← key]`. Conclude with `Finset.sum_congr rfl fun j _ => congrArg (a j * ·) (hg' (zC j) (k j) (hk₁ j) (hk₂ j)).symm`.
-/
theorem separate_numberField (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (F : Type) [Field F] (σ : F →+* ℂ) (M W : Scheme.{0}) (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ)
    [SmoothOfRelativeDimension n (f ≫ p)] [SmoothOfRelativeDimension n p] (hMp : IsProjOver (f ≫ p))
    (hWp : IsProjOver p) (hMc : GeometricallyConnected (f ≫ p)) (hWc : GeometricallyConnected p) [Surjective f]
    (hn : 1 ≤ n) (U : W.Opens) (hU : Etale (f ∣_ U)) (K : CanonLB (f ≫ p) n) (N : LB W) (hN : N.IsLB) (N' B : LB M)
    (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (hNn : letI := algebraΓOfHom p; IsNef F N)
    (hN'n : letI := algebraΓOfHom (f ≫ p); IsNef F N') (hm : (n + 1).choose 2 < m)
    (hBc : cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN') (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M))
    (hz : Function.Injective z) (hzp : ∀ j, z j ≫ f ≫ p = spMap σ) (hzf : ∀ j j', z j ≫ f = z j' ≫ f)
    (hzU : ∀ j s, (z j ≫ f) s ∈ U ∧ AmpleAt N ((z j ≫ f) s)) (k : J → (tens K.bundle B).ι)
    (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ)
    (h : ∀ g : H0 (f ≫ p) (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) : a = 0 := by
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j₀⟩⟩
  · exact Subsingleton.elim _ _
  letI : Algebra F ℂ := σ.toAlgebra
  let πW := pullback.fst p (spMap (algebraMap F ℂ))
  let pC := pullback.snd p (spMap (algebraMap F ℂ))
  let πM := pullback.fst (f ≫ p) (spMap (algebraMap F ℂ))
  let qM := pullback.snd (f ≫ p) (spMap (algebraMap F ℂ))
  have HW : IsPullback πW pC p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  have HM : IsPullback πM qM (f ≫ p) (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  let fC := HW.lift (πM ≫ f) qM (by rw [Category.assoc, HM.w])
  have hf₁ : fC ≫ πW = πM ≫ f := HW.lift_fst _ _ _
  have hf₂ : fC ≫ pC = qM := HW.lift_snd _ _ _
  have HM' : IsPullback πM (fC ≫ pC) (f ≫ p) (spMap (algebraMap F ℂ)) := hf₂.symm ▸ HM
  have Hf : IsPullback πM fC f πW := IsPullback.of_bot HM' hf₁.symm HW
  obtain ⟨hWi, -, hWs, hWq, -⟩ := BaseChangeVariety.baseChange_props F ℂ W _ p pC πW n HW hWp hWc
  obtain ⟨hMi, -, hMs, hMq, -⟩ := BaseChangeVariety.baseChange_props F ℂ M _ (f ≫ p) (fC ≫ pC) πM n HM' hMp hMc
  haveI := hWi; haveI := hMi; haveI := hWs; haveI := hMs
  haveI : Surjective fC := MorphismProperty.of_isPullback (P := @Surjective) Hf inferInstance
  haveI : IsAffineHom πW := MorphismProperty.of_isPullback (P := @IsAffineHom) HW.flip inferInstance
  let zC : J → (Sp ℂ ⟶ pullback (f ≫ p) (spMap (algebraMap F ℂ))) := fun j =>
    HM.lift (z j) (𝟙 _) (by rw [hzp j, Category.id_comp])
  have hz₁ : ∀ j, zC j ≫ πM = z j := fun j => HM.lift_fst _ _ _
  have hz₂ : ∀ j, zC j ≫ qM = 𝟙 _ := fun j => HM.lift_snd _ _ _
  let x := zC j₀ ≫ fC
  have hxW : ∀ j, (zC j ≫ fC) ≫ πW = z j ≫ f := fun j => by
    rw [Category.assoc, hf₁, ← Category.assoc, hz₁]
  have hxp : ∀ j, (zC j ≫ fC) ≫ pC = 𝟙 _ := fun j => by rw [Category.assoc, hf₂, hz₂]
  have hzx : ∀ j, zC j ≫ fC = x := fun j =>
    HW.hom_ext (by rw [hxW, hxW, hzf j j₀]) (by rw [hxp, hxp])
  have hπx : ∀ s, πW (x s) = (z j₀ ≫ f) s := fun s => congrArg (fun g => g s) (hxW j₀)
  obtain ⟨s₀⟩ : Nonempty (Sp ℂ) := inferInstance
  letI := algebraΓOfHom pC
  letI := algebraΓOfHom (fC ≫ pC)
  have hNC := LB.isLB_pull hN πW
  have hAx : AmpleAt (N.pull πW) (x s₀) :=
    AmplePull.ampleAt_pull W _ πW N hN (x s₀) (by rw [hπx]; exact (hzU j₀ s₀).2)
  have hNnC : IsNef ℂ (N.pull πW) := nef_pull hNN p pC πW hWp hWq N hNn
  have hc : 1 • cls (N.pull πW) hNC = cls (N.pull πW) hNC + cls (LB.triv _) (LB.isLB_triv _) := by
    rw [one_smul, cls_triv, add_zero]
  have hbig : IsBig ℂ (N.pull πW) :=
    isBig_of_smul_cls_eq_add_ampleAt hNN ℂ _ pC hWq _ _ _ hNC hNC (LB.isLB_triv _) 1 (x s₀) hNnC one_pos hc hAx
      (isNef_triv ℂ _)
  have hpos := GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive hNN ℂ _ pC hWq _ _ _ hNC hNC (LB.isLB_triv _) 1 (x s₀) hNnC one_pos hc hAx
    (isNef_triv ℂ _)
  have hbig' : IsBig ℂ ((N.pull πW).pull fC) := BigPull.isBig_pull ℂ _ _ pC fC hMq
    (by rw [HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth pC n hWs,
      HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (fC ≫ pC) n hMs])
    fC.surjective.denseRange _ hbig
  have hUC : Etale (fC ∣_ (πW ⁻¹ᵁ U)) := etale_restrict_of_isPullback Hf U hU
  have hcB : cls (B.pull πM) (LB.isLB_pull hB πM) =
      m • CechPic.pull fC (cls (N.pull πW) hNC) + cls (N'.pull πM) (LB.isLB_pull hN' πM) := by
    rw [cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add, map_nsmul, ← pull_comp, ← pull_comp, hf₁]
  have hpt : ∀ (Y : Scheme.{0}) (y : Sp ℂ ⟶ Y) (O : Y.Opens), y s₀ ∈ O → ⊤ ≤ y ⁻¹ᵁ O := by
    intro Y y O hs t _
    rw [Subsingleton.elim t s₀]
    exact hs
  have hkM : ∀ j, ⊤ ≤ (zC j ≫ πM) ⁻¹ᵁ (tens K.bundle B).U (k j) := fun j => by rw [hz₁]; exact hk j
  have hk₁ : ∀ j, ⊤ ≤ zC j ⁻¹ᵁ (tens (K.bundle.pull πM) (B.pull πM)).U (pIdx _ πM (k j).1, pIdx B πM (k j).2) :=
    fun j => hpt _ _ _ ⟨mem_pIdx.2 (hkM j trivial).1, mem_pIdx.2 (hkM j trivial).2⟩
  have hk₂ : ∀ j, ⊤ ≤ zC j ⁻¹ᵁ ((tens K.bundle B).pull πM).U (pIdx _ πM (k j)) :=
    fun j => hpt _ _ _ (mem_pIdx.2 (hkM j trivial))
  refine GlobalTheory.T.sections_adjointNef_separate_etaleFibre hK hNN _ _ pC fC n hWq hMq hn (CanonLB.baseChange HM' K) (N.pull πW) hNC (N'.pull πM)
    (B.pull πM) (LB.isLB_pull hN' πM) (LB.isLB_pull hB πM) m x (πW ⁻¹ᵁ U) hNnC hbig
    (nef_pull hNN pC (fC ≫ pC) fC hWq hMq _ hNnC) hbig' (nef_pull hNN (f ≫ p) (fC ≫ pC) πM hMp hMq N' hN'n) hm hcB
    (hxp j₀) (hpt _ _ _ (show πW (x s₀) ∈ U from hπx s₀ ▸ (hzU j₀ s₀).1)) hUC
    (fun Z e hZ hxZ he hd => hpos Z e hZ (hxZ ⟨s₀, rfl⟩) he hd) J zC
    (fun j j' e => hz (by rw [← hz₁, ← hz₁ j', e])) hzx _ hk₁ a fun g => ?_
  obtain ⟨g', hg'⟩ := exists_val_eq_tens_pull qM πM K.isLB hB g
  have key := sum_val_pull_eq_zero (f ≫ p) n hMp hMc hn (isLB_tens K.isLB hB) zC hz₂ k hkM hk₂ a (fun g => by
    rw [← h g]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hv : ∀ {y y' : Sp ℂ ⟶ M} (_ : y = y') (hy : ⊤ ≤ y ⁻¹ᵁ (tens K.bundle B).U (k j))
        (hy' : ⊤ ≤ y' ⁻¹ᵁ (tens K.bundle B).U (k j)),
        H0.val y (k j) le_top hy g = H0.val y' (k j) le_top hy' g := by
      rintro y _ rfl _ _
      rfl
    exact congrArg (a j * ·) (hv (hz₁ j) (hkM j) (hk j))) g'
  rw [← key]
  exact Finset.sum_congr rfl fun j _ => congrArg (a j * ·) (hg' (zC j) (k j) (hk₁ j) (hk₂ j)).symm

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `separate_numberField hK hNN F σ M W p f n hMp hWp hMc hWc hn U hU K N hN N' B hN' hB m hNn hN'n hm hBc J z hz hzp hzf hzU k hk a h`.
-/
theorem separate_numberField' (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (F : Type) [Field F] (σ : F →+* ℂ) (M W : Scheme.{0}) (pM : M ⟶ Sp F) (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ)
    [SmoothOfRelativeDimension n pM] [SmoothOfRelativeDimension n p] (e : f ≫ p = pM) (hMp : IsProjOver pM)
    (hWp : IsProjOver p) (hMc : GeometricallyConnected pM) (hWc : GeometricallyConnected p) (hf : Surjective f)
    (hn : 1 ≤ n) (U : W.Opens) (hU : Etale (f ∣_ U)) (K : CanonLB pM n) (N : LB W) (hN : N.IsLB) (N' B : LB M)
    (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (hNn : letI := algebraΓOfHom p; IsNef F N)
    (hN'n : letI := algebraΓOfHom pM; IsNef F N') (hm : (n + 1).choose 2 < m)
    (hBc : cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN') (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M))
    (hz : Function.Injective z) (hzp : ∀ j, z j ≫ pM = spMap σ) (hzf : ∀ j j', z j ≫ f = z j' ≫ f)
    (hzU : ∀ j s, (z j ≫ f) s ∈ U ∧ AmpleAt N ((z j ≫ f) s)) (k : J → (tens K.bundle B).ι)
    (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ)
    (h : ∀ g : H0 pM (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) : a = 0 := by
  subst e
  exact separate_numberField hK hNN F σ M W p f n hMp hWp hMc hWc hn U hU K N hN N' B hN' hB m hNn hN'n hm hBc J z
    hz hzp hzf hzU k hk a h

/- English proof (translation)
Substitute `e` using the available equality. Establish `hdW` using `HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p n inferInstance`. Establish `hdM` using `HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (f ≫ p) n inferInstance`. Establish `h₁ : IsProper p` using `((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hWp).1`. Establish `h₂ : IsProper (f ≫ p)` using `((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hMp).1`.

Establish `h₃ : IsProper f` using `IsProper.of_comp f p`. Establish `hr` using `GlobalTheory.T.residue_degree_generic_ne_zero_equidimensional F M W p f n inferInstance inferInstance hf hdM hdW`. Conclude with `⟨ampleAt_of_isBig_pull hNN p f hn hdW hdM hWp hMp hf hr hL hb, exists_etale_restrict p f hr⟩`.
-/
theorem generic_data (hNN : GlobalTheory.Published.NefNumerics) {F : Type} [Field F] [CharZero F] {M W : Scheme.{0}}
    [IsIntegral M] [IsIntegral W] (pM : M ⟶ Sp F) (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ)
    [SmoothOfRelativeDimension n pM] [SmoothOfRelativeDimension n p] (hn : 1 ≤ n) (e : f ≫ p = pM)
    (hMp : IsProjOver pM) (hWp : IsProjOver p) (hf : Surjective f) (L : LB W)
    (hL : letI := algebraΓOfHom p; IsNef F L) (hb : letI := algebraΓOfHom pM; IsBig F (L.pull f)) :
    AmpleAt L (genericPoint W) ∧ ∃ U : W.Opens, genericPoint W ∈ U ∧ Etale (f ∣_ U) := by
  subst e
  have hdW := HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p n inferInstance
  have hdM := HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (f ≫ p) n inferInstance
  have h₁ : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hWp).1
  have h₂ : IsProper (f ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hMp).1
  have h₃ : IsProper f := IsProper.of_comp f p
  have hr := GlobalTheory.T.residue_degree_generic_ne_zero_equidimensional F M W p f n inferInstance inferInstance hf hdM hdW
  exact ⟨ampleAt_of_isBig_pull hNN p f hn hdW hdM hWp hMp hf hr hL hb, exists_etale_restrict p f hr⟩

/- English proof (translation)
Introduce `hK hNN hPr F _ _ σ X X' W V _ _ _ sX n _ φ q sW i ℓ hXp hgc hn hφp hWp hqf hqs hcomm hi hℓ hℓφ`. Use `letI := algebraΓOfHom sX`. Introduce `K δ N' B hδ hN' hB N hN m hpull hδn hδb hN'n hm hBc J _ v hv hvσ hvq hvgen k hk a hsum`. Use `haveI := hi`. Take `⟨W', hW'i, pW, U, M, f, NW, hNW, hMi, hWs, hWp', hWgc, hfp, hfs, hUne, hcls, z, hzU, hzσ, hzf, hzgen⟩` from `QuotSetup.exists_resolved_modification hPr F X X' W V sX n φ q sW i ℓ hXp hgc hφp hWp hqf hqs hcomm hi hℓ hℓφ δ hδ N hN hpull J v hvq hvgen`.

Use `haveI := hW'i`. Use `haveI := hMi`. Use `haveI := hWs`. Establish `hUd : Dense (U : Set X)` using `U.isOpen.dense hUne`. Establish `hMgc : GeometricallyConnected M.str` using `Modif.geometricallyConnected_str F X sX U n M inferInstance hgc hUd`.

Establish `hδσn : (letI` using `algebraΓOfHom M.str; IsNef F (δ.pull M.σ)) := nef_pull hNN sX M.str M.σ hXp M.proj δ hδn`. Establish `hN'σn : (letI` using `algebraΓOfHom M.str; IsNef F (N'.pull M.σ)) := nef_pull hNN sX M.str M.σ hXp M.proj N' hN'n`. Establish `hδσb : (letI` using `algebraΓOfHom M.str; IsBig F (δ.pull M.σ)) := big_pull_modif sX n U M hUne δ hδb`. Establish `hNWn : (letI` using `algebraΓOfHom pW; IsNef F NW) := GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective F M.X W' f pW M.str NW hNW (δ.pull M.σ) (LB.isLB_pull hδ M.σ) hfp hWp' M.proj hfs hcls hδσn`. Use `letI := algebraΓOfHom M.str`.

Establish `hfNb : IsBig F (NW.pull f)` using `hδσb.of_cls_eq (LB.isLB_pull hNW f) hcls`. Take `⟨hamp, UW, hgUW, het⟩` from `generic_data hNN M.str pW f n hn hfp M.proj hWp' hfs NW hNWn hfNb`. Set `K' : CanonLB M.str n` to `CanonLB.all M.str n`. Take `⟨Ψ, hΨ⟩` from `GlobalTheory.T.exists_push_sections_canonical_modification F X sX n U M K K' B hXp hUne hB`. Establish `hK'B : (tens K'.bundle (B.pull M.σ)).IsLB` using `isLB_tens K'.isLB (LB.isLB_pull hB M.σ)`.

Take `⟨s0⟩ : Nonempty (Sp ℂ)` from `inferInstance`. Establish `hpt : ∀ (Y : Scheme.{0}) (x : Sp ℂ ⟶ Y) (O : Y.Opens), x s0 ∈ O → ⊤ ≤ x ⁻¹ᵁ O`. Introduce `Y x O hs t _`. Rewrite using `[Subsingleton.elim t s0]`. Conclude with `hs`.

Use `choose k' hk' using fun j => (exists_chart hK'B ((z j) s0)).imp fun c hc => hpt _ (z j) _ hc`. Establish `hkσ : ∀ j, ⊤ ≤ (z j ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U (k j)` using `fun j => by rw [hzσ j]; exact hk j`. Use `choose lam hlam using fun j => hΨ (z j) (hzU j) (k' j) (hk' j) (k j) (hkσ j)`. Establish `hvx : ∀ {x y : Sp ℂ ⟶ X} (e : x = y) (c : (tens K.bundle B).ι) (hx : ⊤ ≤ x ⁻¹ᵁ (tens K.bundle B).U c) (hy : ⊤ ≤ y ⁻¹ᵁ (tens K.bundle B).U c) (g : H0 sX (tens K.bundle B) ⊤), H0.val x c le_top hx g = H0.val y c le_top hy g`. Introduce `x y e c hx hy g`.

Substitute `e` using the available equality. Both sides reduce to the same expression. Establish `hzinj : Function.Injective z` using `fun j j' e => hv ((cancel_mono i).1 (by rw [← hzσ j, ← hzσ j', e]))`. Establish `hzp : ∀ j, z j ≫ M.str = spMap σ` using `fun j => by show z j ≫ M.σ ≫ sX = _`. Rewrite using `[← Category.assoc, hzσ j, Category.assoc]`.

Conclude with `hvσ j`. Establish `hBM : cls (B.pull M.σ) (LB.isLB_pull hB M.σ) = m • CechPic.pull f (cls NW hNW) + cls (N'.pull M.σ) (LB.isLB_pull hN' M.σ)`. Rewrite using `[hcls]`. Express the relevant statement in the definitionally equal form `CechPic.pull M.σ (cls B hB) = m • CechPic.pull M.σ (cls δ hδ) + CechPic.pull M.σ (cls N' hN')`. Rewrite using `[hBc, map_add, map_nsmul]`.

Establish `hsep` using `separate_numberField' hK hNN F σ M.X W' M.str pW f n hfp M.proj hWp' hMgc hWgc hfs hn UW het K' NW hNW (N'.pull M.σ) (B.pull M.σ) (LB.isLB_pull hN' M.σ) (LB.isLB_pull hB M.σ) m hNWn hN'σn hm hBM J z hzinj hzp hzf (fun j s => by rw [hzgen j s]; exact ⟨hgUW, hamp⟩) k' hk' (fun j => …`. Rewrite using `[← hsum (Ψ g)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hvx (hzσ j) (k j) (hkσ j) (hk j) (Ψ g), hlam j g]`. Use the proof step `ring)`.

Use function extensionality and compare the values at `j`. Establish `h` using `congrFun hsep j`. Simplify `h` using `[Units.ne_zero]`.
-/
theorem sections_separate_quotient_fibre : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [NumberField F] (σ : F →+* ℂ) (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → 1 ≤ n → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → letI := algebraΓOfHom sX; ∀ (K : CanonLB sX n) (δ N' B : LB X) (hδ : δ.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (N : LB W) (hN : N.IsLB) (m : ℕ), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → IsNef F δ → IsBig F δ → IsNef F N' → (n + 1).choose 2 < m → cls B hB = m • cls δ hδ + cls N' hN' → ∀ (J : Type) [Fintype J] (v : J → (Sp ℂ ⟶ V)), Function.Injective v → (∀ j, v j ≫ i ≫ sX = spMap σ) → (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 sX (tens K.bundle B) ⊤, ∑ j, a j * H0.val (v j ≫ i) (k j) le_top (hk j) g = 0) → a = 0 := by
  intro hK hNN hPr F _ _ σ X X' W V _ _ _ sX n _ φ q sW i ℓ hXp hgc hn hφp hWp hqf hqs hcomm hi hℓ hℓφ
  letI := algebraΓOfHom sX
  intro K δ N' B hδ hN' hB N hN m hpull hδn hδb hN'n hm hBc J _ v hv hvσ hvq hvgen k hk a hsum
  haveI := hi
  obtain ⟨W', hW'i, pW, U, M, f, NW, hNW, hMi, hWs, hWp', hWgc, hfp, hfs, hUne, hcls, z, hzU, hzσ, hzf, hzgen⟩ :=
    QuotSetup.exists_resolved_modification hPr F X X' W V sX n φ q sW i ℓ hXp hgc hφp hWp hqf hqs hcomm hi hℓ hℓφ δ hδ N hN hpull J v hvq hvgen
  haveI := hW'i; haveI := hMi; haveI := hWs
  have hUd : Dense (U : Set X) := U.isOpen.dense hUne
  have hMgc : GeometricallyConnected M.str :=
    Modif.geometricallyConnected_str F X sX U n M inferInstance hgc hUd
  have hδσn : (letI := algebraΓOfHom M.str; IsNef F (δ.pull M.σ)) :=
    nef_pull hNN sX M.str M.σ hXp M.proj δ hδn
  have hN'σn : (letI := algebraΓOfHom M.str; IsNef F (N'.pull M.σ)) :=
    nef_pull hNN sX M.str M.σ hXp M.proj N' hN'n
  have hδσb : (letI := algebraΓOfHom M.str; IsBig F (δ.pull M.σ)) := big_pull_modif sX n U M hUne δ hδb
  have hNWn : (letI := algebraΓOfHom pW; IsNef F NW) :=
    GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective F M.X W' f pW M.str NW hNW (δ.pull M.σ) (LB.isLB_pull hδ M.σ) hfp hWp' M.proj hfs hcls hδσn
  letI := algebraΓOfHom M.str
  have hfNb : IsBig F (NW.pull f) := hδσb.of_cls_eq (LB.isLB_pull hNW f) hcls
  obtain ⟨hamp, UW, hgUW, het⟩ := generic_data hNN M.str pW f n hn hfp M.proj hWp' hfs NW hNWn hfNb
  let K' : CanonLB M.str n := CanonLB.all M.str n
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_push_sections_canonical_modification F X sX n U M K K' B hXp hUne hB
  have hK'B : (tens K'.bundle (B.pull M.σ)).IsLB := isLB_tens K'.isLB (LB.isLB_pull hB M.σ)
  obtain ⟨s0⟩ : Nonempty (Sp ℂ) := inferInstance
  have hpt : ∀ (Y : Scheme.{0}) (x : Sp ℂ ⟶ Y) (O : Y.Opens), x s0 ∈ O → ⊤ ≤ x ⁻¹ᵁ O := by
    intro Y x O hs t _
    rw [Subsingleton.elim t s0]
    exact hs
  choose k' hk' using fun j => (exists_chart hK'B ((z j) s0)).imp fun c hc => hpt _ (z j) _ hc
  have hkσ : ∀ j, ⊤ ≤ (z j ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U (k j) := fun j => by rw [hzσ j]; exact hk j
  choose lam hlam using fun j => hΨ (z j) (hzU j) (k' j) (hk' j) (k j) (hkσ j)
  have hvx : ∀ {x y : Sp ℂ ⟶ X} (e : x = y) (c : (tens K.bundle B).ι) (hx : ⊤ ≤ x ⁻¹ᵁ (tens K.bundle B).U c)
      (hy : ⊤ ≤ y ⁻¹ᵁ (tens K.bundle B).U c) (g : H0 sX (tens K.bundle B) ⊤),
      H0.val x c le_top hx g = H0.val y c le_top hy g := by
    intro x y e c hx hy g
    subst e
    rfl
  have hzinj : Function.Injective z := fun j j' e => hv ((cancel_mono i).1 (by rw [← hzσ j, ← hzσ j', e]))
  have hzp : ∀ j, z j ≫ M.str = spMap σ := fun j => by
    show z j ≫ M.σ ≫ sX = _
    rw [← Category.assoc, hzσ j, Category.assoc]
    exact hvσ j
  have hBM : cls (B.pull M.σ) (LB.isLB_pull hB M.σ) =
      m • CechPic.pull f (cls NW hNW) + cls (N'.pull M.σ) (LB.isLB_pull hN' M.σ) := by
    rw [hcls]
    change CechPic.pull M.σ (cls B hB) = m • CechPic.pull M.σ (cls δ hδ) + CechPic.pull M.σ (cls N' hN')
    rw [hBc, map_add, map_nsmul]
  have hsep := separate_numberField' hK hNN F σ M.X W' M.str pW f n hfp M.proj hWp' hMgc hWgc hfs hn UW het K' NW hNW
    (N'.pull M.σ) (B.pull M.σ) (LB.isLB_pull hN' M.σ) (LB.isLB_pull hB M.σ) m hNWn hN'σn hm hBM
    J z hzinj hzp hzf (fun j s => by rw [hzgen j s]; exact ⟨hgUW, hamp⟩) k' hk' (fun j => a j * (lam j : ℂ)) (fun g => by
      rw [← hsum (Ψ g)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hvx (hzσ j) (k j) (hkσ j) (hk j) (Ψ g), hlam j g]
      ring)
  funext j
  have h := congrFun hsep j
  simpa [Units.ne_zero] using h

end GlobalTheory.QuotSep
