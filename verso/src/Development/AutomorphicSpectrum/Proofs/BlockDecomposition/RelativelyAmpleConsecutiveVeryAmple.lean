import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre GlobalTheory.ProjSpace

namespace GlobalTheory.CompanionTheory.ConsecAmple

variable {R : Type} [CommRing R] {X Y Z P : Scheme.{0}}

/- English proof (translation)
Take `⟨hs, hs'⟩` from `hf`. Take `⟨ht, ht'⟩` from `hg`. Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations. Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)`.

Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)`. Use `TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩` and prove the remaining obligations. Rewrite using `[nonzeroLocus_boxSec, e.apply_symm_apply]`. Conclude with `⟨hi, hj⟩`. Take `⟨aff₁, r₁, hr₁, sj₁⟩` from `hs' (e a).1`.

Take `⟨aff₂, r₂, hr₂, sj₂⟩` from `ht' (e a).2`. Establish `loc` using `nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)`. Establish `l₁` using `loc.le.trans inf_le_left`. Establish `l₂` using `loc.le.trans inf_le_right`. Establish `o₁ : r₁ (e a).1 = 1` using `ratio_self _ _ (hr₁ _)`.

Establish `o₂ : r₂ (e a).2 = 1` using `ratio_self _ _ (hr₂ _)`. Use `⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩` and prove the remaining obligations. Establish `: IsAffine _` using `aff₁`. Establish `: IsAffine _` using `aff₂`. Establish `: IsAffine _` using `isAffineOpen_top (Spec (CommRingCat.of R))`.

Conclude with `.of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom`. Use `(rs_mul p q _ _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)` and prove the remaining obligations. Conclude with `(congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans (mul_mul_mul_comm _ _ _ _)`. Establish `po` using `(isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1 (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)`. Rewrite using `[← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]`.

Introduce and unpack `_ (⟨d, rfl⟩ | ⟨d, rfl⟩)`. Take `⟨F, rfl⟩` from `sj₁ d`. Express the relevant statement in the definitionally equal form `ap p l₁ _ ∈ _`. Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩`.

Consider the case `add F G hF hG => rw [map_add, map_add]`. Conclude with `Subring.add_mem _ hF hG`. Consider the case `mul_X F i hF`. Rewrite using `[map_mul, map_mul]`. Use `Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩` and prove the remaining obligations.

Simplify using `only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]`. Take `⟨F, rfl⟩` from `sj₂ d`. Express the relevant statement in the definitionally equal form `ap q l₂ _ ∈ _`. Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C c => exact ⟨MvPolynomial.C c, by`.

Rewrite using `[MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩`. Consider the case `add F G hF hG => rw [map_add, map_add]`. Conclude with `Subring.add_mem _ hF hG`. Consider the case `mul_X F i hF`. Rewrite using `[map_mul, map_mul]`.

Use `Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩` and prove the remaining obligations. Simplify using `only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]`.
-/
theorem veryAmpleBy_box {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Spec (CommRingCat.of R)}
    {g : Y ⟶ Spec (CommRingCat.of R)} (sq : IsPullback p q f g) {H : LB X} {K : LB Y} {m n : ℕ}
    {s : Fin (m + 1) → LB.Sec H} {t : Fin (n + 1) → LB.Sec K} (hf : VeryAmpleBy f H s) (hg : VeryAmpleBy g K t)
    (e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1)) :
    VeryAmpleBy (p ≫ f) (box p q H K) fun a => boxSec p q (s (e a).1) (t (e a).2) := by
  obtain ⟨hs, hs'⟩ := hf
  obtain ⟨ht, ht'⟩ := hg
  refine ⟨?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
    rw [nonzeroLocus_boxSec, e.apply_symm_apply]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' (e a).1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht' (e a).2
  have loc := nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ (e a).1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ (e a).2 = 1 := ratio_self _ _ (hr₂ _)
  refine ⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change ap q l₂ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]

/- English proof (translation)
Take `⟨hs, hc⟩` from `(veryAmpleBy_iff f s).1 h`. Use `(veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_secPull hs j, ?_⟩` and prove the remaining obligations. Rewrite using `[toProj_secPull hs j]`. Use `infer_instance`.
-/
theorem veryAmpleBy_secPull {f : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y} {M : ℕ} {s : Fin (M + 1) → LB.Sec L}
    (h : VeryAmpleBy f L s) (j : Z ⟶ Y) [IsClosedImmersion j] :
    VeryAmpleBy (j ≫ f) (L.pull j) fun i => GlobalTheory.Cartier.secPull (s i) j := by
  obtain ⟨hs, hc⟩ := (veryAmpleBy_iff f s).1 h
  refine (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_secPull hs j, ?_⟩
  rw [toProj_secPull hs j]
  infer_instance

/- English proof (translation)
Establish `e : Units.map (ap p h).toMonoidHom u = res h (pullU p U u)` using `Units.ext rfl`. Rewrite using `[e]`. Conclude with `(gm_res r z h hz _).trans (gm_pull r p z U (h hz) u)`.
-/
theorem gm_ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (r : Z ⟶ P) (z : Z) (hz : r z ∈ W)
    (u : Γ(X, U)ˣ) : gm r z W (Units.map (ap p h).toMonoidHom u) = gm (r ≫ p) z U u := by
  have e : Units.map (ap p h).toMonoidHom u = res h (pullU p U u) := Units.ext rfl
  rw [e]
  exact (gm_res r z h hz _).trans (gm_pull r p z U (h hz) u)

/- English proof (translation)
The claim follows from `(map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_ap p _ r z h _) (gm_ap q _ r z h _))`.
-/
theorem gm_box (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (K : LB Y) (r : Z ⟶ P) (z : Z) (a b : H.ι × K.ι)
    (h : r z ∈ (box p q H K).U a ⊓ (box p q H K).U b) :
    gm r z ((box p q H K).U a ⊓ (box p q H K).U b) ((box p q H K).g a b) =
      gm (r ≫ p) z (H.U a.1 ⊓ H.U b.1) (H.g a.1 b.1) * gm (r ≫ q) z (K.U a.2 ⊓ K.U b.2) (K.g a.2 b.2) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_ap p _ r z h _) (gm_ap q _ r z h _))

/- English proof (translation)
Establish `h₁ : p (j y) = y` using `by rw [← Scheme.Hom.comp_apply, hp]; rfl`. Establish `h₂ : q (j y) = ψ y` using `by rw [← Scheme.Hom.comp_apply, hq]`. Establish `h₃ : ψ y ∈ B.U (c.1 PUnit.unit)` using `mem_pull.1 hy.1`. Establish `h₄ : y ∈ H.U c.2` using `hy.2`. Conclude with `⟨show p (j y) ∈ H.U c.2 by rw [h₁]; exact h₄, show q (j y) ∈ _ by rw [h₂]; exact h₃⟩`.
-/
theorem mem_box_of_graph (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (B : LB Y) (ψ : X ⟶ Y) (j : X ⟶ P) (hp : j ≫ p = 𝟙 X)
    (hq : j ≫ q = ψ) (c : (B.pull ψ).ι × H.ι) (y : X) (hy : y ∈ (tw (B.pull ψ) H 1).U c) :
    j y ∈ (box p q H B).U (c.2, c.1 PUnit.unit) := by
  have h₁ : p (j y) = y := by rw [← Scheme.Hom.comp_apply, hp]; rfl
  have h₂ : q (j y) = ψ y := by rw [← Scheme.Hom.comp_apply, hq]
  have h₃ : ψ y ∈ B.U (c.1 PUnit.unit) := mem_pull.1 hy.1
  have h₄ : y ∈ H.U c.2 := hy.2
  exact ⟨show p (j y) ∈ H.U c.2 by rw [h₁]; exact h₄, show q (j y) ∈ _ by rw [h₂]; exact h₃⟩

def chartPullBox (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (B : LB Y) (ψ : X ⟶ Y) (j : X ⟶ P) (hp : j ≫ p = 𝟙 X)
    (hq : j ≫ q = ψ) : ChartPull (tw (B.pull ψ) H 1) (box p q H B) j where
  idx c := (c.2, c.1 PUnit.unit)
  le c y hy := mem_box_of_graph p q H B ψ j hp hq c y hy
  g y c c' hc hc' := by
    refine (GlobalTheory.LBAlg.gm_tw (B.pull ψ) H 1 (𝟙 X) y c c' ⟨hc, hc'⟩).trans (Eq.trans ?_
      (gm_box p q H B j y _ _ ⟨mem_box_of_graph p q H B ψ j hp hq c y hc,
        mem_box_of_graph p q H B ψ j hp hq c' y hc'⟩).symm)
    rw [gm_pull_g B ψ (𝟙 X) y c.1 c'.1 hc.1 hc'.1, hp, hq, Category.id_comp, zpow_one, mul_comm]

/- English proof (translation)
Establish `hψ : toProj f c hc ≫ PSpace.str R n = f` using `toProj_str f c hc`. Establish `sq` using `IsPullback.of_hasPullback f (PSpace.str R n)`. Set `j : X ⟶ pullback f (PSpace.str R n)` to `pullback.lift (𝟙 X) (toProj f c hc) (by rw [hψ, Category.id_comp])`. Establish `hp : j ≫ pullback.fst f (PSpace.str R n) = 𝟙 X` using `pullback.lift_fst _ _ _`. Establish `hq : j ≫ pullback.snd f (PSpace.str R n) = toProj f c hc` using `pullback.lift_snd _ _ _`.

Use `isProper_str R n` as an intermediate fact. Establish `: IsSeparated (pullback.fst f (PSpace.str R n))` using `inferInstance`. Establish `: IsClosedImmersion j`. Establish `: IsClosedImmersion (j ≫ pullback.fst f (PSpace.str R n))` using `by rw [hp]; infer_instance`. Conclude with `IsClosedImmersion.of_comp j (pullback.fst f (PSpace.str R n))`.

Establish `hcoord : VeryAmpleBy (PSpace.str R n) (O1 R n) (coord R n)` using `(veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_coord R n, by rw [toProj_coord]; infer_instance⟩`. Set `e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1)` to `(finCongr (by ring)).trans finProdFinEquiv.symm`. Establish `h₁` using `veryAmpleBy_secPull (veryAmpleBy_box sq ha hcoord e) j`. Establish `e₁ : j ≫ pullback.fst f (PSpace.str R n) ≫ f = f` using `by rw [← Category.assoc, hp, Category.id_comp]`. Rewrite `h₁` using `[e₁]`.

Establish `hB` using `isLB_box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) hK (O1_isLB R n)`. Establish `hO` using `LB.isLB_pull (O1_isLB R n) (toProj f c hc)`. Establish `i₁ : LBIso ((box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) K (O1 R n)).pull j) (tw ((O1 R n).pull (toProj f c hc)) K 1)` using `LBIso.chartPull (chartPullPull _ j) (chartPullBox _ _ K (O1 R n) _ j hp hq) (GlobalTheory.LBAlg.lbIso_self hB)`. Establish `i₂` using `GlobalTheory.LBAlg.lbIso_tw_congr (t := 1) hK (lbIso_pullback_O1_toProj f c hc)`. Take `⟨t, ht⟩` from `GlobalTheory.exists_veryAmpleBy_of_lbIso (LB.isLB_pull hB j) (isLB_tw hM hK 1) (LBIso.trans (LB.isLB_pull hB j) (isLB_tw hO hK 1) (isLB_tw hM hK 1) i₁ i₂) h₁`.

Conclude with `⟨_, t, ht⟩`.
-/
theorem exists_veryAmpleBy_tw {f : X ⟶ Spec (CommRingCat.of R)} {K M : LB X} (hK : K.IsLB) (hM : M.IsLB) {m n : ℕ}
    {a : Fin (m + 1) → LB.Sec K} (ha : VeryAmpleBy f K a) {c : Fin (n + 1) → LB.Sec M}
    (hc : ⨆ i, nonzeroLocus (c i) = ⊤) :
    ∃ (m' : ℕ) (s : Fin (m' + 1) → LB.Sec (tw M K 1)), VeryAmpleBy f (tw M K 1) s := by
  have hψ : toProj f c hc ≫ PSpace.str R n = f := toProj_str f c hc
  have sq := IsPullback.of_hasPullback f (PSpace.str R n)
  let j : X ⟶ pullback f (PSpace.str R n) := pullback.lift (𝟙 X) (toProj f c hc) (by rw [hψ, Category.id_comp])
  have hp : j ≫ pullback.fst f (PSpace.str R n) = 𝟙 X := pullback.lift_fst _ _ _
  have hq : j ≫ pullback.snd f (PSpace.str R n) = toProj f c hc := pullback.lift_snd _ _ _
  have := isProper_str R n
  have : IsSeparated (pullback.fst f (PSpace.str R n)) := inferInstance
  have : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ pullback.fst f (PSpace.str R n)) := by rw [hp]; infer_instance
    exact IsClosedImmersion.of_comp j (pullback.fst f (PSpace.str R n))
  have hcoord : VeryAmpleBy (PSpace.str R n) (O1 R n) (coord R n) :=
    (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_coord R n, by rw [toProj_coord]; infer_instance⟩
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) := (finCongr (by ring)).trans finProdFinEquiv.symm
  have h₁ := veryAmpleBy_secPull (veryAmpleBy_box sq ha hcoord e) j
  have e₁ : j ≫ pullback.fst f (PSpace.str R n) ≫ f = f := by rw [← Category.assoc, hp, Category.id_comp]
  rw [e₁] at h₁
  have hB := isLB_box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) hK (O1_isLB R n)
  have hO := LB.isLB_pull (O1_isLB R n) (toProj f c hc)
  have i₁ : LBIso ((box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) K (O1 R n)).pull j)
      (tw ((O1 R n).pull (toProj f c hc)) K 1) :=
    LBIso.chartPull (chartPullPull _ j) (chartPullBox _ _ K (O1 R n) _ j hp hq) (GlobalTheory.LBAlg.lbIso_self hB)
  have i₂ := GlobalTheory.LBAlg.lbIso_tw_congr (t := 1) hK (lbIso_pullback_O1_toProj f c hc)
  obtain ⟨t, ht⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (LB.isLB_pull hB j) (isLB_tw hM hK 1)
    (LBIso.trans (LB.isLB_pull hB j) (isLB_tw hO hK 1) (isLB_tw hM hK 1) i₁ i₂) h₁
  exact ⟨_, t, ht⟩

/- English proof (translation)
The claim follows from `map_zpow _ _ _`.
-/
theorem gm_pw (H : LB X) (n : ℤ) (r : Z ⟶ X) (z : Z) (i j : H.ι) :
    gm r z ((pw H n).U i ⊓ (pw H n).U j) ((pw H n).g i j) = gm r z (H.U i ⊓ H.U j) (H.g i j) ^ n :=
  map_zpow _ _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩`. Simplify using `only [zpow_mul]`.
-/
theorem pw_pw (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  change (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  simp only [zpow_mul]

/- English proof (translation)
Establish `l₁ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.1` using `fun p x hx => ⟨hx.1, hx.2.1.1⟩`. Establish `l₂ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.2` using `fun p x hx => ⟨hx.1, hx.2.1.2⟩`. Establish `l₃ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.2` using `fun p x hx => ⟨hx.1, hx.2.2⟩`. Establish `v : ∀ (x : X) (p : L.ι × ((L.ι × L.ι) × L.ι)), x ∈ L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) → gm (𝟙 X) x _ (res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) * res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) = gm (𝟙 X) x _ (L.g p.1 p.2.1.1) * gm (𝟙 X) x _ (L. …` using `fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _) ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _))))) ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _))))`. Establish `key : ∀ (x : X) {a b i j : L.ι}, x ∈ L.U a → x ∈ L.U b → x ∈ L.U i → x ∈ L.U j → gm (𝟙 X) x _ (L.g a i) = gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b j) * (gm (𝟙 X) x _ (L.g i j))⁻¹`.

Introduce `x a b i j ha hb hi hj`. Rewrite using `[gm_cocycle hL (𝟙 X) x ha hb hj, ← gm_cocycle hL (𝟙 X) x ha hi hj, mul_inv_cancel_right]`. Use `GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) * res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) fun x p q h₁ h₂ h₃ h₄ => ?_` and prove the remaining obligations. Establish `eA : gm (𝟙 X) x _ ((tw (tw L (pw L N) t) (pw (pw L N) t) 1).g p.2 q.2) = gm (𝟙 X) x (L.U p.2.1.1 ⊓ L.U q.2.1.1) (L.g p.2.1.1 q.2.1.1) * gm (𝟙 X) x (L.U p.2.1.2 ⊓ L.U q.2.1.2) (L.g p.2.1.2 q.2.1.2) ^ (N * t) * gm (𝟙 X) x (L.U p.2.2 ⊓ L.U q.2.2) (L.g p.2.2 q.2.2) ^ (N * t)`. Use `(GlobalTheory.LBAlg.gm_tw (tw L (pw L N) t) (pw (pw L N) t) 1 (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩).trans ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.LBAlg.gm_tw L (pw L N) t (𝟙 X) x p.2.1 q.2.1 ⟨h₂.1, h₄.1⟩]`. Use `congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) ?_` and prove the remaining obligations. Conclude with `(congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.1.2 q.2.1.2)).trans (zpow_mul _ _ _).symm`. Conclude with `((zpow_one _).trans (gm_pw (pw L N) t (𝟙 X) x p.2.2 q.2.2)).trans ((congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.2 q.2.2)).trans (zpow_mul _ _ _).symm)`. Use `(v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw L _ (𝟙 X) x p.1 q.1).symm (congrArg (·⁻¹) eA.symm)) (v x q ⟨h₃, h₄⟩).symm))` and prove the remaining obligations.

Establish `k₁` using `key x (a := p.1) (b := q.1) (i := p.2.1.1) (j := q.2.1.1) h₁ h₃ h₂.1.1 h₄.1.1`. Establish `k₂` using `key x (a := p.1) (b := q.1) (i := p.2.1.2) (j := q.2.1.2) h₁ h₃ h₂.1.2 h₄.1.2`. Establish `k₃` using `key x (a := p.1) (b := q.1) (i := p.2.2) (j := q.2.2) h₁ h₃ h₂.2 h₄.2`. Rewrite using `[k₁, k₂, k₃]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Use `module`.
-/
theorem lbIso_tw_tw_pw {L : LB X} (hL : L.IsLB) (N t : ℤ) :
    LBIso (tw (tw L (pw L N) t) (pw (pw L N) t) 1) (pw L (1 + 2 * N * t)) := by
  have l₁ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.1 :=
    fun p x hx => ⟨hx.1, hx.2.1.1⟩
  have l₂ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.2 :=
    fun p x hx => ⟨hx.1, hx.2.1.2⟩
  have l₃ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.2 :=
    fun p x hx => ⟨hx.1, hx.2.2⟩
  have v : ∀ (x : X) (p : L.ι × ((L.ι × L.ι) × L.ι)), x ∈ L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) →
      gm (𝟙 X) x _ (res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) *
          res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) =
        gm (𝟙 X) x _ (L.g p.1 p.2.1.1) * gm (𝟙 X) x _ (L.g p.1 p.2.1.2) ^ (N * t) *
          gm (𝟙 X) x _ (L.g p.1 p.2.2) ^ (N * t) :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ x _ hx _) ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _)))))
      ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _))))
  have key : ∀ (x : X) {a b i j : L.ι}, x ∈ L.U a → x ∈ L.U b → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (L.g a i) = gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b j) * (gm (𝟙 X) x _ (L.g i j))⁻¹ := by
    intro x a b i j ha hb hi hj
    rw [gm_cocycle hL (𝟙 X) x ha hb hj, ← gm_cocycle hL (𝟙 X) x ha hi hj, mul_inv_cancel_right]
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) *
    res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) fun x p q h₁ h₂ h₃ h₄ => ?_
  have eA : gm (𝟙 X) x _ ((tw (tw L (pw L N) t) (pw (pw L N) t) 1).g p.2 q.2) =
      gm (𝟙 X) x (L.U p.2.1.1 ⊓ L.U q.2.1.1) (L.g p.2.1.1 q.2.1.1) *
        gm (𝟙 X) x (L.U p.2.1.2 ⊓ L.U q.2.1.2) (L.g p.2.1.2 q.2.1.2) ^ (N * t) *
        gm (𝟙 X) x (L.U p.2.2 ⊓ L.U q.2.2) (L.g p.2.2 q.2.2) ^ (N * t) := by
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L N) t) (pw (pw L N) t) 1 (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩).trans ?_
    rw [GlobalTheory.LBAlg.gm_tw L (pw L N) t (𝟙 X) x p.2.1 q.2.1 ⟨h₂.1, h₄.1⟩]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) ?_
    · exact (congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.1.2 q.2.1.2)).trans (zpow_mul _ _ _).symm
    · exact ((zpow_one _).trans (gm_pw (pw L N) t (𝟙 X) x p.2.2 q.2.2)).trans
        ((congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.2 q.2.2)).trans (zpow_mul _ _ _).symm)
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw L _ (𝟙 X) x p.1 q.1).symm
    (congrArg (·⁻¹) eA.symm)) (v x q ⟨h₃, h₄⟩).symm))
  have k₁ := key x (a := p.1) (b := q.1) (i := p.2.1.1) (j := q.2.1.1) h₁ h₃ h₂.1.1 h₄.1.1
  have k₂ := key x (a := p.1) (b := q.1) (i := p.2.1.2) (j := q.2.1.2) h₁ h₃ h₂.1.2 h₄.1.2
  have k₃ := key x (a := p.1) (b := q.1) (i := p.2.2) (j := q.2.2) h₁ h₃ h₂.2 h₄.2
  rw [k₁, k₂, k₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

/- English proof (translation)
Introduce `A _ _ X L hL hA`. Take `⟨N, hN, m, s, hH, hs⟩` from `veryAmpleBy_of_relAmple hL hA (𝟙 X.left) (Category.id_comp _) hL (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _)) (GlobalTheory.LBAlg.lbIso_self hL))`. Take `⟨t₀, ht₀⟩` from `GlobalTheory.TwistGen.twist_generated A X.left X.hom (pw L N) m s hH hs L hL`. Take `⟨T, hT, hTt⟩ : ∃ T : ℕ, 1 ≤ T ∧ t₀ ≤ (T : ℤ)` from `⟨(max t₀ 1).toNat, by omega, by omega⟩`. Take `⟨n', u, hu⟩` from `ht₀ T hTt`.

Take `⟨k, a, ha⟩` from `veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs T hT`. Establish `hK` using `isLB_pw hH T`. Establish `hM` using `isLB_tw hL hH T`. Take `⟨m', s', hs'⟩` from `exists_veryAmpleBy_tw hK hM ha hu`. Take `⟨t', ht'⟩` from `GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw hM hK 1) (isLB_pw hL _) (lbIso_tw_tw_pw hL N T) hs'`.

Establish `A₁ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T : ℕ) : ℤ))), VeryAmpleBy X.hom (pw L ((2 * N * T : ℕ) : ℤ)) a`. Establish `e₁ : pw L ((2 * N * T : ℕ) : ℤ) = pw (pw L N) ((2 * T : ℕ) : ℤ)`. Rewrite using `[pw_pw]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e₁]`. Conclude with `veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs (2 * T) (by omega)`. Establish `A₂ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T + 1 : ℕ) : ℤ))), VeryAmpleBy X.hom (pw L ((2 * N * T + 1 : ℕ) : ℤ)) a`. Establish `e₂ : ((2 * N * T + 1 : ℕ) : ℤ) = 1 + 2 * (N : ℤ) * (T : ℤ)`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e₂]`. Conclude with `⟨m', t', ht'⟩`. Take `⟨k₁, a₁, h₁⟩` from `A₁`.

Take `⟨k₂, a₂, h₂⟩` from `A₂`. Conclude with `⟨2 * N * T, Nat.mul_pos (Nat.mul_pos two_pos hN) hT, k₁, a₁, k₂, a₂, h₁, h₂⟩`.
-/
theorem exists_consecutive_veryAmple : ∀ (A : Type) [CommRing A] [IsNoetherianRing A]
    (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∃ (m : ℕ)
    (s : Fin (m + 1) → LB.Sec (pw L (d : ℤ))) (m' : ℕ) (s' : Fin (m' + 1) → LB.Sec (pw L ((d + 1 : ℕ) : ℤ))),
    VeryAmpleBy X.hom (pw L (d : ℤ)) s ∧ VeryAmpleBy X.hom (pw L ((d + 1 : ℕ) : ℤ)) s' := by
  intro A _ _ X L hL hA
  obtain ⟨N, hN, m, s, hH, hs⟩ := veryAmpleBy_of_relAmple hL hA (𝟙 X.left) (Category.id_comp _) hL
    (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _)) (GlobalTheory.LBAlg.lbIso_self hL))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated A X.left X.hom (pw L N) m s hH hs L hL
  obtain ⟨T, hT, hTt⟩ : ∃ T : ℕ, 1 ≤ T ∧ t₀ ≤ (T : ℤ) := ⟨(max t₀ 1).toNat, by omega, by omega⟩
  obtain ⟨n', u, hu⟩ := ht₀ T hTt
  obtain ⟨k, a, ha⟩ := veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs T hT
  have hK := isLB_pw hH T
  have hM := isLB_tw hL hH T
  obtain ⟨m', s', hs'⟩ := exists_veryAmpleBy_tw hK hM ha hu
  obtain ⟨t', ht'⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw hM hK 1) (isLB_pw hL _)
    (lbIso_tw_tw_pw hL N T) hs'
  have A₁ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T : ℕ) : ℤ))),
      VeryAmpleBy X.hom (pw L ((2 * N * T : ℕ) : ℤ)) a := by
    have e₁ : pw L ((2 * N * T : ℕ) : ℤ) = pw (pw L N) ((2 * T : ℕ) : ℤ) := by
      rw [pw_pw]
      congr 1
      push_cast
      ring
    rw [e₁]
    exact veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs (2 * T) (by omega)
  have A₂ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T + 1 : ℕ) : ℤ))),
      VeryAmpleBy X.hom (pw L ((2 * N * T + 1 : ℕ) : ℤ)) a := by
    have e₂ : ((2 * N * T + 1 : ℕ) : ℤ) = 1 + 2 * (N : ℤ) * (T : ℤ) := by
      push_cast
      ring
    rw [e₂]
    exact ⟨m', t', ht'⟩
  obtain ⟨k₁, a₁, h₁⟩ := A₁
  obtain ⟨k₂, a₂, h₂⟩ := A₂
  exact ⟨2 * N * T, Nat.mul_pos (Nat.mul_pos two_pos hN) hT, k₁, a₁, k₂, a₂, h₁, h₂⟩

end GlobalTheory.CompanionTheory.ConsecAmple
