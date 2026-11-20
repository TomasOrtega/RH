import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfThickeningsLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianLiftAmpleBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpPowOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolLiftComplete

/- English proof (translation)
Introduce `K _ _ R₁ _ _ _ _ hc π hπ A _ _ hA P hP r₁ r₂ hs ha hker`. Take `⟨L, hL, hΛ, haL⟩` from `GlobalTheory.PolBundleLoc.exists_ample_root A hA hP r₁ r₂ hs ha`. Establish `hKL : KTriv A L` using `GlobalTheory.KTrivOfLam.kTriv_of_lam_iso (Sp K) A hA P hP hker L hL hΛ`. Use `set I := RingHom.ker π with hI`. Establish `hItop : I ≠ ⊤`.

Introduce `h`. Establish `h1 : (1 : R₁) ∈ I` using `h ▸ Submodule.mem_top`. Rewrite `h1` using `[hI, RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero h1`. Establish `hIc : IsAdicComplete I R₁` using `GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ I (maximalIdeal R₁) (le_maximalIdeal hItop) hc`.

Establish `hne : ∀ e : ℕ, I ^ (e + 1) ≠ ⊤` using `fun e h => hItop (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))`. Use `haveI hnt : ∀ e : ℕ, Nontrivial (R₁ ⧸ I ^ (e + 1)) := fun e => Ideal.Quotient.nontrivial_iff.2 (hne e)`. Use `haveI hloc : ∀ e : ℕ, IsLocalRing (R₁ ⧸ I ^ (e + 1)) := fun e => IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Set `St : ℕ → Type 1` to `fun e => Σ Y : Over (Sp (R₁ ⧸ I ^ (e + 1))), Σ _ : GrpObj Y, {L : LB Y.left // IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L}`. Establish `hstep : ∀ (e : ℕ) (y : St e), ∃ (y' : St (e + 1)) (i : y.1.left ⟶ y'.1.left), @IsGrpPullback _ _ y.1 y.2.1 y'.1 y'.2.1 (thickTrans R₁ I e) i ∧ LBIso y.2.2.1 (y'.2.2.1.pull i)`.

Introduce and unpack `e ⟨Y, g, L, hA, hL, ha, hK⟩`. Take `⟨Y', g', L', i, hA', hL', ha', hK', hi, hLi⟩` from `GlobalTheory.SqStep.exists_lift (R₁ ⧸ I ^ (e + 1 + 1)) (R₁ ⧸ I ^ (e + 1)) (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))) (Ideal.Quotient.factor_surjective _) (GlobalTheory.MumLift.ker_factor_sq I e) Y hA L hL ha hK`. Conclude with `⟨⟨Y', g', L', hA', hL', ha', hK'⟩, i, hi, hLi⟩`. Use `choose nx β hβ hLβ using hstep`. Set `e₀ : R₁ ⧸ I ^ (0 + 1) ≃+* K` to `(Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).trans (RingHom.quotientKerEquivOfSurjective hπ)`.

Set `s : Sp (R₁ ⧸ I ^ (0 + 1)) ⟶ Sp K` to `spMap (e₀.symm : K →+* R₁ ⧸ I ^ (0 + 1))`. Set `t : Sp K ⟶ Sp (R₁ ⧸ I ^ (0 + 1))` to `spMap (e₀ : R₁ ⧸ I ^ (0 + 1) →+* K)`. Establish `hts : t ≫ s = 𝟙 _`. Simplify using `only [t, s, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Rewrite using `[RingEquiv.comp_symm]`.

Simplify using the standard rewrite rules. Establish `htπ : t ≫ thick R₁ I 0 = spMap π`. Simplify using `only [t, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Set `Y₀ : Over (Sp (R₁ ⧸ I ^ (0 + 1)))` to `(Over.pullback s).obj A`.

Set `g₀ : Y₀.left ⟶ A.left` to `pullback.fst A.hom s`. Establish `G₀ : IsGrpPullback Y₀ A s g₀` using `isGrpPullback_pullback A s`. Establish `hL₀ : (L.pull g₀).IsLB` using `pull_isLB hL g₀`. Establish `hA₀ : IsAbelianScheme Y₀` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA G₀`. Use `haveI := hA.proper`.

Establish `ha₀ : RelAmple Y₀ (L.pull g₀)` using `GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL haL G₀.1`. Establish `hK₀ : KTriv Y₀ (L.pull g₀)`. Take `⟨w, hw⟩ : LBIso (L.pull g₀) (L.pull g₀)` from `(GlobalTheory.CechPic.cls_eq_iff hL₀ hL₀).1 rfl`. Conclude with `kTriv_pull G₀ hL hL₀ ((isGen_iff w).1 hw) hKL`. Set `y₀ : St 0` to `⟨Y₀, inferInstance, L.pull g₀, hA₀, hL₀, ha₀, hK₀⟩`.

Set `Y : ∀ n : ℕ, St n` to `fun n => Nat.rec (motive := fun n => St n) y₀ (fun n y => nx n y) n`. Use `letI : ∀ e, GrpObj (Y e).1 := fun e => (Y e).2.1`. Take `⟨B, _, M, b, hB, hM, haM, hb, -, hiso⟩` from `GlobalTheory.AlgGroup.exists_abelianScheme_of_tower R₁ I hItop hIc hc (fun e => (Y e).1) (fun e => β e (Y e)) (fun e => (Y e).2.2.2.1) (fun e => hβ e (Y e)) (fun e => (Y e).2.2.1) (fun e => (Y e).2.2.2.2.1) (fun e => hLβ e (Y e)) (Y 0).2.2.2.2.2.1`. Use `haveI : IsCommMonObj B := hB.comm`. Set `φ : A.left ⟶ Y₀.left` to `pullback.lift (𝟙 _) (A.hom ≫ t) (by rw [Category.id_comp, Category.assoc, hts, Category.comp_id])`.

Establish `hφ₁ : φ ≫ g₀ = 𝟙 _` using `pullback.lift_fst _ _ _`. Establish `hφ₂ : φ ≫ Y₀.hom = A.hom ≫ t` using `pullback.lift_snd _ _ _`. Use `haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))`. Establish `n₀ : IsGrpPullback A A (t ≫ s) (φ ≫ g₀)` using `(isGrpPullback_of_iso (Iso.refl A)).congr hts.symm hφ₁.symm`. Establish `hcan : IsGrpPullback A Y₀ t φ` using `IsGrpPullback.cancel G₀ n₀ hφ₂`.

Establish `hi : IsGrpPullback A B (spMap π) (φ ≫ b 0)` using `(hcan.comp (hb 0)).congr htπ rfl`. Establish `hLi : LBIso L (M.pull (φ ≫ b 0))`. Use `(GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hM _)).1 ?_` and prove the remaining obligations. Establish `a₂ : GlobalTheory.CechPic.cls _ hL₀ = GlobalTheory.CechPic.cls _ (pull_isLB hM (b 0))` using `(GlobalTheory.CechPic.cls_eq_iff _ _).2 (hiso 0)`. Rewrite using `[GlobalTheory.CechPic.cls_pull hM, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hM (b 0) (pull_isLB hM (b 0)), ← a₂, GlobalTheory.CechPic.cls_pull hL, ← GlobalTheory.CechPic.pull_comp, hφ₁, GlobalTheory.CechPic.pull_id]`.

Establish `hJ : I ^ (0 + 1) ≤ Ideal.jacobson ⊥` using `(Ideal.pow_le_self (Nat.succ_ne_zero 0)).trans (IsAdicComplete.le_jacobson_bot I)`. Establish `hK : KTriv B M` using `GlobalTheory.KTrivJacobson.kTriv_of_quotient R₁ (I ^ (0 + 1)) hJ B hB M hM haM Y₀ (b 0) (hb 0) _ hL₀ (hiso 0) hK₀`. Establish `hPf` using `GlobalTheory.AbDual.isPerfect_lam hM hK`. Establish `hr : Out.Rigidified B M` using `GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₁) (pull_isLB hM _)`. Establish `hΘ` using `GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hM`.

Establish `w : (φ ≫ b 0) ≫ B.hom = A.hom ≫ spMap π` using `hi.1.w`. Establish `sq` using `GlobalTheory.LamPull.exists_isSquare w`. Establish `hlamA : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `hlamB : (abelian₂ B M).IsLB` using `LB.isLB_linComb hM _ _`. Use `⟨B, inferInstance, hB.comm, φ ≫ b 0, _, abelian₂ B M, hB, hi, sq, hPf.isLB, hPf.zero_left, hPf.zero_right, GlobalTheory.FullSiegel.lam_symm hM, GlobalTheory.EighthPowerLocal.relAmple_diag_lam hB hM hΘ haM, fun T x h => GlobalTheory.FullSiegel.eq_one_of_lam_triv hM hr hK T x h, ?_ …` and prove the remaining obligations.

Conclude with `LBIso.trans hP hlamA (pull_isLB hlamB _) (LBIso.symm hΛ) (GlobalTheory.LamPull.lbIso_lam_pull hi hM hL hLi sq)`.
-/
theorem exists_lift : ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (π : V →+* K), Function.Surjective π → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) → ∃ (AV : Over (Sp V)) (_ : GrpObj AV) (_ : IsCommMonObj AV) (φ : A.left ⟶ AV.left) (φ₂ : (G2 A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV ∧ IsGrpPullback A AV (spMap π) φ ∧ IsSquare φ φ₂ ∧ PV.IsLB ∧ (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) ∧ (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) ∧ LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) ∧ Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) ∧ (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) ∧ LBIso P (PV.pull φ₂) := by
  intro K _ _ R₁ _ _ _ _ hc π hπ A _ _ hA P hP r₁ r₂ hs ha hker
  obtain ⟨L, hL, hΛ, haL⟩ := GlobalTheory.PolBundleLoc.exists_ample_root A hA hP r₁ r₂ hs ha
  have hKL : KTriv A L := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso (Sp K) A hA P hP hker L hL hΛ
  set I := RingHom.ker π with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R₁) ∈ I := h ▸ Submodule.mem_top
    rw [hI, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hIc : IsAdicComplete I R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ I (maximalIdeal R₁) (le_maximalIdeal hItop) hc
  have hne : ∀ e : ℕ, I ^ (e + 1) ≠ ⊤ := fun e h =>
    hItop (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI hnt : ∀ e : ℕ, Nontrivial (R₁ ⧸ I ^ (e + 1)) := fun e => Ideal.Quotient.nontrivial_iff.2 (hne e)
  haveI hloc : ∀ e : ℕ, IsLocalRing (R₁ ⧸ I ^ (e + 1)) := fun e =>
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let St : ℕ → Type 1 := fun e => Σ Y : Over (Sp (R₁ ⧸ I ^ (e + 1))), Σ _ : GrpObj Y,
    {L : LB Y.left // IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L}
  have hstep : ∀ (e : ℕ) (y : St e), ∃ (y' : St (e + 1)) (i : y.1.left ⟶ y'.1.left),
      @IsGrpPullback _ _ y.1 y.2.1 y'.1 y'.2.1 (thickTrans R₁ I e) i ∧ LBIso y.2.2.1 (y'.2.2.1.pull i) := by
    rintro e ⟨Y, g, L, hA, hL, ha, hK⟩
    obtain ⟨Y', g', L', i, hA', hL', ha', hK', hi, hLi⟩ := GlobalTheory.SqStep.exists_lift (R₁ ⧸ I ^ (e + 1 + 1))
      (R₁ ⧸ I ^ (e + 1))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))
      (Ideal.Quotient.factor_surjective _) (GlobalTheory.MumLift.ker_factor_sq I e) Y hA L hL ha hK
    exact ⟨⟨Y', g', L', hA', hL', ha', hK'⟩, i, hi, hLi⟩
  choose nx β hβ hLβ using hstep
  let e₀ : R₁ ⧸ I ^ (0 + 1) ≃+* K :=
    (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let s : Sp (R₁ ⧸ I ^ (0 + 1)) ⟶ Sp K := spMap (e₀.symm : K →+* R₁ ⧸ I ^ (0 + 1))
  let t : Sp K ⟶ Sp (R₁ ⧸ I ^ (0 + 1)) := spMap (e₀ : R₁ ⧸ I ^ (0 + 1) →+* K)
  have hts : t ≫ s = 𝟙 _ := by
    simp only [t, s, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [RingEquiv.comp_symm]
    simp
  have htπ : t ≫ thick R₁ I 0 = spMap π := by
    simp only [t, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let Y₀ : Over (Sp (R₁ ⧸ I ^ (0 + 1))) := (Over.pullback s).obj A
  let g₀ : Y₀.left ⟶ A.left := pullback.fst A.hom s
  have G₀ : IsGrpPullback Y₀ A s g₀ := isGrpPullback_pullback A s
  have hL₀ : (L.pull g₀).IsLB := pull_isLB hL g₀
  have hA₀ : IsAbelianScheme Y₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA G₀
  haveI := hA.proper
  have ha₀ : RelAmple Y₀ (L.pull g₀) := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL haL G₀.1
  have hK₀ : KTriv Y₀ (L.pull g₀) := by
    obtain ⟨w, hw⟩ : LBIso (L.pull g₀) (L.pull g₀) := (GlobalTheory.CechPic.cls_eq_iff hL₀ hL₀).1 rfl
    exact kTriv_pull G₀ hL hL₀ ((isGen_iff w).1 hw) hKL
  let y₀ : St 0 := ⟨Y₀, inferInstance, L.pull g₀, hA₀, hL₀, ha₀, hK₀⟩
  let Y : ∀ n : ℕ, St n := fun n => Nat.rec (motive := fun n => St n) y₀ (fun n y => nx n y) n
  letI : ∀ e, GrpObj (Y e).1 := fun e => (Y e).2.1
  obtain ⟨B, _, M, b, hB, hM, haM, hb, -, hiso⟩ := GlobalTheory.AlgGroup.exists_abelianScheme_of_tower R₁ I hItop hIc hc
    (fun e => (Y e).1) (fun e => β e (Y e)) (fun e => (Y e).2.2.2.1) (fun e => hβ e (Y e))
    (fun e => (Y e).2.2.1) (fun e => (Y e).2.2.2.2.1) (fun e => hLβ e (Y e)) (Y 0).2.2.2.2.2.1
  haveI : IsCommMonObj B := hB.comm
  let φ : A.left ⟶ Y₀.left := pullback.lift (𝟙 _) (A.hom ≫ t)
    (by rw [Category.id_comp, Category.assoc, hts, Category.comp_id])
  have hφ₁ : φ ≫ g₀ = 𝟙 _ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ Y₀.hom = A.hom ≫ t := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  have n₀ : IsGrpPullback A A (t ≫ s) (φ ≫ g₀) :=
    (isGrpPullback_of_iso (Iso.refl A)).congr hts.symm hφ₁.symm
  have hcan : IsGrpPullback A Y₀ t φ := IsGrpPullback.cancel G₀ n₀ hφ₂
  have hi : IsGrpPullback A B (spMap π) (φ ≫ b 0) := (hcan.comp (hb 0)).congr htπ rfl
  have hLi : LBIso L (M.pull (φ ≫ b 0)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hM _)).1 ?_
    have a₂ : GlobalTheory.CechPic.cls _ hL₀ = GlobalTheory.CechPic.cls _ (pull_isLB hM (b 0)) :=
      (GlobalTheory.CechPic.cls_eq_iff _ _).2 (hiso 0)
    rw [GlobalTheory.CechPic.cls_pull hM, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hM (b 0) (pull_isLB hM (b 0)), ← a₂,
      GlobalTheory.CechPic.cls_pull hL, ← GlobalTheory.CechPic.pull_comp, hφ₁, GlobalTheory.CechPic.pull_id]
  have hJ : I ^ (0 + 1) ≤ Ideal.jacobson ⊥ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero 0)).trans (IsAdicComplete.le_jacobson_bot I)
  have hK : KTriv B M :=
    GlobalTheory.KTrivJacobson.kTriv_of_quotient R₁ (I ^ (0 + 1)) hJ B hB M hM haM Y₀ (b 0) (hb 0) _ hL₀ (hiso 0) hK₀
  have hPf := GlobalTheory.AbDual.isPerfect_lam hM hK
  have hr : Out.Rigidified B M := GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₁) (pull_isLB hM _)
  have hΘ := GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hM
  have w : (φ ≫ b 0) ≫ B.hom = A.hom ≫ spMap π := hi.1.w
  have sq := GlobalTheory.LamPull.exists_isSquare w
  have hlamA : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hlamB : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  refine ⟨B, inferInstance, hB.comm, φ ≫ b 0, _, abelian₂ B M, hB, hi, sq, hPf.isLB, hPf.zero_left, hPf.zero_right,
    GlobalTheory.FullSiegel.lam_symm hM, GlobalTheory.EighthPowerLocal.relAmple_diag_lam hB hM hΘ haM,
    fun T x h => GlobalTheory.FullSiegel.eq_one_of_lam_triv hM hr hK T x h, ?_⟩
  exact LBIso.trans hP hlamA (pull_isLB hlamB _) (LBIso.symm hΛ)
    (GlobalTheory.LamPull.lbIso_lam_pull hi hM hL hLi sq)

end GlobalTheory.PolLiftComplete
