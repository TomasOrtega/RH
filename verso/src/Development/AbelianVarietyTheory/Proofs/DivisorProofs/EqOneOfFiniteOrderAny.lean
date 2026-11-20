import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeckeOperatorMultiplicativeOnSectionProducts
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegrees
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfFiniteOrderOfFixThreeTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsInducedTranslationFrobeniusOnSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImage
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.TorsionAnyChar

def AnyU (p : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G],
    Unif I D A G → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif I D A G, p U

def AnyUF (p : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G],
    Unif I D A G → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], Prop) : Prop :=
  AnyU fun {R} _ _ {_} {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], p U F

def AnyD (p : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}, DegData R I →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], p D F

section
open GlobalTheory.TorusExt

/- English proof (translation)
Introduce `hL R _ _ I hA D F _ _ _`. Use `⟨exists_lift, fun n hn g => ?_, fun t => ?_, fun g hb => ?_, fun t t' g g' g'' h h' => ?_⟩` and prove the remaining obligations. Use `letI := gtGroup D.toPre F`. Conclude with `(exists_nsmul_eq hL.1.mulN (Or.inl hA.1) (by omega) g).imp fun _ e => (isNsmul_iff_eq _ _ _).2 e.symm`. Conclude with `⟨_, (isTor_iff _ _).2 (isTorusPtF_torusPt t), fun g h => (isTorusPtF_iff_eq g t).1 ((isTor_iff _ _).1 h)⟩`.

Take `⟨t, ht⟩` from `exists_isTorusPtF_of_b hb`. Use `⟨t, (isTor_iff _ _).2 ht, fun t' ht' => MonoidHom.ext fun χ => Units.ext ?_⟩` and prove the remaining obligations. Conclude with `congrFun (((isTor_iff _ _).1 ht').fun_unique ht) χ.toAdd`. Use `letI := gtGroup D.toPre F`. Establish `a` using `((isTor_iff _ _).1 h).add ((isTor_iff _ _).1 h')`.

Rewrite using `[isTor_iff]`. Conclude with `(isAdd_iff_eq _ _ _).trans ⟨fun e => e ▸ a, fun e => e.unique a⟩`.
-/
theorem gtOnto_any : LL → AnyD fun {R} _ _ {I} D F _ _ => (∀ b : TF (R := R) F ⟶ D.toPre.P.A, ∃ g : GtPtF D.toPre F, g.b = b) ∧ (∀ n, 1 ≤ n → ∀ g : GtPtF D.toPre F, ∃ g', GtPtF.IsNsmul n g' g) ∧ (∀ t, ∃! g : GtPtF D.toPre F, IsTor t g) ∧ (∀ g : GtPtF D.toPre F, g.b = 1 → ∃! t, IsTor t g) ∧ ∀ t t' (g g' g'' : GtPtF D.toPre F), IsTor t g → IsTor t' g' → (g.IsAdd g' g'' ↔ IsTor (t * t') g'') := by
  intro hL R _ _ I hA D F _ _ _
  refine ⟨exists_lift, fun n hn g => ?_, fun t => ?_, fun g hb => ?_, fun t t' g g' g'' h h' => ?_⟩
  · letI := gtGroup D.toPre F
    exact (exists_nsmul_eq hL.1.mulN (Or.inl hA.1) (by omega) g).imp fun _ e => (isNsmul_iff_eq _ _ _).2 e.symm
  · exact ⟨_, (isTor_iff _ _).2 (isTorusPtF_torusPt t), fun g h => (isTorusPtF_iff_eq g t).1 ((isTor_iff _ _).1 h)⟩
  · obtain ⟨t, ht⟩ := exists_isTorusPtF_of_b hb
    refine ⟨t, (isTor_iff _ _).2 ht, fun t' ht' => MonoidHom.ext fun χ => Units.ext ?_⟩
    exact congrFun (((isTor_iff _ _).1 ht').fun_unique ht) χ.toAdd
  · letI := gtGroup D.toPre F
    have a := ((isTor_iff _ _).1 h).add ((isTor_iff _ _).1 h')
    rw [isTor_iff]
    exact (isAdd_iff_eq _ _ _).trans ⟨fun e => e ▸ a, fun e => e.unique a⟩

end

section
open GlobalTheory.UT.CoefDet

/- English proof (translation)
Introduce `hL R _ _ I hA D F _ _ _ k s s' H`. Establish `hsm` using `D.toPre.P.isAb.smooth`. Set `p : (DegPre.BF D.toPre F).left ⟶ Spec (CommRingCat.of F)` to `(fst (TF (R := R) F) D.toPre.P.A).left`. Establish `hp : Smooth p` using `inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.toPre.P.A.hom))`. Establish `: IsReduced (DegPre.BF D.toPre F).left` using `GlobalTheory.isReduced_of_smooth_of_isReduced p`.

Use `fam_ext fun χ j => fn_ext_of_points p fun r hr z hz => ?_` and prove the remaining obligations. Set `r' : TF (R` to `R) F ⟶ DegPre.BF D.toPre F := Over.homMk r (by`. Rewrite using `[← Over.w (fst (TF (R := R) F) D.toPre.P.A), ← Category.assoc]`. Conclude with `(congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))`. Take `⟨g, hg⟩` from `(gtOnto_any hL R I hA D F).1 (r' ≫ snd _ _)`.

Establish `er : lift (𝟙 (TF (R` using `R) F)) g.b = r' := by`. Rewrite using `[hg]`. Use `CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)` and prove the remaining obligations. Rewrite using `[lift_fst]`. Conclude with `Over.OverMorphism.ext hr.symm`.

Take `⟨w, hw, hc⟩` from `H g`. Take `⟨J, hJ⟩` from `CoefBasic.exists_good' (Z := (TF (R := R) F).left) D.toPre.P.isLB z`. Establish `a` using `CoefBasic.isCoef_coef g hw χ s z J hJ`. Establish `a'` using `CoefBasic.isCoef_coef g hw χ s' z J hJ`. Rewrite `a` using `[hc χ, a', Units.mul_left_inj, Units.mul_left_inj, er]`.

Conclude with `(sec_trans (s.s χ) r z hz (hJ.mem _ r)).trans ((congrArg _ a.symm).trans (sec_trans (s'.s χ) r z hz (hJ.mem _ r)).symm)`.
-/
theorem famEq_any : LL → AnyD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (s s' : Fam D.toPre F k), (∀ g : GtPtF D.toPre F, ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ ∀ χ, coef s g w χ = coef s' g w χ) → s = s' := by
  intro hL R _ _ I hA D F _ _ _ k s s' H
  have hsm := D.toPre.P.isAb.smooth
  let p : (DegPre.BF D.toPre F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.toPre.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.toPre.P.A.hom))
  have : IsReduced (DegPre.BF D.toPre F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine fam_ext fun χ j => fn_ext_of_points p fun r hr z hz => ?_
  let r' : TF (R := R) F ⟶ DegPre.BF D.toPre F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.toPre.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  obtain ⟨g, hg⟩ := (gtOnto_any hL R I hA D F).1 (r' ≫ snd _ _)
  have er : lift (𝟙 (TF (R := R) F)) g.b = r' := by
    rw [hg]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  obtain ⟨w, hw, hc⟩ := H g
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TF (R := R) F).left) D.toPre.P.isLB z
  have a := CoefBasic.isCoef_coef g hw χ s z J hJ
  have a' := CoefBasic.isCoef_coef g hw χ s' z J hJ
  rw [hc χ, a', Units.mul_left_inj, Units.mul_left_inj, er] at a
  exact (sec_trans (s.s χ) r z hz (hJ.mem _ r)).trans ((congrArg _ a.symm).trans
    (sec_trans (s'.s χ) r z hz (hJ.mem _ r)).symm)

end

section
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.CoefPhi

/- English proof (translation)
Introduce `hL R _ _ I _ D F _ _ _ k _ p w hw g₀ g₁ hadd ω₀ h₀`. Take `⟨hb, hs⟩` from `(isAdd_iff _ _ _).1 hadd`. Take `⟨ω₁, h₁, v₁⟩` from `exists_frame p w hw g₀ ω₀ h₀ g₁.b hb`. Use `⟨ω₁, h₁, fun hz ho z J hJ => ?_, ?_⟩` and prove the remaining obligations. Establish `C : IsCub (th D.toPre (T` using `TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ`.

Take `⟨z₁, z₂⟩` from `(isZero_iff _).1 hz`. Establish `c : cubN (th D.toPre z J) k 1 p.g.b g₀.b = 1` using `by rw [z₁, C.N_one]`. Rewrite using `[v₁ z J hJ, ho.2 z J hJ, z₂ _ z J hJ, c, _root_.one_mul, _root_.mul_one, _root_.mul_one]`. Introduce and unpack `n _ _ rfl ⟨qy, qg, qe⟩ hy hg wN w₀ w₁ ⟨hN, vN⟩ ⟨-, v₀⟩ ⟨hw₁, vw₁⟩ s s' hΦ α dsimp only at hy hg`. Substitute `hy hg` using the available equality.

Establish `H` using `(phiRel_iff hL.1.globalFns _ wN hN s s').1 hΦ`. Use `coef_eq fun z J hJ => ?_` and prove the remaining obligations. Establish `C : IsCub (th D.toPre (T` using `TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ`. Establish `e₁` using `H α _ rfl _ (lift (𝟙 (TF (R := R) F)) g₀.b) z J hJ`. Establish `t : lift (𝟙 (TF (R` using `R) F)) g₀.b ≫ DegPre.trPt D.toPre F p.g.b = lift (𝟙 (TF (R := R) F)) g₁.b := by`.

Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, tr_fst, lift_fst, lift_fst]`. Rewrite using `[lift_snd, hb, Category.assoc]`. Use `(congrArg (_ ≫ ·) (tr_pr D.toPre F p.g.b)).trans ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]`.

Simplify using `only at e₁ vN`. Rewrite `e₁` using `[t, uVal, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp, Over.id_left, val_mul hJ, vN z J hJ, CoefPhi.cubN_mul C]`. Establish `e₂` using `gt_nsmul (𝟙 (TF (R := R) F)) hJ g₀ α p.y n`. Rewrite `e₂` using `[Category.id_comp, Over.id_left, cPoint_y]`. Establish `e₃` using `hs α z J hJ`.

Rewrite using `[isCoef_coef g₁ hw₁ α s z J hJ]`. Simplify using `only`. Rewrite using `[e₁, v₀ z J hJ, vw₁ z J hJ, v₁ z J hJ]`. Simplify using `only [_root_.mul_assoc, ← Units.val_mul]`. Use `congr 2`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₂` using `congrArg Additive.ofMul e₂`. Establish `a₃` using `congrArg Additive.ofMul e₃`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢`. Take the linear combination `(norm := module) a₃ - a₂`.
-/
theorem coefPhi_any : LL → AnyD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (g₀ g₁ : GtPtF D.toPre F), g₀.IsAdd p.g g₁ → ∀ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen → ∃ ω₁ : Frm D.toPre F k g₁.b, ω₁.IsGen ∧ (g₀.IsZero → FrmOne ω₀ → ∀ z J, Good D.toPre.P.L z J → val ω₁ (𝟙 _) z J = val w (𝟙 _) z J) ∧ ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → ∀ (wN : Frm D.toPre F N q.g.b) (w₀ : Frm D.toPre F N g₀.b) (w₁ : Frm D.toPre F N g₁.b), (wN.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val wN (𝟙 _) z J = val w (𝟙 _) z J ^ n) → (w₀.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₀ (𝟙 _) z J = val ω₀ (𝟙 _) z J ^ n) → (w₁.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J = val ω₁ (𝟙 _) z J ^ n) → ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N q wN s s' → ∀ α, coef s' g₀ w₀ (α + q.y) = coef s g₁ w₁ α := by
  intro hL R _ _ I _ D F _ _ _ k _ p w hw g₀ g₁ hadd ω₀ h₀
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ω₁, h₁, v₁⟩ := exists_frame p w hw g₀ ω₀ h₀ g₁.b hb
  refine ⟨ω₁, h₁, fun hz ho z J hJ => ?_, ?_⟩
  · have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 hz
    have c : cubN (th D.toPre z J) k 1 p.g.b g₀.b = 1 := by rw [z₁, C.N_one]
    rw [v₁ z J hJ, ho.2 z J hJ, z₂ _ z J hJ, c, _root_.one_mul, _root_.mul_one, _root_.mul_one]
  · rintro n _ _ rfl ⟨qy, qg, qe⟩ hy hg wN w₀ w₁ ⟨hN, vN⟩ ⟨-, v₀⟩ ⟨hw₁, vw₁⟩ s s' hΦ α
    dsimp only at hy hg
    subst hy hg
    have H := (phiRel_iff hL.1.globalFns _ wN hN s s').1 hΦ
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    have e₁ := H α _ rfl _ (lift (𝟙 (TF (R := R) F)) g₀.b) z J hJ
    have t : lift (𝟙 (TF (R := R) F)) g₀.b ≫ DegPre.trPt D.toPre F p.g.b = lift (𝟙 (TF (R := R) F)) g₁.b := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
      · rw [lift_snd, hb, Category.assoc]
        refine (congrArg (_ ≫ ·) (tr_pr D.toPre F p.g.b)).trans ?_
        rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
    dsimp only at e₁ vN
    rw [t, uVal, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp, Over.id_left, val_mul hJ, vN z J hJ,
      CoefPhi.cubN_mul C] at e₁
    have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g₀ α p.y n
    rw [Category.id_comp, Over.id_left, cPoint_y] at e₂
    have e₃ := hs α z J hJ
    rw [isCoef_coef g₁ hw₁ α s z J hJ]
    dsimp only
    rw [e₁, v₀ z J hJ, vw₁ z J hJ, v₁ z J hJ]
    simp only [_root_.mul_assoc, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂

end

section
open GlobalTheory.UT.PhiProj

/- English proof (translation)
Introduce `hL R _ _ I _ D F _ _ _ k hk`. Establish `hG : GlobalFnsSt` using `hL.1.globalFns`. Establish `ex : ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), ∃ Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k, w.IsGen → ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s` using `fun p w => by`. Distinguish the cases in `hw : w.IsGen`. Take `⟨Φ, h⟩` from `phiFun_of_globalFns hG R I D F k hk p w hw`.

Conclude with `⟨Φ, fun _ => h⟩`. Conclude with `⟨0, fun h => (hw h).elim⟩`. Use `choose Φ hΦ using ex`. Establish `rel : ∀ p w, w.IsGen → ∀ s, PhiRel D.toPre F k p w s (Φ p w s)` using `fun p w hw s => (hΦ p w hw s _).2 rfl`. Use `⟨Φ, fun p w hw => ⟨?_, hΦ p w hw⟩, fun p w hw c hc => ?_, fun p w w' hw hw' => ?_, fun p p' w hw he => ?_, fun p p' p'' w w' hw hw' hadd => ?_, fun p w hy hg hw => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc, hcs⟩` from `H1.phiPow_core hG p w hw`. Use `bijective_of_pow (Φ p w) hk hc fun s => ?_` and prove the remaining obligations. Establish `h` using `hcs (fun i => (Φ p w ^ (i : ℕ)) s) (fun i => by`. Rewrite using `[hΦ p w hw]`. Simplify using `only [Fin.val_succ, Fin.val_castSucc, pow_succ', Module.End.mul_apply])`.

Rewrite `h` using `[isSmul_iff]`. Simplify `h` using `only [Fin.val_last, Fin.val_zero, pow_zero, Module.End.one_apply]`. Take `⟨w', hw', hv⟩` from `exists_scaled hw c hc`. Conclude with `⟨w', hw', LinearMap.ext fun s => ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩`. Take `⟨c, hc, hv⟩` from `CoefBasic.exists_frame_ratio hw hw'`.

Conclude with `⟨c, hc, LinearMap.ext fun s => ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩`. Take `⟨w', hw', h⟩` from `phiRel_of_equiv hG he hw`. Conclude with `⟨w', hw', LinearMap.ext fun s => ((hΦ p' w' hw' s _).1 (h s _ (rel p w hw s))).symm⟩`. Take `⟨q, hy, hg, he⟩` from `hadd`. Take `⟨w₂, hw₂, h₂⟩` from `GlobalTheory.ThetaMul.phi_mul_core hG p p' q hy hg w w' hw hw'`.

Take `⟨w'', hw'', h⟩` from `phiRel_of_equiv hG he hw₂`. Conclude with `⟨w'', hw'', LinearMap.ext fun s => ((hΦ p'' w'' hw'' s _).1 (h s _ (h₂ s _ _ (rel p' w' hw' s) (rel p w hw _)))).symm⟩`. Conclude with `LinearMap.ext fun s => ((hΦ p w hw.1 s s).1 (phiRel_zero hG p w hy hg hw s)).symm`.
-/
theorem phiProj_any : LL → AnyD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ Φ : ∀ (p : QkPt D.toPre F k), Frm D.toPre F k p.g.b → (Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ p w, w.IsGen → Function.Bijective (Φ p w) ∧ ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ p w s) ∧ (∀ p w, w.IsGen → ∀ c : F, c ≠ 0 → ∃ w', w'.IsGen ∧ Φ p w' = c • Φ p w) ∧ (∀ p w w', w.IsGen → w'.IsGen → ∃ c : F, c ≠ 0 ∧ Φ p w' = c • Φ p w) ∧ (∀ p p' w, w.IsGen → QkPt.Equiv D.toPre F p p' → ∃ w', w'.IsGen ∧ Φ p' w' = Φ p w) ∧ (∀ p p' p'' w w', w.IsGen → w'.IsGen → QkAdd p p' p'' → ∃ w'', w''.IsGen ∧ Φ p'' w'' = Φ p w ∘ₗ Φ p' w') ∧ ∀ p w, p.y = 0 → p.g.IsZero → FrmOne w → Φ p w = LinearMap.id := by
  intro hL R _ _ I _ D F _ _ _ k hk
  have hG : GlobalFnsSt := hL.1.globalFns
  have ex : ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), ∃ Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k,
      w.IsGen → ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s := fun p w => by
    by_cases hw : w.IsGen
    · obtain ⟨Φ, h⟩ := phiFun_of_globalFns hG R I D F k hk p w hw
      exact ⟨Φ, fun _ => h⟩
    · exact ⟨0, fun h => (hw h).elim⟩
  choose Φ hΦ using ex
  have rel : ∀ p w, w.IsGen → ∀ s, PhiRel D.toPre F k p w s (Φ p w s) := fun p w hw s => (hΦ p w hw s _).2 rfl
  refine ⟨Φ, fun p w hw => ⟨?_, hΦ p w hw⟩, fun p w hw c hc => ?_, fun p w w' hw hw' => ?_,
    fun p p' w hw he => ?_, fun p p' p'' w w' hw hw' hadd => ?_, fun p w hy hg hw => ?_⟩
  · obtain ⟨c, hc, hcs⟩ := H1.phiPow_core hG p w hw
    refine bijective_of_pow (Φ p w) hk hc fun s => ?_
    have h := hcs (fun i => (Φ p w ^ (i : ℕ)) s) (fun i => by
      rw [hΦ p w hw]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at h
    simpa only [Fin.val_last, Fin.val_zero, pow_zero, Module.End.one_apply] using h
  · obtain ⟨w', hw', hv⟩ := exists_scaled hw c hc
    exact ⟨w', hw', LinearMap.ext fun s =>
      ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩
  · obtain ⟨c, hc, hv⟩ := CoefBasic.exists_frame_ratio hw hw'
    exact ⟨c, hc, LinearMap.ext fun s =>
      ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩
  · obtain ⟨w', hw', h⟩ := phiRel_of_equiv hG he hw
    exact ⟨w', hw', LinearMap.ext fun s => ((hΦ p' w' hw' s _).1 (h s _ (rel p w hw s))).symm⟩
  · obtain ⟨q, hy, hg, he⟩ := hadd
    obtain ⟨w₂, hw₂, h₂⟩ := GlobalTheory.ThetaMul.phi_mul_core hG p p' q hy hg w w' hw hw'
    obtain ⟨w'', hw'', h⟩ := phiRel_of_equiv hG he hw₂
    exact ⟨w'', hw'', LinearMap.ext fun s =>
      ((hΦ p'' w'' hw'' s _).1 (h s _ (h₂ s _ _ (rel p' w' hw' s) (rel p w hw _)))).symm⟩
  · exact LinearMap.ext fun s => ((hΦ p w hw.1 s s).1 (phiRel_zero hG p w hy hg hw s)).symm

end

section

/- English proof (translation)
Introduce `hL R _ _ I _ D A G _ _ _ U`. Use `⟨GlobalTheory.expansion_bijective_over_fields hL.1.globalFns R I D A G U, ?_⟩` and prove the remaining obligations. Introduce `F _ _ k w₀ t t' t'' s s' c h h' e`. Establish `key` using `GlobalTheory.FieldBaseChange.expandsF_lin U.toUnifPre F c h h'`. Establish `ext : ∀ a b : SecA A F k, (∀ j, a.f j = b.f j) → a = b`.

Introduce and unpack `⟨a, _⟩ ⟨b, _⟩ hab`. Take `rfl : a = b` from `funext hab`. Both sides reduce to the same expression. Conclude with `(congrArg (fun x : SecA A F k => U.ExpandsF F k w₀ x (c • s + s')) (ext t'' _ fun j => (e j).trans rfl)).mpr key`.
-/
theorem expBijF_any : LL → AnyU fun {R} _ _ {I} {D} {A} {G} _ _ U => ExpBijF U.toUnifPre ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (w₀ : W0 U.toUnifPre) (t t' t'' : SecA A F k) (s s' : Fam D.toPre F k) (c : F), U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀ t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → U.ExpandsF F k w₀ t'' (c • s + s') := by
  intro hL R _ _ I _ D A G _ _ _ U
  refine ⟨GlobalTheory.expansion_bijective_over_fields hL.1.globalFns R I D A G U, ?_⟩
  intro F _ _ k w₀ t t' t'' s s' c h h' e
  have key := GlobalTheory.FieldBaseChange.expandsF_lin U.toUnifPre F c h h'
  have ext : ∀ a b : SecA A F k, (∀ j, a.f j = b.f j) → a = b := by
    rintro ⟨a, _⟩ ⟨b, _⟩ hab
    obtain rfl : a = b := funext hab
    rfl
  exact (congrArg (fun x : SecA A F k => U.ExpandsF F k w₀ x (c • s + s')) (ext t'' _ fun j => (e j).trans rfl)).mpr key

end

section
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.SecAdicSum

/- English proof (translation)
Introduce `_ R _ _ I hR D F _ _ _ K _ φ ε Ix n n₀ hS b τ _ x x₀ hx`. Use `hR.1` as an intermediate fact. Use `D.toPre.P.isAb.smooth` as an intermediate fact. Establish `hL` using `D.toPre.P.isLB`. Take `⟨P⟩` from `GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)`.

Use `choose v hv hv' using fun i => exists_vec P (n i)`. Take `⟨v₀, hv₀, hv₀'⟩` from `exists_vec P n₀`. Take `⟨z⟩` from `CoefBasic.exists_pt (R := R) (F := F)`. Take `⟨J, hJ⟩` from `CoefBasic.exists_good' hL z`. Take `⟨i₀, hi₀⟩` from `exists_mem P (b.left z)`.

Set `t` to `trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J`. Use `choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)`. Use `letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))`. Set `ev : (Fin P.a → R) →ₗ[R] F` to `Fintype.linearCombination R y`. Establish `key : ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (w : Fin P.a → R) (c : F), (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) → sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w` using `fun s w c h₁ h₂ => by`.

Establish `e` using `gs_loc₀ P h₁ b.left z hi₀ hJ`. Rewrite `e` using `[h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq]`. Use `CoefBasic.cstH_inj (R := R) z ?_` and prove the remaining obligations. Establish `e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val` using `(Units.eq_mul_inv_iff_mul_eq t).2 e.symm`. Establish `hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k)` using `fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]`.

Rewrite using `[e', loc₀, hs, Finset.sum_mul]`. Use `Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm` and prove the remaining obligations. Rewrite using `[gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]`. Both sides reduce to the same expression. Take `rfl : x = fun i => ev (v i)` from `funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)`.

Take `rfl : x₀ = ev v₀` from `key _ _ _ hv₀' (hx z J hJ).2`. Use `sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_` and prove the remaining obligations. Take `⟨S, hS⟩` from `hS e`. Use `⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]`.

Take `⟨J', hJ'⟩` from `CoefBasic.exists_good' hL p`. Take `⟨h₁, h₂⟩` from `hS _ (𝟙 _) p J' hJ'`. Rewrite `h₁`, `h₂` using `[Category.id_comp]`. Establish `h₃` using `h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)`. Establish `e₀` using `gs_loc₀ P hv₀' _ p hp hJ'`.

Establish `e₁` using `fun j => gs_loc₀ P (hv' j) _ p hp hJ'`. Rewrite `e₀` using `[gs_eq _ p _ hp]`. Simplify using `only [gs_eq _ p _ hp] at e₁`. Rewrite using `[loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j, ← Finset.mul_sum]`. Conclude with `sub_eq_zero.2 (congrArg _ h₃)`.
-/
theorem sumF_any : LL → AnyD fun {R} _ _ {I} D F _ _ => ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (n₀ : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good D.toPre.P.L z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro _ R _ _ I hR D F _ _ _ K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  have hL := D.toPre.P.isLB
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁
    rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
      ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end

section
open GlobalTheory.FieldBaseChange GlobalTheory.UT.ProdConv

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Substitute `hm` using the available equality. Use `choose p hp using fun α β => exists_isProd r k l (add_sub_cancel β α) (f β) (f' (α - β))`. Take `⟨τ, hτ, vτ⟩` from `exists_frame g hw α`. Use `sumF_any hL R I hR D F (Fin 4) (D.toPre.famφB α) (DegPre.famε (k + l)) D.toPre.X (p α) (f'' α) (fun e => level U e r rfl (h e) (h' e) (h'' e) hσ p hp α) g.b τ hτ _ _ fun z J hJ => ⟨fun χ => ?_, ?_⟩` and prove the remaining obligations. Establish `b` using `gt_mul (𝟙 (TF (R := R) F)) hJ g χ (α - χ)`.

Rewrite `b` using `[add_sub_cancel, Category.id_comp, Over.id_left]`. Rewrite using `[hp α χ _ g.b z J hJ, vτ z J hJ, constVal_TF, hww z J hJ, CoefBasic.cst_eq z (_ * _), map_mul, map_mul, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]`. Conclude with `alg_prod _ (hx χ z J hJ) (hx' (α - χ) z J hJ) b`. Rewrite using `[vτ z J hJ]`. Conclude with `alg_term (hx'' z J hJ)`.
-/
theorem point_any [IsAlgClosed F] (hL : LL) (hR : AdmBase R I) {k l m : ℕ} (r : R) {σ : H0 U.LG.L k}
    {σ' : H0 U.LG.L l} {σ'' : H0 U.LG.L m} (hm : m = k + l)
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D.toPre.SecB l α} {f'' : ∀ α, D.toPre.SecB m α}
    (h : ∀ e, U.ExpandsAt e k σ f) (h' : ∀ e, U.ExpandsAt e l σ' f') (h'' : ∀ e, U.ExpandsAt e m σ'' f'')
    (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ G.left) (z : Z) (j), q z ∈ U.LG.L.U j →
      sv U m σ'' q z j = constVal (q ≫ G.hom) z r * (sv U k σ q z j * sv U l σ' q z j))
    (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} {w' : Frm D.toPre F l g.b} {w'' : Frm D.toPre F m g.b}
    (hw : w''.IsGen) (hww : ∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J)
    {x x' : D.toPre.X → F} (hx : ∀ χ, IsTerm g w (f χ) (x χ)) (hx' : ∀ χ, IsTerm g w' (f' χ) (x' χ))
    (α : D.toPre.X) {x'' : F} (hx'' : IsTerm g w'' (f'' α) x'') :
    SumF I F (fun χ => algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) * (x χ * x' (α - χ))) x'' := by
  subst hm
  choose p hp using fun α β => exists_isProd r k l (add_sub_cancel β α) (f β) (f' (α - β))
  obtain ⟨τ, hτ, vτ⟩ := exists_frame g hw α
  refine sumF_any hL R I hR D F (Fin 4) (D.toPre.famφB α) (DegPre.famε (k + l)) D.toPre.X (p α) (f'' α)
    (fun e => level U e r rfl (h e) (h' e) (h'' e) hσ p hp α) g.b τ hτ _ _ fun z J hJ => ⟨fun χ => ?_, ?_⟩
  · have b := gt_mul (𝟙 (TF (R := R) F)) hJ g χ (α - χ)
    rw [add_sub_cancel, Category.id_comp, Over.id_left] at b
    rw [hp α χ _ g.b z J hJ, vτ z J hJ, constVal_TF, hww z J hJ, CoefBasic.cst_eq z (_ * _), map_mul, map_mul,
      ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]
    exact alg_prod _ (hx χ z J hJ) (hx' (α - χ) z J hJ) b
  · rw [vτ z J hJ]
    exact alg_term (hx'' z J hJ)

end

section
open GlobalTheory.FieldBaseChange GlobalTheory.UT.ProdConv

/- English proof (translation)
Introduce `hL R _ _ I hR D A G _ _ _ U F _ _ _ w₀ hw₀ k k' k'' hk hk' hm t t' t'' s s' s'' h h' h'' ht g w w' w'' hw hw' hw'' hww α`. Establish `hG` using `hL.1.globalFns`. Establish `hk'' : 1 ≤ k''` using `by omega`. Take `⟨v, a, b⟩` from `h`. Take `⟨v', a', b'⟩` from `h'`.

Take `⟨v'', a'', b''⟩` from `h''`. Take `⟨n, c, x, hx, e₁, e₂⟩` from `(expandsG_iff U.toUnifPre F k v s).1 b`. Take `⟨n', c', x', hx', e₁', e₂'⟩` from `(expandsG_iff U.toUnifPre F k' v' s').1 b'`. Take `⟨u, hu⟩` from `exists_powMul A.isLB (q := (snd (TFK (R := R) F) A.A).left) hm t t'`. Take `rfl : t'' = u` from `sec_ext' A.isLB fun y J hJ => (ht y J hJ).trans (hu _ (𝟙 _) y _ (hJ (𝟙 _ ≫ _))).symm`.

Use `choose τ hτ using fun p : Fin n × Fin n' => exists_powMul U.LG.isLB (q := 𝟙 G.left) hm (x p.1).1 (x' p.2).1`. Use `choose Φ hΦ using fun p => ((U.expand k'' hk'').1 (genericSec U.toUnifPre k'' (τ p))).exists`. Use `choose r hr y hy d₁ d₂ using fun p => (expands_iff U.toUnifPre k'' _ _).1 (hΦ p)`. Establish `hr' : ∀ p, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)) ≠ 0` using `fun p => by`. Rewrite using `[map_ne_zero]`.

Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hr p)`. Establish `hyτ : ∀ p, (y p).1 = r p • (show IntSec U.toUnifPre k'' from τ p)` using `fun p => genericSec_injective U.toUnifPre k'' ((d₁ p).trans (map_smulₛₗ _ _ _).symm)`. Establish `hv : v'' = (∑ p : Fin n × Fin n', (c p.1 * c' p.2) • extendSec U.toUnifPre F k'' (genericSec U.toUnifPre k'' (τ p)) : GroupSec U.toUnifPre F k'')`. Use `powVal_ext U.LG.isLB fun z i hi => ?_` and prove the remaining obligations. Take `⟨i₁, hi₁⟩` from `exists_chart A.isLB (U.gen.hom.left ((snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left z))`.

Establish `m` using `(isoRelM_iff _ _ _ _ a.1 _ a.2.1 _ _).1 a _ (𝟙 _) z i i₁ hi hi₁`. Establish `m'` using `(isoRelM_iff _ _ _ _ a'.1 _ a'.2.1 _ _).1 a' _ (𝟙 _) z i i₁ hi hi₁`. Establish `m''` using `(isoRelM_iff _ _ _ _ a''.1 _ a''.2.1 _ _).1 a'' _ (𝟙 _) z i i₁ hi hi₁`. Establish `b₁ : (snd (TFK (R` using `R) F) A.A).left ((𝟙 _ ≫ (U.genF F).left) z) ∈ A.L.U i₁ := (congrArg (fun q => q z ∈ A.L.U i₁) a.1).mpr hi₁`. Establish `m₀` using `hu _ _ z i₁ b₁`.

Rewrite `m`, `m'`, `m''` using `[Category.comp_id]`. Establish `w₁` using `(congrArg (fun q => powVal q (𝟙 _) z i) e₁).trans (powVal_comb U.toUnifPre c (fun p => (x p).1) z hi)`. Establish `w₂` using `(congrArg (fun q => powVal q (𝟙 _) z i) e₁').trans (powVal_comb U.toUnifPre c' (fun p => (x' p).1) z hi)`. Use `Eq.trans ?_ (powVal_comb U.toUnifPre _ τ z hi).symm` and prove the remaining obligations. Establish `w₃ : powVal v'' (𝟙 _) z i = powVal v (𝟙 _) z i * powVal v' (𝟙 _) z i`.

Rewrite using `[m, m', m'', m₀, hm, Nat.cast_add, zpow_add, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[w₃, w₁, w₂, Finset.sum_mul_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `cm : constVal (groupBase G F) z (c p * c' q) = constVal (groupBase G F) z (c p) * constVal (groupBase G F) z (c' q)` using `(congrArg (gs _ z ⊤) (map_mul _ _ _)).trans (gs_mul _ z ⊤ trivial _ _)`.

Rewrite using `[hτ (p, q) _ (UnifPre.gFK (G := G) F) z i hi, cm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∀ β, famProj D.toPre F k'' β (∑ p : Fin n × Fin n', (c p.1 * c' p.2) • famPull D.toPre (FractionRing R) F hG k'' (Φ p)) = ∑ p : Fin n × Fin n', (c p.1 * c' p.2 * (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)))⁻¹) • termPull D.toPre (FractionRing R) F k' …` using `fun β => by`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[d₂, map_smulₛₗ, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' p)]`. Both sides reduce to the same expression. Establish `hE` using `expandsG_of_fintype U.toUnifPre F k'' v'' _ _ y hy (hv.trans (Finset.sum_congr (M := GroupSec U.toUnifPre F k'') rfl fun p _ => by`. Rewrite using `[d₁, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' p)])) hs`. Rewrite `hs` using `[← ((expandsG_bijective U.toUnifPre F hG hk'' (U.expand k'' hk'')).1 v'').unique b'' hE]`.

Use `choose z hz using fun i χ => exists_isTerm g hw ((x i).2 χ)`. Use `choose z' hz' using fun i χ => exists_isTerm g hw' ((x' i).2 χ)`. Use `choose z'' hz'' using fun p => exists_isTerm g hw'' ((y p).2 α)`. Establish `key` using `sumF_sum hR Finset.univ (fun p : Fin n × Fin n' => c p.1 * c' p.2 * (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)))⁻¹) fun p => point_any U.toUnifPre hL hR (r p) hm (hx p.1) (hx' p.2) (hy p) (fun Z q z j hj => by`. Rewrite using `[hyτ p]`.

Conclude with `(powVal_smul _ _ q z hj).trans (congrArg _ (hτ p Z q z j hj))) g hw'' hww (hz p.1) (hz' p.2) α (hz'' p)`. Rewrite using `[coef_eq_sum g hz'' (hs α)]`. Use `key using 2 with χ` and compare the differences between its conclusion and the goal. Rewrite using `[coef_eq_sum g (fun i => hz i χ) (e₂ χ), coef_eq_sum g (fun i => hz' i (α - χ)) (e₂' (α - χ)), Finset.sum_mul_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Use `hr' (p, q)` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem prodConv_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k k' k'' : ℕ), 1 ≤ k → 1 ≤ k' → k'' = k + k' → ∀ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F k'') s s' s'', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → U.ExpandsF F k'' w₀ t'' s'' → (∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J) → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) (w' : Frm D.toPre F k' g.b) (w'' : Frm D.toPre F k'' g.b), w.IsGen → w'.IsGen → w''.IsGen → (∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J) → ∀ α, SumF I F (fun χ => coef s g w χ * coef s' g w' (α - χ)) (coef s'' g w'' α) := by
  intro hL R _ _ I hR D A G _ _ _ U F _ _ _ w₀ hw₀ k k' k'' hk hk' hm t t' t'' s s' s'' h h' h'' ht g w w' w'' hw hw' hw''
    hww α
  have hG := hL.1.globalFns
  have hk'' : 1 ≤ k'' := by omega
  obtain ⟨v, a, b⟩ := h
  obtain ⟨v', a', b'⟩ := h'
  obtain ⟨v'', a'', b''⟩ := h''
  obtain ⟨n, c, x, hx, e₁, e₂⟩ := (expandsG_iff U.toUnifPre F k v s).1 b
  obtain ⟨n', c', x', hx', e₁', e₂'⟩ := (expandsG_iff U.toUnifPre F k' v' s').1 b'
  obtain ⟨u, hu⟩ := exists_powMul A.isLB (q := (snd (TFK (R := R) F) A.A).left) hm t t'
  obtain rfl : t'' = u := sec_ext' A.isLB fun y J hJ => (ht y J hJ).trans (hu _ (𝟙 _) y _ (hJ (𝟙 _ ≫ _))).symm
  choose τ hτ using fun p : Fin n × Fin n' => exists_powMul U.LG.isLB (q := 𝟙 G.left) hm (x p.1).1 (x' p.2).1
  choose Φ hΦ using fun p => ((U.expand k'' hk'').1 (genericSec U.toUnifPre k'' (τ p))).exists
  choose r hr y hy d₁ d₂ using fun p => (expands_iff U.toUnifPre k'' _ _).1 (hΦ p)
  have hr' : ∀ p, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)) ≠ 0 := fun p => by
    rw [map_ne_zero]; exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hr p)
  have hyτ : ∀ p, (y p).1 = r p • (show IntSec U.toUnifPre k'' from τ p) := fun p =>
    genericSec_injective U.toUnifPre k'' ((d₁ p).trans (map_smulₛₗ _ _ _).symm)
  have hv : v'' = (∑ p : Fin n × Fin n', (c p.1 * c' p.2) • extendSec U.toUnifPre F k'' (genericSec U.toUnifPre k'' (τ p)) :
      GroupSec U.toUnifPre F k'') := by
    refine powVal_ext U.LG.isLB fun z i hi => ?_
    obtain ⟨i₁, hi₁⟩ := exists_chart A.isLB
      (U.gen.hom.left ((snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left z))
    have m := (isoRelM_iff _ _ _ _ a.1 _ a.2.1 _ _).1 a _ (𝟙 _) z i i₁ hi hi₁
    have m' := (isoRelM_iff _ _ _ _ a'.1 _ a'.2.1 _ _).1 a' _ (𝟙 _) z i i₁ hi hi₁
    have m'' := (isoRelM_iff _ _ _ _ a''.1 _ a''.2.1 _ _).1 a'' _ (𝟙 _) z i i₁ hi hi₁
    have b₁ : (snd (TFK (R := R) F) A.A).left ((𝟙 _ ≫ (U.genF F).left) z) ∈ A.L.U i₁ :=
      (congrArg (fun q => q z ∈ A.L.U i₁) a.1).mpr hi₁
    have m₀ := hu _ _ z i₁ b₁
    rw [Category.comp_id] at m m' m''
    have w₁ := (congrArg (fun q => powVal q (𝟙 _) z i) e₁).trans (powVal_comb U.toUnifPre c (fun p => (x p).1) z hi)
    have w₂ := (congrArg (fun q => powVal q (𝟙 _) z i) e₁').trans (powVal_comb U.toUnifPre c' (fun p => (x' p).1) z hi)
    refine Eq.trans ?_ (powVal_comb U.toUnifPre _ τ z hi).symm
    have w₃ : powVal v'' (𝟙 _) z i = powVal v (𝟙 _) z i * powVal v' (𝟙 _) z i := by
      rw [m, m', m'', m₀, hm, Nat.cast_add, zpow_add, Units.val_mul]; ring
    rw [w₃, w₁, w₂, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have cm : constVal (groupBase G F) z (c p * c' q) = constVal (groupBase G F) z (c p) * constVal (groupBase G F) z (c' q) :=
      (congrArg (gs _ z ⊤) (map_mul _ _ _)).trans (gs_mul _ z ⊤ trivial _ _)
    rw [hτ (p, q) _ (UnifPre.gFK (G := G) F) z i hi, cm]
    ring
  have hs : ∀ β, famProj D.toPre F k'' β (∑ p : Fin n × Fin n', (c p.1 * c' p.2) • famPull D.toPre (FractionRing R) F hG k'' (Φ p)) =
      ∑ p : Fin n × Fin n', (c p.1 * c' p.2 * (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)))⁻¹) •
        termPull D.toPre (FractionRing R) F k'' β (genericTerm D k'' β ((y p).2 β)) := fun β => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [d₂, map_smulₛₗ, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' p)]; rfl
  have hE := expandsG_of_fintype U.toUnifPre F k'' v'' _ _ y hy (hv.trans (Finset.sum_congr (M := GroupSec U.toUnifPre F k'') rfl fun p _ => by
    rw [d₁, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' p)])) hs
  rw [← ((expandsG_bijective U.toUnifPre F hG hk'' (U.expand k'' hk'')).1 v'').unique b'' hE] at hs
  choose z hz using fun i χ => exists_isTerm g hw ((x i).2 χ)
  choose z' hz' using fun i χ => exists_isTerm g hw' ((x' i).2 χ)
  choose z'' hz'' using fun p => exists_isTerm g hw'' ((y p).2 α)
  have key := sumF_sum hR Finset.univ (fun p : Fin n × Fin n' =>
      c p.1 * c' p.2 * (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)))⁻¹)
    fun p => point_any U.toUnifPre hL hR (r p) hm (hx p.1) (hx' p.2) (hy p) (fun Z q z j hj => by
      rw [hyτ p]
      exact (powVal_smul _ _ q z hj).trans (congrArg _ (hτ p Z q z j hj))) g hw'' hww (hz p.1) (hz' p.2) α (hz'' p)
  rw [coef_eq_sum g hz'' (hs α)]
  convert key using 2 with χ
  rw [coef_eq_sum g (fun i => hz i χ) (e₂ χ), coef_eq_sum g (fun i => hz' i (α - χ)) (e₂' (α - χ)), Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have := hr' (p, q)
  field_simp

end

section
open GlobalTheory.UT.PhiMul

/- English proof (translation)
Introduce `hL R _ _ I hI D A G _ _ hG U F _ _ _ w₀ hw₀ k hk p w hw n N hn hn2 q ω hq t t' s s' hs ht`. Establish `hN1 : ∀ i, 1 ≤ N i` using `fun i => by rw [(hn i).2]; exact Nat.mul_pos hk (hn i).1`. Establish `hN2 : N 2 = N 0 + N 1` using `by rw [(hn 0).2, (hn 1).2, (hn 2).2, hn2, mul_add]`. Establish `hB` using `(expBijF_any hL R I hI D A G hG U).1 F (N 2) (hN1 2) w₀ hw₀`. Take `⟨u, hu⟩` from `exists_secA_mul hN2 (t' 0) (t' 1)`.

Take `⟨r, hr, -⟩` from `hB.1 u`. Establish `hrs : r = s' 2`. Use `famEq_any hL R I hI D F (N 2) r (s' 2) fun g₀ => ?_` and prove the remaining obligations. Use `letI := GlobalTheory.TorusExt.gtGroup D.toPre F`. Establish `hadd : g₀.IsAdd p.g (g₀ + p.g)` using `(GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl`.

Take `⟨ω₀, hω₀⟩ : ∃ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen` from `exists_gen_of_local (V := F) D.toPre.P.L D.toPre.P.isLB _ _`. Take `⟨ω₁, hω₁, -, hφ⟩` from `coefPhi_any hL R I hI D F k hk p w hw g₀ _ hadd ω₀ hω₀`. Use `choose a ha using fun i => exists_frm_pow ω₀ hω₀ (n i) (N i) (hn i).2`. Use `choose b hb using fun i => exists_frm_pow ω₁ hω₁ (n i) (N i) (hn i).2`. Establish `hc : ∀ i α, coef (s' i) g₀ (a i) (α + (q i).y) = coef (s i) (g₀ + p.g) (b i) α` using `fun i => hφ (n i) (N i) (hn i).1 (hn i).2 (q i) (hq i).1 (hq i).2.1 (ω i) (a i) (b i) (hq i).2.2 (ha i) (hb i) (s i) (s' i) (hs i).2.2`.

Use `⟨a 2, (ha 2).1, fun χ => ?_⟩` and prove the remaining obligations. Establish `S₀` using `prodConv_any hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t' 0) (t' 1) u (s' 0) (s' 1) r (hs 0).2.1 (hs 1).2.1 hr hu g₀ (a 0) (a 1) (a 2) (ha 0).1 (ha 1).1 (ha 2).1 (fun z J hJ => by rw [(ha 0).2 z J hJ, (ha 1).2 z J hJ, (ha 2).2 z J hJ, hn2, pow_add]) χ`. Establish `S₁` using `prodConv_any hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t 0) (t 1) (t 2) (s 0) (s 1) (s 2) (hs 0).1 (hs 1).1 (hs 2).1 ht (g₀ + p.g) (b 0) (b 1) (b 2) (hb 0).1 (hb 1).1 (hb 2).1 (fun z J hJ => by rw [(hb 0).2 z J hJ, (hb 1).2 z J hJ, (hb 2).2 z J hJ, hn2, …`. Establish `hy : (q 2).y = (q 0).y + (q 1).y` using `by rw [(hq 0).1, (hq 1).1, (hq 2).1, hn2, add_smul]`. Establish `S₂` using `((GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ 0).2.2 _ (fun ψ => ψ + (q 0).y) (add_left_injective _) (fun i hi => absurd ⟨i - (q 0).y, sub_add_cancel _ _⟩ hi)).2 S₀`.

Establish `e : ((fun ψ => coef (s' 0) g₀ (a 0) ψ * coef (s' 1) g₀ (a 1) (χ - ψ)) ∘ fun ψ => ψ + (q 0).y) = fun ψ => coef (s 0) (g₀ + p.g) (b 0) ψ * coef (s 1) (g₀ + p.g) (b 1) (χ - (q 2).y - ψ)`. Use function extensionality and compare the values at `ψ`. Rewrite using `[← hc 0, ← hc 1, hy]`. Establish `e' : χ - ((q 0).y + (q 1).y) - ψ + (q 1).y = χ - (ψ + (q 0).y)` using `by abel`. Rewrite using `[e']`.

Both sides reduce to the same expression. Rewrite `S₂` using `[e]`. Rewrite using `[(GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ _).1 S₂ S₁, ← hc 2, sub_add_cancel]`. Take `rfl : u = t' 2` from `(hB.2 (s' 2)).unique (hrs ▸ hr) (hs 2).2.1`. Conclude with `hu`.
-/
theorem phiMul_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (n : Fin 3 → ℕ) (N : Fin 3 → ℕ), (∀ i, 1 ≤ n i ∧ N i = k * n i) → n 2 = n 0 + n 1 → ∀ (q : ∀ i, QkPt D.toPre F (N i)) (ω : ∀ i, Frm D.toPre F (N i) (q i).g.b), (∀ i, (q i).y = n i • p.y ∧ (q i).g = p.g ∧ ((ω i).IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val (ω i) (𝟙 _) z J = val w (𝟙 _) z J ^ n i)) → ∀ (t t' : ∀ i, SecA A F (N i)) (s s' : ∀ i, Fam D.toPre F (N i)), (∀ i, U.ExpandsF F (N i) w₀ (t i) (s i) ∧ U.ExpandsF F (N i) w₀ (t' i) (s' i) ∧ PhiRel D.toPre F (N i) (q i) (ω i) (s i) (s' i)) → (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) → ∀ z J, Good A.L z J → sA (t' 2) (𝟙 _) z J = sA (t' 0) (𝟙 _) z J * sA (t' 1) (𝟙 _) z J := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ w₀ hw₀ k hk p w hw n N hn hn2 q ω hq t t' s s' hs ht
  have hN1 : ∀ i, 1 ≤ N i := fun i => by rw [(hn i).2]; exact Nat.mul_pos hk (hn i).1
  have hN2 : N 2 = N 0 + N 1 := by rw [(hn 0).2, (hn 1).2, (hn 2).2, hn2, mul_add]
  have hB := (expBijF_any hL R I hI D A G hG U).1 F (N 2) (hN1 2) w₀ hw₀
  obtain ⟨u, hu⟩ := exists_secA_mul hN2 (t' 0) (t' 1)
  obtain ⟨r, hr, -⟩ := hB.1 u
  have hrs : r = s' 2 := by
    refine famEq_any hL R I hI D F (N 2) r (s' 2) fun g₀ => ?_
    letI := GlobalTheory.TorusExt.gtGroup D.toPre F
    have hadd : g₀.IsAdd p.g (g₀ + p.g) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl
    obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen :=
      exists_gen_of_local (V := F) D.toPre.P.L D.toPre.P.isLB _ _
    obtain ⟨ω₁, hω₁, -, hφ⟩ := coefPhi_any hL R I hI D F k hk p w hw g₀ _ hadd ω₀ hω₀
    choose a ha using fun i => exists_frm_pow ω₀ hω₀ (n i) (N i) (hn i).2
    choose b hb using fun i => exists_frm_pow ω₁ hω₁ (n i) (N i) (hn i).2
    have hc : ∀ i α, coef (s' i) g₀ (a i) (α + (q i).y) = coef (s i) (g₀ + p.g) (b i) α := fun i =>
      hφ (n i) (N i) (hn i).1 (hn i).2 (q i) (hq i).1 (hq i).2.1 (ω i) (a i) (b i) (hq i).2.2 (ha i) (hb i)
        (s i) (s' i) (hs i).2.2
    refine ⟨a 2, (ha 2).1, fun χ => ?_⟩
    have S₀ := prodConv_any hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t' 0) (t' 1) u
      (s' 0) (s' 1) r (hs 0).2.1 (hs 1).2.1 hr hu g₀ (a 0) (a 1) (a 2) (ha 0).1 (ha 1).1 (ha 2).1
      (fun z J hJ => by rw [(ha 0).2 z J hJ, (ha 1).2 z J hJ, (ha 2).2 z J hJ, hn2, pow_add]) χ
    have S₁ := prodConv_any hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t 0) (t 1) (t 2)
      (s 0) (s 1) (s 2) (hs 0).1 (hs 1).1 (hs 2).1 ht (g₀ + p.g) (b 0) (b 1) (b 2) (hb 0).1 (hb 1).1 (hb 2).1
      (fun z J hJ => by rw [(hb 0).2 z J hJ, (hb 1).2 z J hJ, (hb 2).2 z J hJ, hn2, pow_add]) (χ - (q 2).y)
    have hy : (q 2).y = (q 0).y + (q 1).y := by rw [(hq 0).1, (hq 1).1, (hq 2).1, hn2, add_smul]
    have S₂ := ((GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ 0).2.2 _ (fun ψ => ψ + (q 0).y)
      (add_left_injective _) (fun i hi => absurd ⟨i - (q 0).y, sub_add_cancel _ _⟩ hi)).2 S₀
    have e : ((fun ψ => coef (s' 0) g₀ (a 0) ψ * coef (s' 1) g₀ (a 1) (χ - ψ)) ∘ fun ψ => ψ + (q 0).y) =
        fun ψ => coef (s 0) (g₀ + p.g) (b 0) ψ * coef (s 1) (g₀ + p.g) (b 1) (χ - (q 2).y - ψ) := by
      funext ψ
      rw [← hc 0, ← hc 1, hy]
      have e' : χ - ((q 0).y + (q 1).y) - ψ + (q 1).y = χ - (ψ + (q 0).y) := by abel
      rw [e']
      rfl
    rw [e] at S₂
    rw [(GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ _).1 S₂ S₁, ← hc 2, sub_add_cancel]
  obtain rfl : u = t' 2 := (hB.2 (s' 2)).unique (hrs ▸ hr) (hs 2).2.1
  exact hu

end

section
open GlobalTheory.FieldBaseChange GlobalTheory.InducingAut

/- English proof (translation)
Introduce `hL R _ _ I hI D A G _ _ hS U F _ _ _ k hk p`. Establish `hG` using `hL.1.globalFns`. Establish `hN : ∀ n, 1 ≤ k * (n + 1)` using `fun n => Nat.mul_pos hk n.succ_pos`. Take `⟨w₀, hw₀⟩` from `U.ext`. Take `⟨w, hw⟩` from `exists_frame D.toPre F k p.g.b`.

Use `choose ω hω vω using fun n => exists_frame_pow w hw (n + 1)`. Set `q : ∀ n, QkPt D.toPre F (k * (n + 1))` to `fun n => ⟨(n + 1) • p.y, p.g, exists_qk_mul D.tau_bimult p (n + 1)⟩`. Use `choose Φ hΦ using fun n => phiProj_any hL R I hI D F (k * (n + 1)) (hN n)`. Establish `hΦ'` using `fun n => (hΦ n).1 (q n) (ω n) (hω n)`. Use `choose Ψ lin ex un using fun n => exists_transport hG U F (hN n) hw₀ _ (hΦ' n).1`.

Establish `mul : ∀ m : Fin 3 → ℕ, m 2 = m 0 + m 1 + 1 → ∀ t : ∀ i, SecA A F (k * (m i + 1)), (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) → ∀ z J, Good A.L z J → sA (Ψ _ (t 2)) (𝟙 _) z J = sA (Ψ _ (t 0)) (𝟙 _) z J * sA (Ψ _ (t 1)) (𝟙 _) z J`. Introduce `m hm t`. Use `choose s hs hs' using fun i => ex (m i) (t i)`. Conclude with `phiMul_any hL R I hI D A G hS U F w₀ hw₀ k hk p w hw (fun i => m i + 1) (fun i => k * (m i + 1)) (fun i => ⟨Nat.succ_pos _, rfl⟩) (by show m 2 + 1 = m 0 + 1 + (m 1 + 1); omega) (fun i => q (m i)) (fun i => ω (m i)) (fun i => ⟨rfl, rfl, hω _, vω _⟩) t (fun i => Ψ _ (t i)) s _ (fun …`. Take `⟨ψ, hψ, hα⟩` from `GlobalTheory.T.exists_automorphism_of_multiplicative_section_family F _ A (jFK (R := R) F) k hk Ψ lin (fun a b s s' s'' h => (mul_chart_iff A.isLB _ _ _ _).2 (mul ![a, b, a + b + 1] rfl (Fin.cons s (Fin.cons s' (Fin.cons s'' finZeroElim))) ((mul_chart_iff A.isLB _ _ _ _).1 h)))`.

Use `⟨ψ, fun n N hn hN' q' hy hg => ?_⟩` and prove the remaining obligations. Take `⟨n, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Substitute `hN'` using the available equality. Take `rfl : q' = q n` from `GlobalTheory.TorusExt.qk_ext hy hg`. Take `⟨α, hα, tw⟩` from `hα n`.

Use `⟨hψ, fun w₁ hw₁ => ⟨α, ω n, hα, hω n, fun t t' s s' h h' H => ?_⟩⟩` and prove the remaining obligations. Take `rfl : t' = Ψ n t` from `sec_ext' A.isLB fun y J hJ => (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A H (𝟙 _) y hJ).trans (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A (tw t) (𝟙 _) y hJ).symm`. Conclude with `((hΦ' n).2 _ _).2 (un n w₁ hw₁ t s s' h h')`.
-/
theorem existsAut_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ ψ : (TFK (R := R) F ⊗ A.A) ≅ (TFK (R := R) F ⊗ A.A), ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q ψ.hom := by
  intro hL R _ _ I hI D A G _ _ hS U F _ _ _ k hk p
  have hG := hL.1.globalFns
  have hN : ∀ n, 1 ≤ k * (n + 1) := fun n => Nat.mul_pos hk n.succ_pos
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨w, hw⟩ := exists_frame D.toPre F k p.g.b
  choose ω hω vω using fun n => exists_frame_pow w hw (n + 1)
  let q : ∀ n, QkPt D.toPre F (k * (n + 1)) := fun n =>
    ⟨(n + 1) • p.y, p.g, exists_qk_mul D.tau_bimult p (n + 1)⟩
  choose Φ hΦ using fun n => phiProj_any hL R I hI D F (k * (n + 1)) (hN n)
  have hΦ' := fun n => (hΦ n).1 (q n) (ω n) (hω n)
  choose Ψ lin ex un using fun n => exists_transport hG U F (hN n) hw₀ _ (hΦ' n).1
  have mul : ∀ m : Fin 3 → ℕ, m 2 = m 0 + m 1 + 1 → ∀ t : ∀ i, SecA A F (k * (m i + 1)),
      (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) →
      ∀ z J, Good A.L z J → sA (Ψ _ (t 2)) (𝟙 _) z J = sA (Ψ _ (t 0)) (𝟙 _) z J * sA (Ψ _ (t 1)) (𝟙 _) z J := by
    intro m hm t
    choose s hs hs' using fun i => ex (m i) (t i)
    exact phiMul_any hL R I hI D A G hS U F w₀ hw₀ k hk p w hw (fun i => m i + 1) (fun i => k * (m i + 1))
      (fun i => ⟨Nat.succ_pos _, rfl⟩) (by show m 2 + 1 = m 0 + 1 + (m 1 + 1); omega) (fun i => q (m i))
      (fun i => ω (m i)) (fun i => ⟨rfl, rfl, hω _, vω _⟩) t (fun i => Ψ _ (t i)) s _
      (fun i => ⟨hs i, hs' i, ((hΦ' _).2 _ _).2 rfl⟩)
  obtain ⟨ψ, hψ, hα⟩ := GlobalTheory.T.exists_automorphism_of_multiplicative_section_family F _ A (jFK (R := R) F) k hk Ψ lin (fun a b s s' s'' h =>
    (mul_chart_iff A.isLB _ _ _ _).2 (mul ![a, b, a + b + 1] rfl
      (Fin.cons s (Fin.cons s' (Fin.cons s'' finZeroElim))) ((mul_chart_iff A.isLB _ _ _ _).1 h)))
  refine ⟨ψ, fun n N hn hN' q' hy hg => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hN'
  obtain rfl : q' = q n := GlobalTheory.TorusExt.qk_ext hy hg
  obtain ⟨α, hα, tw⟩ := hα n
  refine ⟨hψ, fun w₁ hw₁ => ⟨α, ω n, hα, hω n, fun t t' s s' h h' H => ?_⟩⟩
  obtain rfl : t' = Ψ n t := sec_ext' A.isLB fun y J hJ =>
    (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A H (𝟙 _) y hJ).trans
      (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A (tw t) (𝟙 _) y hJ).symm
  exact ((hΦ' n).2 _ _).2 (un n w₁ hw₁ t s s' h h')

end

section
open GlobalTheory.UT.IndComp

/- English proof (translation)
Introduce `hL R _ _ I hR D A G _ _ _ U F _ _ _ N hN p p' p'' ψ ψ' hψ`. Establish `hG` using `hL.1.globalFns`. Take `⟨Φ, hrel, -, hrat, hequ, hadd, hone⟩` from `phiProj_any hL R I hR D F N hN`. Use `⟨fun hψ' hs => ⟨by rw [Category.assoc, hψ'.1, hψ.1], fun w₀ hw₀ => ?_⟩, fun he => ⟨hψ.1, fun w₀ hw₀ => ?_⟩, fun h4 hψ' => ?_, fun hy hg => ⟨Category.id_comp _, fun w₀ hw₀ => ?_⟩⟩` and prove the remaining obligations. Take `⟨α, w, hα, hw, h⟩` from `hψ.2 w₀ hw₀`.

Take `⟨α', w', hα', hw', h'⟩` from `hψ'.2 w₀ hw₀`. Take `⟨w'', hw'', hΦ⟩` from `hadd p p' p'' w w' hw hw' hs`. Take `⟨β, hβ, hc⟩` from `exists_twist_comp A.isLB ψ ψ' (N : ℤ) α α' hα hα'`. Take `⟨e, he⟩` from `GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀`. Use `⟨β, w'', hβ, hw'', fun t t' s s' ht ht' H => ?_⟩` and prove the remaining obligations.

Take `⟨u, hu⟩` from `VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα' t`. Take `⟨v, hv⟩` from `VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα u`. Take `rfl : v = t'` from `twist_unique A.isLB (hc t u v hu hv) H`. Establish `e₁` using `((hrel p' w' hw').2 _ _).1 (h' t u s _ ht ((he u _).2 rfl) hu)`. Establish `e₂` using `((hrel p w hw).2 _ _).1 (h u v _ s' ((he u _).2 rfl) ht' hv)`.

Use `((hrel p'' w'' hw'').2 _ _).2 ?_` and prove the remaining obligations. Rewrite using `[hΦ, LinearMap.comp_apply, ← e₁, e₂]`. Take `⟨α, w, hα, hw, h⟩` from `hψ.2 w₀ hw₀`. Take `⟨w', hw', hΦ⟩` from `hequ p p' w hw he`. Use `⟨α, w', hα, hw', fun t t' s s' ht ht' H => ((hrel p' w' hw').2 _ _).2 ?_⟩` and prove the remaining obligations.

Rewrite using `[hΦ]`. Conclude with `((hrel p w hw).2 _ _).1 (h t t' s s' ht ht' H)`. Take `⟨w₀, hw₀⟩` from `U.ext`. Take `⟨α, w, hα, hw, h⟩` from `hψ.2 w₀ hw₀`. Take `⟨α', w', hα', hw', h'⟩` from `hψ'.2 w₀ hw₀`.

Take `⟨c, hc, hΦ⟩` from `hrat p w w' hw hw'`. Take `⟨e, he⟩` from `GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀`. Use `AutUniq.endo_eq_of_sections hL R A F N h4 ψ ψ' hψ.1 hψ'.1 α α' hα hα' (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc)) fun t t₁ t₂ h₁ h₂ j => ?_` and prove the remaining obligations. Establish `e₁` using `((hrel p w hw).2 _ _).1 (h t t₁ _ _ ((he t _).2 rfl) ((he t₁ _).2 rfl) h₁)`. Establish `e₂` using `((hrel p w' hw').2 _ _).1 (h' t t₂ _ _ ((he t _).2 rfl) ((he t₂ _).2 rfl) h₂)`.

Rewrite `e₂` using `[hΦ, LinearMap.smul_apply, ← e₁]`. Conclude with `congrArg (fun x => LB.Sec.f x j) (e.injective (e₂.trans (e.map_smul c t₁).symm))`. Take `⟨w, hw⟩` from `(CoefBasic.coef_basic R D.toPre F N p'.g).2.1 hg.1`. Take `⟨β, hβ, hc⟩` from `exists_twist_id (T := TFK (R := R) F) A.isLB (N : ℤ)`. Take `⟨e, he⟩` from `GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀`.

Use `⟨β, w, hβ, hw.1, fun t t' s s' ht ht' H => ((hrel p' w hw.1).2 _ _).2 ?_⟩` and prove the remaining obligations. Take `rfl : t = t'` from `twist_unique A.isLB (hc t) H`. Rewrite using `[hone p' w hy hg hw]`. Conclude with `((he _ _).1 ht').symm.trans ((he _ _).1 ht)`.
-/
theorem indAtComp_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  intro hL R _ _ I hR D A G _ _ _ U F _ _ _ N hN p p' p'' ψ ψ' hψ
  have hG := hL.1.globalFns
  obtain ⟨Φ, hrel, -, hrat, hequ, hadd, hone⟩ := phiProj_any hL R I hR D F N hN
  refine ⟨fun hψ' hs => ⟨by rw [Category.assoc, hψ'.1, hψ.1], fun w₀ hw₀ => ?_⟩, fun he => ⟨hψ.1, fun w₀ hw₀ => ?_⟩,
    fun h4 hψ' => ?_, fun hy hg => ⟨Category.id_comp _, fun w₀ hw₀ => ?_⟩⟩
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨w'', hw'', hΦ⟩ := hadd p p' p'' w w' hw hw' hs
    obtain ⟨β, hβ, hc⟩ := exists_twist_comp A.isLB ψ ψ' (N : ℤ) α α' hα hα'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w'', hβ, hw'', fun t t' s s' ht ht' H => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα' t
    obtain ⟨v, hv⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα u
    obtain rfl : v = t' := twist_unique A.isLB (hc t u v hu hv) H
    have e₁ := ((hrel p' w' hw').2 _ _).1 (h' t u s _ ht ((he u _).2 rfl) hu)
    have e₂ := ((hrel p w hw).2 _ _).1 (h u v _ s' ((he u _).2 rfl) ht' hv)
    refine ((hrel p'' w'' hw'').2 _ _).2 ?_
    rw [hΦ, LinearMap.comp_apply, ← e₁, e₂]
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨w', hw', hΦ⟩ := hequ p p' w hw he
    refine ⟨α, w', hα, hw', fun t t' s s' ht ht' H => ((hrel p' w' hw').2 _ _).2 ?_⟩
    rw [hΦ]
    exact ((hrel p w hw).2 _ _).1 (h t t' s s' ht ht' H)
  · obtain ⟨w₀, hw₀⟩ := U.ext
    obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨c, hc, hΦ⟩ := hrat p w w' hw hw'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine AutUniq.endo_eq_of_sections hL R A F N h4 ψ ψ' hψ.1 hψ'.1 α α' hα hα'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc)) fun t t₁ t₂ h₁ h₂ j => ?_
    have e₁ := ((hrel p w hw).2 _ _).1 (h t t₁ _ _ ((he t _).2 rfl) ((he t₁ _).2 rfl) h₁)
    have e₂ := ((hrel p w' hw').2 _ _).1 (h' t t₂ _ _ ((he t _).2 rfl) ((he t₂ _).2 rfl) h₂)
    rw [hΦ, LinearMap.smul_apply, ← e₁] at e₂
    exact congrArg (fun x => LB.Sec.f x j) (e.injective (e₂.trans (e.map_smul c t₁).symm))
  · obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F N p'.g).2.1 hg.1
    obtain ⟨β, hβ, hc⟩ := exists_twist_id (T := TFK (R := R) F) A.isLB (N : ℤ)
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w, hβ, hw.1, fun t t' s s' ht ht' H => ((hrel p' w hw.1).2 _ _).2 ?_⟩
    obtain rfl : t = t' := twist_unique A.isLB (hc t) H
    rw [hone p' w hy hg hw]
    exact ((he _ _).1 ht').symm.trans ((he _ _).1 ht)

end

section

/- English proof (translation)
Introduce `hL R _ _ I _ D A G _ _ _ U F _ _ _ N hN p x`. Establish `hG` using `hL.1.globalFns`. Establish `key` using `fun w₀ : W0 U.toUnifPre => exists_twist_iff A.L (translT A.A x) (translPt A.A x) (lift_snd _ _) (N : ℤ) (W := Frm D.toPre F N p.g.b) (fun w => w.IsGen) (fun w Q => ∀ (t t' : SecA A F N) s s', U.toUnifPre.ExpandsF F N w₀ t s → U.toUnifPre.ExpandsF F N w₀ t' s' → Q t t' → PhiRel D. …`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, H⟩ w₀ hw₀`.

Take `⟨α, w, hα, hw, h⟩` from `(key w₀).1 (H w₀ hw₀)`. Use `⟨(hL.1.kerPow _ A N hN _ x).1 fun _ => ⟨⊤, trivial, exists_isGen_pull _ α hα _⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, β, hβ⟩ rfl`. Take `⟨c, hc, hcs⟩` from `exists_smul_of_pt_eq hG A F (N : ℤ) _ α β hα hβ`. Take `⟨w', hw', hΦ⟩` from `ProdTorsion.exists_phiRel_smul hG p w hw c hc`.

Take `⟨e, he⟩` from `GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀`. Use `⟨w', hw', fun t t' s s' hs hs' ht => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `VVRank.exists_isTwistPull A.A (hm := (lift_snd _ _ : translT A.A y ≫ _ = _)) A.isLB hα t`. Establish `e₁` using `hΦ _ _ (h t u s _ hs ((he u _).2 rfl) hu)`. Establish `e₂ : s' = c • e u` using `((he _ _).1 hs').symm.trans ((congrArg e (hcs t u t' hu ht)).trans (e.map_smul c u))`.

Conclude with `e₂ ▸ e₁`. Introduce `H`. Use `⟨lift_fst _ _, fun w₀ hw₀ => (key w₀).2 ?_⟩` and prove the remaining obligations. Use `haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))`. Use `haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))`.

Take `⟨θ, rfl⟩` from `BoxTheta.exists_theta hL.1.kerPow A hN x (H w₀ hw₀).1`. Take `⟨w, hw, h⟩` from `(H w₀ hw₀).2 θ rfl`. Conclude with `⟨θ.φ, w, θ.isGen, hw, h⟩`.
-/
theorem indAtTransl_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  intro hL R _ _ I _ D A G _ _ _ U F _ _ _ N hN p x
  have hG := hL.1.globalFns
  have key := fun w₀ : W0 U.toUnifPre => exists_twist_iff A.L (translT A.A x) (translPt A.A x) (lift_snd _ _) (N : ℤ)
    (W := Frm D.toPre F N p.g.b) (fun w => w.IsGen) (fun w Q => ∀ (t t' : SecA A F N) s s',
      U.toUnifPre.ExpandsF F N w₀ t s → U.toUnifPre.ExpandsF F N w₀ t' s' → Q t t' → PhiRel D.toPre F N p w s s')
  constructor
  · rintro ⟨-, H⟩ w₀ hw₀
    obtain ⟨α, w, hα, hw, h⟩ := (key w₀).1 (H w₀ hw₀)
    refine ⟨(hL.1.kerPow _ A N hN _ x).1 fun _ => ⟨⊤, trivial, exists_isGen_pull _ α hα _⟩, ?_⟩
    rintro ⟨y, β, hβ⟩ rfl
    obtain ⟨c, hc, hcs⟩ := exists_smul_of_pt_eq hG A F (N : ℤ) _ α β hα hβ
    obtain ⟨w', hw', hΦ⟩ := ProdTorsion.exists_phiRel_smul hG p w hw c hc
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨w', hw', fun t t' s s' hs hs' ht => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := (lift_snd _ _ : translT A.A y ≫ _ = _)) A.isLB hα t
    have e₁ := hΦ _ _ (h t u s _ hs ((he u _).2 rfl) hu)
    have e₂ : s' = c • e u := ((he _ _).1 hs').symm.trans ((congrArg e (hcs t u t' hu ht)).trans (e.map_smul c u))
    exact e₂ ▸ e₁
  · intro H
    refine ⟨lift_fst _ _, fun w₀ hw₀ => (key w₀).2 ?_⟩
    haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
    obtain ⟨θ, rfl⟩ := BoxTheta.exists_theta hL.1.kerPow A hN x (H w₀ hw₀).1
    obtain ⟨w, hw, h⟩ := (H w₀ hw₀).2 θ rfl
    exact ⟨θ.φ, w, θ.isGen, hw, h⟩

end

section

/- English proof (translation)
Introduce and unpack `⟨hL, hL₂, -, -, -⟩ R _ _ I hadm D A G _ _ hG U`. Use `haveI := hG.geomConnected`. Establish `h₁` using `GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hadm D A G U.toUnifPre 2 (by norm_num) (U.expand 2 (by norm_num))`. Establish `h₂` using `(GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2 (by norm_num)).2`. Conclude with `Nat.pow_right_injective (le_refl 2) (h₁.symm.trans h₂)`.
-/
theorem dimEq_any :
    LL → AnyU fun {R} _ _ {I} {D} {A} {G} _ _ U => A.g = D.toPre.rank + D.toPre.P.g := by
  rintro ⟨hL, hL₂, -, -, -⟩ R _ _ I hadm D A G _ _ hG U
  haveI := hG.geomConnected
  have h₁ := GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hadm D A G U.toUnifPre 2 (by norm_num)
    (U.expand 2 (by norm_num))
  have h₂ := (GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2
    (by norm_num)).2
  exact Nat.pow_right_injective (le_refl 2) (h₁.symm.trans h₂)

end

/- English proof (translation)
Rewrite `hσ` using `[← nsmul_eq_mul]`. Substitute `hσ` using the available equality. Use `SerreTorsion.eq_one_of_pow (fun n x hn hx => htf n x hn (by rwa [← nsmul_eq_mul])) hMp (fun x hx => hsep x fun k => ?_) (by omega) dvd_rfl (by omega) m hm φ h` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx k`. Conclude with `⟨y, by rw [hy, nsmul_eq_mul, Nat.cast_pow]⟩`.
-/
theorem serre_prime (E : Type) [Ring E] (M : ℕ) (hMp : M.Prime) (hM : 3 ≤ M)
    (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → (n : E) * x = 0 → x = 0)
    (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = (M : E) ^ k * y) → x = 0) (σ φ : E) (m : ℕ) (hm : m ≠ 0)
    (hσ : σ = 1 + (M : E) * φ) (h : σ ^ m = 1) : σ = 1 := by
  rw [← nsmul_eq_mul] at hσ
  subst hσ
  refine SerreTorsion.eq_one_of_pow (fun n x hn hx => htf n x hn (by rwa [← nsmul_eq_mul])) hMp
    (fun x hx => hsep x fun k => ?_) (by omega) dvd_rfl (by omega) m hm φ h
  obtain ⟨y, hy⟩ := hx k
  exact ⟨y, by rw [hy, nsmul_eq_mul, Nat.cast_pow]⟩

/- English proof (translation)
Distinguish the cases in `h : ((3 : ℕ) : F) = 0`. Use `⟨5, by norm_num, by norm_num, fun h' => one_ne_zero (α := F) ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at h h'`. Take the linear combination `2 * h - h'`. Conclude with `⟨3, by norm_num, le_rfl, h⟩`.
-/
theorem exists_odd_prime_ne_zero (F : Type) [Field F] : ∃ M : ℕ, M.Prime ∧ 3 ≤ M ∧ (M : F) ≠ 0 := by
  by_cases h : ((3 : ℕ) : F) = 0
  · refine ⟨5, by norm_num, by norm_num, fun h' => one_ne_zero (α := F) ?_⟩
    push_cast at h h'
    linear_combination 2 * h - h'
  · exact ⟨3, by norm_num, le_rfl, h⟩

section
open SerreField GlobalTheory.FiniteOrderFix

/- English proof (translation)
Establish `hdiv` using `DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one (fun S _ P n hn => ⟨(h.mulN S P n hn).1, (h.mulN S P n hn).2.1, (h.mulN S P n hn).2.2.1, (h.mulN S P n hn).2.2.2.1⟩)`. Establish `hfix'` using `fix_torsion_of_fix_geometric_of_isDominant h.mulN P M (by omega) (by`. Simplify using `using hMK.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) (𝟙 _) σ hσ hfix`. Set `τ : P.A ⟶ P.A` to `σ`. Establish `hu : IsMonHom (τ * (𝟙 P.A)⁻¹)`.

Rewrite using `[Hom.mul_def, Hom.inv_def]`. Use `infer_instance`. Take `⟨⟨φ, hφ, e⟩, -⟩` from `hdiv _ P P.A M (by omega) (τ * (𝟙 P.A)⁻¹) hu (fun T x hx => by`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, hfix' T x hx, Category.comp_id, mul_inv_cancel])`. Establish `hpow : ∀ (n : ℕ) (x : P.A ⟶ P.A), (toRing τ ^ n).1 (Additive.ofMul x) = Additive.ofMul (x ≫ (σ ^ n : CategoryTheory.End P.A))` using `fun n x => by`.

Proceed by induction on `n with`. Consider the case `zero => exact congrArg Additive.ofMul (Category.comp_id x).symm`. Consider the case `succ n ih`. Rewrite using `[pow_succ', pow_succ', End.mul_def, ← Category.assoc]`. Conclude with `(congrArg (toRing τ).1 ih).trans (toRing_apply _ _)`.

Establish `key : toRing τ = 1`. Use `serre_prime (homRing P.A) M hMp hM ?_ ?_ (toRing τ) (toRing φ) m hm ?_ ?_` and prove the remaining obligations. Introduce and unpack `k ⟨f, u, hu, hf⟩ hk e`. Establish `h1` using `congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e`. Simplify using `only [natCast_mul_apply, hf, Category.id_comp] at h1`.

Establish `h2 : u ^ k = 1` using `h1`. Take `⟨_, _, _, -⟩` from `h.mulN _ P k (by omega)`. Establish `h3 : u = 1` using `DivisibleHom.cancel_of_flat_surjective (mulA P.A k) (by rw [DivisibleHom.mulA_comp, h2, MonObj.comp_one])`. Conclude with `homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)`. Introduce and unpack `⟨f, u, hu, hf⟩ e`.

Establish `h3 : u = 1` using `eq_of_agree_on_pow_torsion h P P hMp.two_le hMK u 1 fun k x hx => by`. Take `⟨⟨g, v, hv, hg⟩, e⟩` from `e k`. Establish `h1` using `congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e`. Simplify using `only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1`. Establish `h2 : u = v ^ M ^ k` using `h1`.

Rewrite using `[h2, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp, MonObj.comp_one]`. Conclude with `homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)`. Use `homRing_ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = Additive.ofMul (𝟙 P.A) + ((M : homRing P.A) * toRing φ).1 _`. Rewrite using `[natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp, ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]`.

Conclude with `homRing_ext (by rw [hpow, hord, Category.id_comp]; rfl)`. Establish `h1` using `congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) key`. Simplify using `only [toRing_apply, Category.id_comp] at h1`. Conclude with `h1`.
-/
theorem eq_one_of_field_any (h : Laws) {K : Type} [Field K] [IsAlgClosed K] (P : PolAV (Sp K))
    {M : ℕ} (hMp : M.Prime) (hM : 3 ≤ M) (hMK : (M : K) ≠ 0) (σ : CategoryTheory.End P.A) [hσ : IsMonHom (σ : P.A ⟶ P.A)] {m : ℕ} (hm : m ≠ 0)
    (hord : σ ^ m = 1) (hfix : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ M = 1 → x ≫ σ = x) : σ = 1 := by
  have hdiv := DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one (fun S _ P n hn =>
    ⟨(h.mulN S P n hn).1, (h.mulN S P n hn).2.1, (h.mulN S P n hn).2.2.1, (h.mulN S P n hn).2.2.2.1⟩)
  have hfix' := fix_torsion_of_fix_geometric_of_isDominant h.mulN P M (by omega) (by
    simpa using hMK.isUnit.map
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) (𝟙 _) σ hσ hfix
  let τ : P.A ⟶ P.A := σ
  have hu : IsMonHom (τ * (𝟙 P.A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨⟨φ, hφ, e⟩, -⟩ := hdiv _ P P.A M (by omega) (τ * (𝟙 P.A)⁻¹) hu (fun T x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix' T x hx, Category.comp_id, mul_inv_cancel])
  have hpow : ∀ (n : ℕ) (x : P.A ⟶ P.A), (toRing τ ^ n).1 (Additive.ofMul x) =
      Additive.ofMul (x ≫ (σ ^ n : CategoryTheory.End P.A)) := fun n x => by
    induction n with
    | zero => exact congrArg Additive.ofMul (Category.comp_id x).symm
    | succ n ih =>
      rw [pow_succ', pow_succ', End.mul_def, ← Category.assoc]
      exact (congrArg (toRing τ).1 ih).trans (toRing_apply _ _)
  have key : toRing τ = 1 := by
    refine serre_prime (homRing P.A) M hMp hM ?_ ?_ (toRing τ) (toRing φ) m hm ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk e
      have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      obtain ⟨_, _, _, -⟩ := h.mulN _ P k (by omega)
      have h3 : u = 1 := DivisibleHom.cancel_of_flat_surjective (mulA P.A k)
        (by rw [DivisibleHom.mulA_comp, h2, MonObj.comp_one])
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro ⟨f, u, hu, hf⟩ e
      have h3 : u = 1 := eq_of_agree_on_pow_torsion h P P hMp.two_le hMK u 1
        fun k x hx => by
          obtain ⟨⟨g, v, hv, hg⟩, e⟩ := e k
          have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
          simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
          have h2 : u = v ^ M ^ k := h1
          rw [h2, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp, MonObj.comp_one]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 P.A) + ((M : homRing P.A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · exact homRing_ext (by rw [hpow, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

/- English proof (translation)
Introduce and unpack `⟨laws, -⟩ S _ P F _ _ M hMp hM hMF p h hfst h0 ⟨n, hn, hord⟩ hfix`. Take `⟨P', g, hg, -, pm, -⟩` from `laws.polBaseChange S _ p P`. Establish `hg' : IsPullback (snd (Over.mk p) P.A).left (fst (Over.mk p) P.A).left P.A.hom p` using `(IsPullback.of_hasPullback p P.A.hom).flip`. Set `e` to `hg.isoIsPullback _ _ hg'`. Establish `e₁ : e.hom ≫ (snd (Over.mk p) P.A).left = g` using `hg.isoIsPullback_hom_fst _ _ hg'`.

Establish `e₂ : e.hom ≫ (fst (Over.mk p) P.A).left = P'.A.hom` using `hg.isoIsPullback_hom_snd _ _ hg'`. Establish `e₃ : h.left ≫ (fst (Over.mk p) P.A).left = (fst (Over.mk p) P.A).left` using `congrArg (·.left) hfst`. Set `σ : CategoryTheory.End P'.A` to `Over.homMk (e.hom ≫ h.left ≫ e.inv) (by`. Rewrite using `[← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃])`. Establish `hσ : σ.left ≫ e.hom = e.hom ≫ h.left`.

Express the relevant statement in the definitionally equal form `(e.hom ≫ h.left ≫ e.inv) ≫ e.hom = _`. Simplify using the standard rewrite rules. Establish `hpow : ∀ k : ℕ, (σ ^ k).left ≫ e.hom = e.hom ≫ (h ^ k).left` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => exact (Category.id_comp _).trans (Category.comp_id _).symm`.

Consider the case `succ k ih`. Rewrite using `[pow_succ', pow_succ', End.mul_def, End.mul_def, Over.comp_left, Over.comp_left, Category.assoc, hσ, reassoc_of% ih]`. Set `c : Over.mk p ⟶ Over.mk ((baseOver (Sp F)).hom ≫ p)` to `Over.homMk (𝟙 _) (by simp)`. Set `ρ : (baseOver (Sp F) ⟶ P'.A) →* (Over.mk p ⟶ P.A)` to `MonoidHom.mk' (fun x => c ≫ toBase hg.w x) fun x y => by rw [pm, MonObj.comp_mul]`. Establish `hρ : ∀ x, (ptSecT P.A (ρ x)).left = x.left ≫ e.hom` using `fun x => by`.

Use `hg'.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[← Over.comp_left, ptSecT, lift_snd, Category.assoc, e₁]`. Conclude with `Category.id_comp _`. Rewrite using `[← Over.comp_left, ptSecT, lift_fst, Category.assoc, e₂]`. Conclude with `(Over.w x).symm`.

Establish `key : ∀ x, ptSecT P.A (ρ x) ≫ h = ptSecT P.A (ρ x) → x ≫ σ = x` using `fun x hx => by`. Use `congrArg (·.left) hx` as an intermediate fact. Simplify using `only [Over.comp_left, hρ] at this`. Use `Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)` and prove the remaining obligations. Rewrite using `[Over.comp_left, Category.assoc, hσ, ← Category.assoc, this]`.

Establish `hη : (1 : baseOver (Sp F) ⟶ P'.A) = η[P'.A]` using `(congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)`. Establish `: IsMonHom (σ : P'.A ⟶ P'.A)` using `laws.rigidity _ _ _ P'.isAb P'.isAb σ (by`. Use `key 1 (by rw [map_one]; exact h0)` as an intermediate fact. Rewrite using `[hη] at this)` and apply the resulting hypothesis. Establish `h1 : σ = 1` using `eq_one_of_field_any laws P' hMp hM hMF σ (m := n) (by omega) (Over.OverMorphism.ext ((cancel_mono e.hom).1 ((hpow n).trans (by rw [hord]; exact (hpow 0).symm)))) fun x hx => key x (hfix _ (by rw [← map_pow, hx, map_one]))`.

Use `Over.OverMorphism.ext ((cancel_epi e.hom).1 ?_)` and prove the remaining obligations. Rewrite using `[← hσ, h1]`. Conclude with `hpow 0`.
-/
theorem eq_one_of_finite_order_any :
    LL → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (M : ℕ), M.Prime → 3 ≤ M → (M : F) ≠ 0 → ∀ (p : Spec (CommRingCat.of F) ⟶ S) (h : CategoryTheory.End (Over.mk p ⊗ P.A)), h ≫ fst _ _ = fst _ _ → ptSecT P.A 1 ≫ h = ptSecT P.A 1 → (∃ n, 1 ≤ n ∧ h ^ n = 1) → (∀ x : Over.mk p ⟶ P.A, x ^ M = 1 → ptSecT P.A x ≫ h = ptSecT P.A x) → h = 1 := by
  rintro ⟨laws, -⟩ S _ P F _ _ M hMp hM hMF p h hfst h0 ⟨n, hn, hord⟩ hfix
  obtain ⟨P', g, hg, -, pm, -⟩ := laws.polBaseChange S _ p P
  have hg' : IsPullback (snd (Over.mk p) P.A).left (fst (Over.mk p) P.A).left P.A.hom p :=
    (IsPullback.of_hasPullback p P.A.hom).flip
  let e := hg.isoIsPullback _ _ hg'
  have e₁ : e.hom ≫ (snd (Over.mk p) P.A).left = g := hg.isoIsPullback_hom_fst _ _ hg'
  have e₂ : e.hom ≫ (fst (Over.mk p) P.A).left = P'.A.hom := hg.isoIsPullback_hom_snd _ _ hg'
  have e₃ : h.left ≫ (fst (Over.mk p) P.A).left = (fst (Over.mk p) P.A).left := congrArg (·.left) hfst
  let σ : CategoryTheory.End P'.A := Over.homMk (e.hom ≫ h.left ≫ e.inv) (by
    rw [← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃])
  have hσ : σ.left ≫ e.hom = e.hom ≫ h.left := by
    change (e.hom ≫ h.left ≫ e.inv) ≫ e.hom = _
    simp
  have hpow : ∀ k : ℕ, (σ ^ k).left ≫ e.hom = e.hom ≫ (h ^ k).left := fun k => by
    induction k with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | succ k ih =>
      rw [pow_succ', pow_succ', End.mul_def, End.mul_def, Over.comp_left, Over.comp_left, Category.assoc, hσ,
        reassoc_of% ih]
  let c : Over.mk p ⟶ Over.mk ((baseOver (Sp F)).hom ≫ p) := Over.homMk (𝟙 _) (by simp)
  let ρ : (baseOver (Sp F) ⟶ P'.A) →* (Over.mk p ⟶ P.A) := MonoidHom.mk' (fun x => c ≫ toBase hg.w x)
    fun x y => by rw [pm, MonObj.comp_mul]
  have hρ : ∀ x, (ptSecT P.A (ρ x)).left = x.left ≫ e.hom := fun x => by
    refine hg'.hom_ext ?_ ?_
    · rw [← Over.comp_left, ptSecT, lift_snd, Category.assoc, e₁]
      exact Category.id_comp _
    · rw [← Over.comp_left, ptSecT, lift_fst, Category.assoc, e₂]
      exact (Over.w x).symm
  have key : ∀ x, ptSecT P.A (ρ x) ≫ h = ptSecT P.A (ρ x) → x ≫ σ = x := fun x hx => by
    have := congrArg (·.left) hx
    simp only [Over.comp_left, hρ] at this
    refine Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)
    rw [Over.comp_left, Category.assoc, hσ, ← Category.assoc, this]
  have hη : (1 : baseOver (Sp F) ⟶ P'.A) = η[P'.A] :=
    (congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)
  have : IsMonHom (σ : P'.A ⟶ P'.A) := laws.rigidity _ _ _ P'.isAb P'.isAb σ (by
    have := key 1 (by rw [map_one]; exact h0)
    rwa [hη] at this)
  have h1 : σ = 1 := eq_one_of_field_any laws P' hMp hM hMF σ (m := n) (by omega)
    (Over.OverMorphism.ext ((cancel_mono e.hom).1 ((hpow n).trans (by rw [hord]; exact (hpow 0).symm))))
    fun x hx => key x (hfix _ (by rw [← map_pow, hx, map_one]))
  refine Over.OverMorphism.ext ((cancel_epi e.hom).1 ?_)
  rw [← hσ, h1]
  exact hpow 0

end

section
open GlobalTheory.InducedTranslation

/- English proof (translation)
Take `⟨a, ha⟩ : ∃ a, a = ptSecT P.A 1 ≫ ψ ≫ snd _ _` from `⟨_, rfl⟩`. Take `⟨h, hh⟩ : ∃ h : CategoryTheory.End (Over.mk p ⊗ P.A), h = ψ ≫ translT P.A a⁻¹` from `⟨_, rfl⟩`. Establish `hfst : h ≫ fst _ _ = fst _ _` using `by rw [hh, Category.assoc, translT_fst, hψ]`. Establish `h0 : ptSecT P.A 1 ≫ h = ptSecT P.A 1`. Rewrite using `[hh, ← Category.assoc, ptSecT, eq_lift hψ, lift_translT, Category.id_comp, ← ptSecT, ← ptSecT, ← ha, inv_mul_cancel]`.

Establish `hψh : ψ = h ≫ translT P.A a`. Rewrite using `[hh, Category.assoc, translT_comp, mul_inv_cancel, translT_one, Category.comp_id]`. Establish `hmul` using `fun {Z} (t : Z ⟶ Over.mk p) => map_mul_of_fix_origin hL.1 P h hfst h0 t`. Establish `hcomm : ∀ x, translT P.A x ≫ h = h ≫ translT P.A (ptSecT P.A x ≫ h ≫ snd _ _)` using `fun x => end_ext (by`. Rewrite using `[← Category.assoc, lift_translT, eq_lift hfst, hmul, ← Category.assoc (lift _ _) h (translT _ _), eq_lift hfst, lift_translT, ptSecT, ← Category.assoc (fst _ _), comp_lift, Category.comp_id])`.

Establish `hpow : ∀ n : ℕ, ∃ x, (ψ ^ n : CategoryTheory.End _) = (h ^ n : CategoryTheory.End _) ≫ translT P.A x` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨1, by rw [translT_one, Category.comp_id, pow_zero, pow_zero]⟩`. Consider the case `succ n ih`. Take `⟨x, hx⟩` from `ih`.

Use `⟨a * (ptSecT P.A x ≫ h ≫ snd _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', pow_succ', End.mul_def, End.mul_def, hx, ← translT_comp, Category.assoc, Category.assoc, ← Category.assoc h, ← hcomm, Category.assoc, ← hψh]`. Establish `h0' : ∀ n : ℕ, ptSecT P.A 1 ≫ (h ^ n : CategoryTheory.End _) = ptSecT P.A 1` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => exact Category.comp_id _`.

Consider the case `succ n ih => rw [pow_succ', End.mul_def, ← Category.assoc, ih, h0]`. Establish `hhN : h ^ N = 1`. Take `⟨x, hx⟩` from `hpow N`. Establish `e` using `congrArg (ptSecT P.A 1 ≫ · ≫ snd _ _) hx`. Simplify using `only [hord] at e`.

Rewrite `e` using `[End.one_def, Category.id_comp, ← Category.assoc, ← Category.assoc, h0', ptSecT, lift_translT, lift_snd, lift_snd, Category.id_comp, _root_.mul_one]`. Rewrite `hx` using `[← e, translT_one, Category.comp_id, hord]`. Conclude with `hx.symm`. Set `φ : (Over.mk p ⟶ P.A) →* (Over.mk p ⟶ P.A)` to `MonoidHom.mk' (fun x => ptSecT P.A x ≫ h ≫ snd _ _) (hmul (𝟙 _))`. Set `f : {x : Over.mk p ⟶ P.A // x ^ M = 1} → {x : Over.mk p ⟶ P.A // x ^ M = 1}` to `fun x => ⟨φ x.1, by rw [← map_pow, x.2, map_one]⟩`.

Establish `hf : ∀ (n : ℕ) x, ptSecT P.A (f^[n] x).1 = ptSecT P.A x.1 ≫ (h ^ n : CategoryTheory.End _)` using `fun n x => by`. Proceed by induction on `n with`. Consider the case `zero => exact (Category.comp_id _).symm`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', pow_succ', End.mul_def, ← Category.assoc, ← ih]`.

Conclude with `(eq_lift hfst _ _).symm`. Establish `hinj : Function.Injective f`. Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by omega⟩`. Use `Function.LeftInverse.injective (g := f^[n]) fun x => Subtype.ext ?_` and prove the remaining obligations. Establish `e` using `congrArg (· ≫ snd _ _) (hf (n + 1) x)`.

Simplify using `only [hhN] at e`. Rewrite `e` using `[End.one_def, Category.comp_id, ptSecT, ptSecT, lift_snd, lift_snd]`. Then use the resulting hypothesis. Set `π : Equiv.Perm _` to `Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)`. Establish `hπ : π ^ m = 1`. Take `⟨c, rfl⟩` from `hm`.

Rewrite using `[pow_mul, pow_card_eq_one', one_pow]`. Establish `h1 : h ^ m = 1` using `eq_one_of_finite_order_any hL S P F M hMp hM hMF p (h ^ m) (pow_fst h hfst m) (h0' m) ⟨N, hN, by rw [← pow_mul, mul_comm, pow_mul, hhN, one_pow]⟩ fun x hx => by`. Establish `e : f^[m] ⟨x, hx⟩ = ⟨x, hx⟩`. Use `congrArg (fun s : Equiv.Perm _ => s ⟨x, hx⟩) hπ` as an intermediate fact. Simplify using `only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at this`.

Conclude with `this`. Rewrite using `[← hf m ⟨x, hx⟩, e]`. Take `⟨x, hx⟩` from `hpow m`. Conclude with `⟨x, by rw [hx, h1, End.one_def, Category.id_comp]⟩`.
-/
theorem exists_pow_eq_translT_any (hL : LL) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] {M : ℕ} (hMp : M.Prime) (hM : 3 ≤ M) (hMF : (M : F) ≠ 0) (p : Spec (CommRingCat.of F) ⟶ S)
    [Finite {x : Over.mk p ⟶ P.A // x ^ M = 1}] (ψ : CategoryTheory.End (Over.mk p ⊗ P.A))
    (hψ : ψ ≫ fst _ _ = fst _ _) {N : ℕ} (hN : 1 ≤ N) (hord : ψ ^ N = 1) {m : ℕ}
    (hm : Nat.card (Equiv.Perm {x : Over.mk p ⟶ P.A // x ^ M = 1}) ∣ m) :
    ∃ x : Over.mk p ⟶ P.A, (ψ ^ m : CategoryTheory.End _) = translT P.A x := by
  obtain ⟨a, ha⟩ : ∃ a, a = ptSecT P.A 1 ≫ ψ ≫ snd _ _ := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : CategoryTheory.End (Over.mk p ⊗ P.A), h = ψ ≫ translT P.A a⁻¹ := ⟨_, rfl⟩
  have hfst : h ≫ fst _ _ = fst _ _ := by rw [hh, Category.assoc, translT_fst, hψ]
  have h0 : ptSecT P.A 1 ≫ h = ptSecT P.A 1 := by
    rw [hh, ← Category.assoc, ptSecT, eq_lift hψ, lift_translT, Category.id_comp, ← ptSecT, ← ptSecT, ← ha,
      inv_mul_cancel]
  have hψh : ψ = h ≫ translT P.A a := by
    rw [hh, Category.assoc, translT_comp, mul_inv_cancel, translT_one, Category.comp_id]
  have hmul := fun {Z} (t : Z ⟶ Over.mk p) => map_mul_of_fix_origin hL.1 P h hfst h0 t
  have hcomm : ∀ x, translT P.A x ≫ h = h ≫ translT P.A (ptSecT P.A x ≫ h ≫ snd _ _) := fun x => end_ext (by
    rw [← Category.assoc, lift_translT, eq_lift hfst, hmul, ← Category.assoc (lift _ _) h (translT _ _), eq_lift hfst,
      lift_translT, ptSecT, ← Category.assoc (fst _ _), comp_lift, Category.comp_id])
  have hpow : ∀ n : ℕ, ∃ x, (ψ ^ n : CategoryTheory.End _) = (h ^ n : CategoryTheory.End _) ≫ translT P.A x :=
    fun n => by
    induction n with
    | zero => exact ⟨1, by rw [translT_one, Category.comp_id, pow_zero, pow_zero]⟩
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      refine ⟨a * (ptSecT P.A x ≫ h ≫ snd _ _), ?_⟩
      rw [pow_succ', pow_succ', End.mul_def, End.mul_def, hx, ← translT_comp, Category.assoc, Category.assoc,
        ← Category.assoc h, ← hcomm, Category.assoc, ← hψh]
  have h0' : ∀ n : ℕ, ptSecT P.A 1 ≫ (h ^ n : CategoryTheory.End _) = ptSecT P.A 1 := fun n => by
    induction n with
    | zero => exact Category.comp_id _
    | succ n ih => rw [pow_succ', End.mul_def, ← Category.assoc, ih, h0]
  have hhN : h ^ N = 1 := by
    obtain ⟨x, hx⟩ := hpow N
    have e := congrArg (ptSecT P.A 1 ≫ · ≫ snd _ _) hx
    simp only [hord] at e
    rw [End.one_def, Category.id_comp, ← Category.assoc, ← Category.assoc, h0', ptSecT, lift_translT, lift_snd,
      lift_snd, Category.id_comp, _root_.mul_one] at e
    rw [← e, translT_one, Category.comp_id, hord] at hx
    exact hx.symm
  let φ : (Over.mk p ⟶ P.A) →* (Over.mk p ⟶ P.A) :=
    MonoidHom.mk' (fun x => ptSecT P.A x ≫ h ≫ snd _ _) (hmul (𝟙 _))
  let f : {x : Over.mk p ⟶ P.A // x ^ M = 1} → {x : Over.mk p ⟶ P.A // x ^ M = 1} :=
    fun x => ⟨φ x.1, by rw [← map_pow, x.2, map_one]⟩
  have hf : ∀ (n : ℕ) x, ptSecT P.A (f^[n] x).1 = ptSecT P.A x.1 ≫ (h ^ n : CategoryTheory.End _) := fun n x => by
    induction n with
    | zero => exact (Category.comp_id _).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ', End.mul_def, ← Category.assoc, ← ih]
      exact (eq_lift hfst _ _).symm
  have hinj : Function.Injective f := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    refine Function.LeftInverse.injective (g := f^[n]) fun x => Subtype.ext ?_
    have e := congrArg (· ≫ snd _ _) (hf (n + 1) x)
    simp only [hhN] at e
    rwa [End.one_def, Category.comp_id, ptSecT, ptSecT, lift_snd, lift_snd] at e
  let π : Equiv.Perm _ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hπ : π ^ m = 1 := by
    obtain ⟨c, rfl⟩ := hm
    rw [pow_mul, pow_card_eq_one', one_pow]
  have h1 : h ^ m = 1 := eq_one_of_finite_order_any hL S P F M hMp hM hMF p (h ^ m)
    (pow_fst h hfst m) (h0' m) ⟨N, hN, by rw [← pow_mul, mul_comm, pow_mul, hhN, one_pow]⟩ fun x hx => by
      have e : f^[m] ⟨x, hx⟩ = ⟨x, hx⟩ := by
        have := congrArg (fun s : Equiv.Perm _ => s ⟨x, hx⟩) hπ
        simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at this
        exact this
      rw [← hf m ⟨x, hx⟩, e]
  obtain ⟨x, hx⟩ := hpow m
  exact ⟨x, by rw [hx, h1, End.one_def, Category.id_comp]⟩

/- English proof (translation)
Introduce `hL R _ _ I hR D A G _ _ hG U F _ _ _ k hk p`. Take `⟨M, hMp, hM, hMF⟩` from `exists_odd_prime_ne_zero F`. Establish `hcard` using `(hL.1.mulN _ A M (by omega)).2.2.2.2 F (jFK (R := R) F) hMF`. Establish `: Finite {x : Over.mk (jFK (R` using `R) F) ⟶ A.A // x ^ M = 1} := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`. Take `⟨m, hm4, hm⟩ : ∃ m, 4 ≤ m ∧ Nat.card (Equiv.Perm {x : Over.mk (jFK (R` from `R) F) ⟶ A.A // x ^ M = 1}) ∣ m := ⟨4 * _, Nat.le_mul_of_pos_right _ Nat.card_pos, Dvd.intro_left _ rfl⟩`.

Establish `hN : 4 ≤ k * m` using `hm4.trans (Nat.le_mul_of_pos_left _ hk)`. Take `⟨g', hg'⟩` from `(gtOnto_any hL R I hR D F).2.1 m (by omega) p.g`. Take `⟨ψ, hψ⟩` from `existsAut_any hL R I hR D A G hG U F k hk p`. Take `⟨τ, q, h1, hord, e⟩` from `eq_pow_of_rel D.tau_bimult p g' hg' (E := CategoryTheory.End (TFK (R := R) F ⊗ A.A)) (IndAt U.toUnifPre F (k * m)) (fun a b c s t hs => by`. Take `⟨c₁, c₂, c₃, c₄⟩` from `indAtComp_any hL R I hR D A G hG U F (k * m) (by omega) a b c s t hs`.

Conclude with `⟨c₁, c₂, c₃ hN, c₄⟩)`. Use the proof step `(fun q => by`. Take `⟨χ, hχ⟩` from `existsAut_any hL R I hR D A G hG U F (k * m) (by omega) q`. Conclude with `⟨χ.hom, hχ 1 (k * m) le_rfl (_root_.mul_one _).symm q (one_nsmul _).symm rfl⟩)`. Use the proof step `ψ.hom (hψ m _ (by omega) rfl)`.

Take `⟨x, hx⟩` from `exists_pow_eq_translT_any hL A hMp hM hMF (jFK (R := R) F) τ h1.1 (by omega : 1 ≤ k * m) hord hm`. Establish `e' : ψ.hom = translT A.A x` using `e.trans hx`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← e']`. Conclude with `hψ`.
-/
theorem existsTransl_any :
    LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q (translT A.A x) := by
  intro hL R _ _ I hR D A G _ _ hG U F _ _ _ k hk p
  obtain ⟨M, hMp, hM, hMF⟩ := exists_odd_prime_ne_zero F
  have hcard := (hL.1.mulN _ A M (by omega)).2.2.2.2 F (jFK (R := R) F) hMF
  have : Finite {x : Over.mk (jFK (R := R) F) ⟶ A.A // x ^ M = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨m, hm4, hm⟩ : ∃ m, 4 ≤ m ∧
      Nat.card (Equiv.Perm {x : Over.mk (jFK (R := R) F) ⟶ A.A // x ^ M = 1}) ∣ m :=
    ⟨4 * _, Nat.le_mul_of_pos_right _ Nat.card_pos, Dvd.intro_left _ rfl⟩
  have hN : 4 ≤ k * m := hm4.trans (Nat.le_mul_of_pos_left _ hk)
  obtain ⟨g', hg'⟩ := (gtOnto_any hL R I hR D F).2.1 m (by omega) p.g
  obtain ⟨ψ, hψ⟩ := existsAut_any hL R I hR D A G hG U F k hk p
  obtain ⟨τ, q, h1, hord, e⟩ := eq_pow_of_rel D.tau_bimult p g' hg'
    (E := CategoryTheory.End (TFK (R := R) F ⊗ A.A)) (IndAt U.toUnifPre F (k * m))
    (fun a b c s t hs => by
      obtain ⟨c₁, c₂, c₃, c₄⟩ := indAtComp_any hL R I hR D A G hG U F (k * m) (by omega) a b c s t hs
      exact ⟨c₁, c₂, c₃ hN, c₄⟩)
    (fun q => by
      obtain ⟨χ, hχ⟩ := existsAut_any hL R I hR D A G hG U F (k * m) (by omega) q
      exact ⟨χ.hom, hχ 1 (k * m) le_rfl (_root_.mul_one _).symm q (one_nsmul _).symm rfl⟩)
    ψ.hom (hψ m _ (by omega) rfl)
  obtain ⟨x, hx⟩ := exists_pow_eq_translT_any hL A hMp hM hMF (jFK (R := R) F) τ h1.1 (by omega : 1 ≤ k * m) hord hm
  have e' : ψ.hom = translT A.A x := e.trans hx
  refine ⟨x, ?_⟩
  rw [← e']
  exact hψ

end

section
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

/- English proof (translation)
Introduce `hL R _ _ I hA D F _ _ _ k hkF`. Establish `hk : 1 ≤ k` using `Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact hkF Nat.cast_zero)`. Establish `: IsNoetherianRing R` using `hA.1`. Establish `h₁` using `(GlobalTheory.GtCount.card_gtTors hL.1 hL.2.1 R D.toPre F k hkF).1`. Simplify using `only [GlobalTheory.GtCount.gtTors_iff] at h₁`.

Establish `h₂` using `(gtOnto_any hL R I hA D F).2.1 k hk`. Rewrite using `[card_qk_eq_mul D.tau_bimult (by omega) fun y => (h₂ _).imp fun _ e => ((isNsmul_iff_eq _ _ _).1 e).symm, h₁, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cardQk_any : LL → AnyD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), (k : F) ≠ 0 → Nat.card (Quot (QkPt.Equiv D.toPre F (k := k))) = k ^ (2 * (D.toPre.rank + D.toPre.P.g)) := by
  intro hL R _ _ I hA D F _ _ _ k hkF
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact hkF Nat.cast_zero)
  have : IsNoetherianRing R := hA.1
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL.1 hL.2.1 R D.toPre F k hkF).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  have h₂ := (gtOnto_any hL R I hA D F).2.1 k hk
  rw [card_qk_eq_mul D.tau_bimult (by omega) fun y => (h₂ _).imp fun _ e => ((isNsmul_iff_eq _ _ _).1 e).symm, h₁,
    ← pow_add]
  congr 1
  ring

end

/- English proof (translation)
Introduce `R _ _ I hI D A G _ _ hG U F _ _ _ k hkF`. Establish `hL` using `GlobalTheory.firstFiveLaws`. Establish `hk : 1 ≤ k` using `Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact hkF Nat.cast_zero)`. Establish `hqk` using `indAtTransl_any hL R I hI D A G hG U F k hk`. Establish `hcomp` using `indAtComp_any hL R I hI D A G hG U F k hk`.

Establish `huniq` using `GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk`. Establish `hinj` using `GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 R I hI D A G hG U F k hk`. Establish `hex : ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U.toUnifPre F k p x` using `fun p => by`. Take `⟨x, hx⟩` from `existsTransl_any hL R I hI D A G hG U F k hk p`. Conclude with `⟨x, (hqk p x).1 (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩`.

Use `choose f hf using hex`. Establish `hwd : ∀ p p', QkPt.Equiv D.toPre F p p' → f p = f p'` using `fun p p' h => huniq p' _ _ ((hqk _ _).1 ((hcomp p p' p' _ (𝟙 _) ((hqk _ _).2 (hf p))).2.1 h)) (hf p')`. Establish `hpow : ∀ p, f p ^ k = 1` using `fun p => by`. Take `⟨w, hw⟩` from `U.ext`. Conclude with `(hf p w hw).1`.

Establish `hA` using `(hL.1.mulN _ A k hk).2.2.2.2 F (jFK (R := R) F) hkF`. Establish `hQ` using `cardQk_any hL R I hI D F k hkF`. Establish `hd` using `dimEq_any hL R I hI D A G hG U`. Set `φ : Quot (QkPt.Equiv D.toPre F (k` to `k)) → {x : TFK (R := R) F ⟶ A.A // x ^ k = 1} := Quot.lift (fun p => ⟨f p, hpow p⟩) (fun p p' h => Subtype.ext (hwd p p' h))`. Establish `hφ : Function.Injective φ`.

Introduce and unpack `⟨p⟩ ⟨p'⟩ h`. Establish `h' : f p = f p'` using `congrArg Subtype.val h`. Conclude with `Quot.sound (hinj p p' (f p) (hf p) (h' ▸ hf p'))`. Use `haveI : Finite {x : TFK (R := R) F ⟶ A.A // x ^ k = 1} := Nat.finite_of_card_ne_zero (by rw [hA]; positivity)`. Establish `hb : Function.Bijective φ` using `hφ.bijective_of_nat_card_le (by rw [hA, hQ, hd])`.

Introduce `x hx`. Take `⟨⟨p⟩, hp⟩` from `hb.2 ⟨x, hx⟩`. Take `rfl : f p = x` from `congrArg Subtype.val hp`. Conclude with `⟨p, hf p⟩`.
-/
theorem exists_qkToAkU : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), (k : F) ≠ 0 → ∀ x : TFK (R := R) F ⟶ A.A, x ^ k = 1 → ∃ p : QkPt D.toPre F k, QkToAkU U.toUnifPre F k p x := by
  intro R _ _ I hI D A G _ _ hG U F _ _ _ k hkF
  have hL := GlobalTheory.firstFiveLaws
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact hkF Nat.cast_zero)
  have hqk := indAtTransl_any hL R I hI D A G hG U F k hk
  have hcomp := indAtComp_any hL R I hI D A G hG U F k hk
  have huniq := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hinj := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hex : ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U.toUnifPre F k p x := fun p => by
    obtain ⟨x, hx⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
    exact ⟨x, (hqk p x).1 (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩
  choose f hf using hex
  have hwd : ∀ p p', QkPt.Equiv D.toPre F p p' → f p = f p' := fun p p' h =>
    huniq p' _ _ ((hqk _ _).1 ((hcomp p p' p' _ (𝟙 _) ((hqk _ _).2 (hf p))).2.1 h)) (hf p')
  have hpow : ∀ p, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.ext
    exact (hf p w hw).1
  have hA := (hL.1.mulN _ A k hk).2.2.2.2 F (jFK (R := R) F) hkF
  have hQ := cardQk_any hL R I hI D F k hkF
  have hd := dimEq_any hL R I hI D A G hG U
  let φ : Quot (QkPt.Equiv D.toPre F (k := k)) → {x : TFK (R := R) F ⟶ A.A // x ^ k = 1} :=
    Quot.lift (fun p => ⟨f p, hpow p⟩) (fun p p' h => Subtype.ext (hwd p p' h))
  have hφ : Function.Injective φ := by
    rintro ⟨p⟩ ⟨p'⟩ h
    have h' : f p = f p' := congrArg Subtype.val h
    exact Quot.sound (hinj p p' (f p) (hf p) (h' ▸ hf p'))
  haveI : Finite {x : TFK (R := R) F ⟶ A.A // x ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hA]; positivity)
  have hb : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hA, hQ, hd])
  intro x hx
  obtain ⟨⟨p⟩, hp⟩ := hb.2 ⟨x, hx⟩
  obtain rfl : f p = x := congrArg Subtype.val hp
  exact ⟨p, hf p⟩

end GlobalTheory.TorsionAnyChar
