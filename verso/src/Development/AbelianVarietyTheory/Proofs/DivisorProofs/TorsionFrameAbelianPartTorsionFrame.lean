import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.FinExtHomInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullMulValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerSectionNonzeroAtOriginStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Tors.FrameTors

/- English proof (translation)
Introduce `_ _` and use `(map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm`.
-/
theorem oneGen_isGen' {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

/- English proof (translation)
Introduce `_ _ _` and use `Finset.prod_congr rfl fun i _ => by rw [h i]`.
-/
theorem formEq_of_eq {X Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (h : ∀ i, ε i = ε' i) : FormEq φ ε φ ε' := fun _ _ _ =>
  Finset.prod_congr rfl fun i _ => by rw [h i]

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Establish `hb : o.b = 1` using `((isZero_iff o).1 ho).1`. Establish `hgN : g.b ^ N = 1` using `(GlobalTheory.UU.RelTests.isNsmul_b hg).symm.trans hb`. Establish `e1 : g.b.left ≫ (𝟙 D.P.A ^ N).left = (1 : TF (R` using `R) F ⟶ D.P.A).left := by`. Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id, hgN]`. Establish `e2 : g.b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (1 : TF (R` using `R) F ⟶ D.P.A).left := by`.

Rewrite using `[← Over.comp_left, MonObj.comp_one]`. Establish `e0 : (DegPre.zeroF D F).left = (1 : TF (R` using `R) F ⟶ D.P.A).left := rfl`. Take `⟨c, -, hc⟩` from `TWM.exists_ratio D.P.isLB (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w (N ^ 2)) (LB.pullGen D.P.L _ _ κ g.b.left)) (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hw _) (pullGen_isGen _ _ _ _ hκ.1 _)) (LB.oneGen D.P.L) (oneGen_isGen' _) (fun U _ h => by`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Fin.prod_univ_two, Fin.prod_univ_three, DegPre.lineφ, DegPre.lineε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Category.comp_id, e1, e2, e0, Finset.univ_eq_empty, Finset.prod_empty, Matrix.tail_cons, Sum.elim_inl, Sum.elim_inr]`.

Generalize the expression as in `h (Over.Hom.left (1 : TF (R := R) F ⟶ D.P.A)) = a`. Generalize the expression as in `h (Over.Hom.left g.b) = b`. Use the proof step `group)`. Use `⟨c, fun z J hJ => ?_⟩` and prove the remaining obligations. Use `hc _ (𝟙 (TF (R := R) F).left) z J hJ` as an intermediate fact.

Rewrite `this` using `[val_mul hJ, TWM.val_powGen, val_pull hJ, val_one, Units.val_one, _root_.mul_one]`. Rewrite `this` using `[Category.id_comp (Over.Hom.left g.b)]`. Conclude with `this`.
-/
theorem exists_lam {N : ℕ} {g o : GtPtF D F} (hg : GtPtF.IsNsmul N g o) (ho : o.IsZero)
    (w : Frm D F 1 g.b) (hw : w.IsGen) (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)) (hκ : Normd κ) :
    ∃ c : F, ∀ z J, Good D.P.L z J → (val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J).val = cst F z c := by
  have hb : o.b = 1 := ((isZero_iff o).1 ho).1
  have hgN : g.b ^ N = 1 := (GlobalTheory.UU.RelTests.isNsmul_b hg).symm.trans hb
  have e1 : g.b.left ≫ (𝟙 D.P.A ^ N).left = (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hgN]
  have e2 : g.b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have e0 : (DegPre.zeroF D F).left = (1 : TF (R := R) F ⟶ D.P.A).left := rfl
  obtain ⟨c, -, hc⟩ := TWM.exists_ratio D.P.isLB
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w (N ^ 2)) (LB.pullGen D.P.L _ _ κ g.b.left))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hw _) (pullGen_isGen _ _ _ _ hκ.1 _))
    (LB.oneGen D.P.L) (oneGen_isGen' _) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Fin.prod_univ_three, DegPre.lineφ, DegPre.lineε, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Category.comp_id, e1, e2, e0,
        Finset.univ_eq_empty, Finset.prod_empty, Matrix.tail_cons, Sum.elim_inl, Sum.elim_inr]
      generalize h (Over.Hom.left (1 : TF (R := R) F ⟶ D.P.A)) = a
      generalize h (Over.Hom.left g.b) = b
      group)
  refine ⟨c, fun z J hJ => ?_⟩
  have := hc _ (𝟙 (TF (R := R) F).left) z J hJ
  rw [val_mul hJ, TWM.val_powGen, val_pull hJ, val_one, Units.val_one, _root_.mul_one] at this
  rw [Category.id_comp (Over.Hom.left g.b)] at this
  exact this

end GlobalTheory.Poinc.Tors.FrameTors

namespace GlobalTheory.Poinc.Tors.FrameTors

/- English proof (translation)
Introduce `hL R _ _ _ I hI D A G _ _ hG U F _ _ w₀ ρ hN N hN1 g o hgo ho w x fr hw hlies htors κ hκ`. Take `⟨lam, hlam⟩` from `exists_lam hgo ho w hw κ hκ`. Establish `hb : o.b = 1` using `((isZero_iff o).1 ho).1`. Establish `hgN : g.b ^ N = 1` using `(GlobalTheory.UU.RelTests.isNsmul_b hgo).symm.trans hb`. Establish `e1 : g.b.left ≫ (𝟙 D.toPre.P.A ^ N).left = (1 : TF (R` using `R) F ⟶ D.toPre.P.A).left := by`.

Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id, hgN]`. Establish `e2 : g.b.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TF (R` using `R) F ⟶ D.toPre.P.A).left := by`. Rewrite using `[← Over.comp_left, MonObj.comp_one]`. Establish `e0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R` using `R) F ⟶ D.toPre.P.A).left := rfl`. Establish `key : ∀ k : ℕ, 4 ≤ k → lam ^ k = 1`.

Introduce `k hk`. Establish `hk1 : 1 ≤ k` using `by omega`. Establish `hk'1 : 1 ≤ k * N ^ 2` using `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero 2 (by omega)))`. Take `⟨t, c, hc0, htc⟩` from `GlobalTheory.T.exists_lineBundlePower_section_nonzero_at_origin hL R A F ρ hN.2.1 k hk`. Take `⟨E, hEG, hEA, hEB, hEh, hEact⟩` from `(IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 N`.

Establish `hsm : Function.Injective fun χ : D.toPre.X => N • χ` using `fun a b h => by`. Establish `h' : (N : ℤ) • a = (N : ℤ) • b` using `by simpa only [natCast_zsmul] using h`. Conclude with `smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 (by omega)) h'`. Establish `hinj : Function.Injective E.h` using `fun a b h => hsm (by simpa only [hEh] using h)`. Take `⟨β₀, hβ₀⟩` from `ThetaSum.exists_gen_pow U.LG U.cubG U.symG U.symG_gen N E.aG hEG`.

Apply the tactic sequence `obtain ⟨β, hβ, -⟩ := exists_gen U.LG.isLB (φ' := ![𝟙 _, E.aG.left]) (ε' := ![((k * N ^ 2 : ℕ) : ℤ), -(k : ℤ)]) (formEq_of_eq fun i => by fin_cases i <;> simp <;> push_cast <;> ring) (GeneratorPullback.powGen _ _ _ β₀ k) (powGen_isGen _ _ _ _ hβ₀ k)`. Take `⟨-, CT2⟩` from `coef_twistPull hL R I hI D A G hG U F E hinj (k * N ^ 2) k hk1 hk'1 ⟨β, hβ⟩`. Rewrite `CT2` using `[hEB]`. Take `⟨α', hα', hα'n, hpm⟩` from `PullMul.pull_mul_value R A F ρ hN.2.1 N k (k * N ^ 2) rfl x fr htors (mulT A.A _ N) (snd _ A.A ^ N) (lift_snd _ _) (lift_fst _ _) (by rw [MonObj.comp_pow, Category.comp_id])`. Take `⟨t', htw, htv⟩` from `hpm t c htc`.

Take `⟨e₁, he₁⟩` from `GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hk1 w₀ hN.1`. Take `⟨e₂, he₂⟩` from `GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hk'1 w₀ hN.1`. Establish `hs : U.ExpandsF F k w₀ t (e₁ t)` using `(he₁ t _).2 rfl`. Establish `hs' : U.ExpandsF F (k * N ^ 2) w₀ t' (e₂ t')` using `(he₂ t' _).2 rfl`. Apply the tactic sequence `obtain ⟨wk, hwk, hwkv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F g.b) (ε' := DegPre.lineε (k * N ^ 2)) (formEq_of_eq fun i => by fin_cases i <;> simp [DegPre.lineε]) (GeneratorPullback.powGen _ _ _ w (k * N ^ 2)) (powGen_isGen _ _ _ _ hw _)`.

Apply the tactic sequence `have hκ'e : ∃ κ' : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (k * N ^ 2) k), κ'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → val κ' r z J = val (GeneratorPullback.powGen _ _ _ κ k) r z J := exists_gen D.toPre.P.isLB (formEq_of_eq fun i …`. Take `⟨κ', hκ'g, hκ'v⟩` from `hκ'e`. Establish `hκ' : Normd κ'` using `⟨hκ'g, corr_of_val D.toPre.P.isLB fun y J hJ => by`. Rewrite using `[val_pull hJ, val_one, hκ'v _ _ y J hJ, TWM.val_powGen]`. Establish `a` using `val_corr hJ hκ.2 (𝟙 _)`.

Rewrite `a` using `[val_pull hJ, val_one]`. Rewrite using `[a, one_pow]⟩`. Take `⟨ω, hω, hωv⟩` from `exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F o.b) (ε' := DegPre.lineε k) (fun U _ h => by`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Fin.prod_univ_two, Fin.prod_univ_three, DegPre.lineφ, DegPre.lineε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Category.comp_id, e1, e2, e0, hb, Matrix.tail_cons, Sum.elim_inl, Sum.elim_inr]`.

Generalize the expression as in `h (Over.Hom.left (1 : TF (R := R) F ⟶ D.toPre.P.A)) = a`. Generalize the expression as in `h (Over.Hom.left g.b) = b`. Use the proof step `group)`. Use the proof step `(LB.mulGen _ _ _ _ _ wk (LB.pullGen _ _ _ κ' g.b.left))`. Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ hwk (pullGen_isGen _ _ _ _ hκ'g _))`.

Establish `hωm : ∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J * val κ' g.b.left z J = val ω (𝟙 _) z J` using `fun z J hJ => by`. Establish `a` using `hωv _ (𝟙 (TF (R := R) F).left) z J hJ`. Rewrite `a` using `[val_mul hJ, val_pull hJ, Category.id_comp (Over.Hom.left g.b)]`. Conclude with `a.symm`. Take `⟨q₁, q₂⟩` from `CT2 w₀ ρ hN (mulT A.A _ N) (snd _ A.A ^ N) (lift_snd _ _) (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α' hα' hα'n t t' (e₁ t) (e₂ t') hs hs' htw κ' hκ' g o ((hEact F g o).2 hgo) wk ω hwk hω hωm`.

Take `⟨w1, hw1⟩` from `(CoefBasic.coef_basic R D.toPre F k o).2.1 hb`. Establish `hωl : ∀ z J, Good D.toPre.P.L z J → (val ω (𝟙 _) z J).val = cst F z (lam ^ k)` using `fun z J hJ => by`. Rewrite using `[← hωm z J hJ, hwkv _ _ z J hJ, TWM.val_powGen, hκ'v _ _ z J hJ, TWM.val_powGen, pow_mul', ← mul_pow, Units.val_pow_eq_pow_val, hlam z J hJ, CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]`. Establish `hcoef : ∀ χ, coef (e₁ t) o ω χ = lam ^ k * coef (e₁ t) o w1 χ` using `fun χ => CoefBasic.coef_eq fun z J hJ => by`. Establish `a` using `CoefBasic.isCoef_coef o hw1.1 χ (e₁ t) z J hJ`.

Rewrite `a` using `[hw1.2 z J hJ, Units.val_one, _root_.mul_one]`. Rewrite using `[hωl z J hJ]`. Simplify using `only [CoefBasic.cst_eq, map_mul] at a ⊢`. Rewrite using `[_root_.mul_assoc, a]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsum1 : SumF I F (coef (e₂ t') g wk) c` using `hlies (k * N ^ 2) hk'1 wk (fun z J hJ => by rw [hwkv _ _ z J hJ, TWM.val_powGen]) hwk t' (e₂ t') c hs' htv`. Establish `hsum0 : SumF I F (coef (e₁ t) o w1) c` using `(sumF_origin hL R I hI D A G hG U F).2.2 w₀ ρ hN k t (e₁ t) hs o w1 ho hw1 c htc`. Establish `hre` using `((GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (coef (e₂ t') g wk) (coef (e₂ t') g wk) c c).2.2 D.toPre.X E.h hinj (fun β hβ => q₂ β hβ)).2 hsum1`. Establish `e3 : (coef (e₂ t') g wk ∘ E.h) = fun χ => (lam ^ k - 1) * coef (e₁ t) o w1 χ + coef (e₁ t) o w1 χ` using `funext fun χ => by`. Simplify using `only [Function.comp_apply, q₁, hcoef]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hre` using `[e3]`. Establish `hsc` using `(GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (coef (e₁ t) o w1) (coef (e₁ t) o w1) c c).2.1 hsum0 hsum0 (lam ^ k - 1)`. Establish `huniq` using `(GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (fun χ => (lam ^ k - 1) * coef (e₁ t) o w1 χ + coef (e₁ t) o w1 χ) (coef (e₁ t) o w1) c ((lam ^ k - 1) * c + c)).1 hre hsc`. Establish `h0 : (lam ^ k - 1) * c = 0` using `by linear_combination -huniq`.

Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hc0`. Establish `h4` using `key 4 le_rfl`. Establish `h5` using `key 5 (by norm_num)`.

Establish `hl : lam = 1`. Establish `h0 : lam ≠ 0` using `by rintro rfl; norm_num at h4`. Combine the equalities or inequalities in the displayed calculation. Use `_ = 1 := by rw [h4, h5]; norm_num`. Introduce `z J hJ`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hlam z J hJ, hl, Units.val_one, CoefBasic.cst_eq, map_one]`.
-/
theorem frame_tors : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), NormW U.toUnifPre w₀ ρ → ∀ N : ℕ, 1 ≤ N → ∀ (g o : GtPtF D.toPre F), GtPtF.IsNsmul N g o → o.IsZero → ∀ (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → LiesOver U.toUnifPre w₀ g w x fr → IsTorsFrame A ρ N x fr → ∀ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ w₀ ρ hN N hN1 g o hgo ho w x fr hw hlies htors κ hκ
  obtain ⟨lam, hlam⟩ := exists_lam hgo ho w hw κ hκ
  have hb : o.b = 1 := ((isZero_iff o).1 ho).1
  have hgN : g.b ^ N = 1 := (GlobalTheory.UU.RelTests.isNsmul_b hgo).symm.trans hb
  have e1 : g.b.left ≫ (𝟙 D.toPre.P.A ^ N).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hgN]
  have e2 : g.b.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have e0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := rfl
  have key : ∀ k : ℕ, 4 ≤ k → lam ^ k = 1 := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    have hk'1 : 1 ≤ k * N ^ 2 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero 2 (by omega)))
    obtain ⟨t, c, hc0, htc⟩ := GlobalTheory.T.exists_lineBundlePower_section_nonzero_at_origin hL R A F ρ hN.2.1 k hk
    obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 N
    have hsm : Function.Injective fun χ : D.toPre.X => N • χ := fun a b h => by
      have h' : (N : ℤ) • a = (N : ℤ) • b := by simpa only [natCast_zsmul] using h
      exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 (by omega)) h'
    have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
    obtain ⟨β₀, hβ₀⟩ := ThetaSum.exists_gen_pow U.LG U.cubG U.symG U.symG_gen N E.aG hEG
    obtain ⟨β, hβ, -⟩ := exists_gen U.LG.isLB (φ' := ![𝟙 _, E.aG.left]) (ε' := ![((k * N ^ 2 : ℕ) : ℤ), -(k : ℤ)])
      (formEq_of_eq fun i => by fin_cases i <;> simp <;> push_cast <;> ring) (GeneratorPullback.powGen _ _ _ β₀ k)
      (powGen_isGen _ _ _ _ hβ₀ k)
    obtain ⟨-, CT2⟩ := coef_twistPull hL R I hI D A G hG U F E hinj (k * N ^ 2) k hk1 hk'1 ⟨β, hβ⟩
    rw [hEB] at CT2
    obtain ⟨α', hα', hα'n, hpm⟩ := PullMul.pull_mul_value R A F ρ hN.2.1 N k (k * N ^ 2) rfl x fr htors
      (mulT A.A _ N) (snd _ A.A ^ N) (lift_snd _ _) (lift_fst _ _) (by rw [MonObj.comp_pow, Category.comp_id])
    obtain ⟨t', htw, htv⟩ := hpm t c htc
    obtain ⟨e₁, he₁⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hk1 w₀ hN.1
    obtain ⟨e₂, he₂⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hk'1 w₀ hN.1
    have hs : U.ExpandsF F k w₀ t (e₁ t) := (he₁ t _).2 rfl
    have hs' : U.ExpandsF F (k * N ^ 2) w₀ t' (e₂ t') := (he₂ t' _).2 rfl
    obtain ⟨wk, hwk, hwkv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F g.b)
      (ε' := DegPre.lineε (k * N ^ 2))
      (formEq_of_eq fun i => by fin_cases i <;> simp [DegPre.lineε]) (GeneratorPullback.powGen _ _ _ w (k * N ^ 2))
      (powGen_isGen _ _ _ _ hw _)
    have hκ'e : ∃ κ' : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (k * N ^ 2) k), κ'.IsGen ∧
        ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
          val κ' r z J = val (GeneratorPullback.powGen _ _ _ κ k) r z J :=
      exists_gen D.toPre.P.isLB (formEq_of_eq fun i => by fin_cases i <;> simp <;> push_cast <;> ring)
        (GeneratorPullback.powGen _ _ _ κ k) (powGen_isGen _ _ _ _ hκ.1 _)
    obtain ⟨κ', hκ'g, hκ'v⟩ := hκ'e
    have hκ' : Normd κ' := ⟨hκ'g, corr_of_val D.toPre.P.isLB fun y J hJ => by
      rw [val_pull hJ, val_one, hκ'v _ _ y J hJ, TWM.val_powGen]
      have a := val_corr hJ hκ.2 (𝟙 _)
      rw [val_pull hJ, val_one] at a
      rw [a, one_pow]⟩

    obtain ⟨ω, hω, hωv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F o.b) (ε' := DegPre.lineε k)
      (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Fin.prod_univ_two, Fin.prod_univ_three, DegPre.lineφ, DegPre.lineε, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Category.comp_id, e1, e2, e0, hb,
          Matrix.tail_cons, Sum.elim_inl, Sum.elim_inr]
        generalize h (Over.Hom.left (1 : TF (R := R) F ⟶ D.toPre.P.A)) = a
        generalize h (Over.Hom.left g.b) = b
        group)
      (LB.mulGen _ _ _ _ _ wk (LB.pullGen _ _ _ κ' g.b.left))
      (mulGen_isGen _ _ _ _ _ _ _ hwk (pullGen_isGen _ _ _ _ hκ'g _))
    have hωm : ∀ z J, Good D.toPre.P.L z J →
        val wk (𝟙 _) z J * val κ' g.b.left z J = val ω (𝟙 _) z J := fun z J hJ => by
      have a := hωv _ (𝟙 (TF (R := R) F).left) z J hJ
      rw [val_mul hJ, val_pull hJ, Category.id_comp (Over.Hom.left g.b)] at a
      exact a.symm
    obtain ⟨q₁, q₂⟩ := CT2 w₀ ρ hN (mulT A.A _ N) (snd _ A.A ^ N) (lift_snd _ _) (lift_fst _ _)
      (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α' hα' hα'n t t' (e₁ t) (e₂ t') hs hs' htw κ' hκ' g o
      ((hEact F g o).2 hgo) wk ω hwk hω hωm
    obtain ⟨w1, hw1⟩ := (CoefBasic.coef_basic R D.toPre F k o).2.1 hb
    have hωl : ∀ z J, Good D.toPre.P.L z J → (val ω (𝟙 _) z J).val = cst F z (lam ^ k) := fun z J hJ => by
      rw [← hωm z J hJ, hwkv _ _ z J hJ, TWM.val_powGen, hκ'v _ _ z J hJ, TWM.val_powGen, pow_mul', ← mul_pow,
        Units.val_pow_eq_pow_val, hlam z J hJ, CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]
    have hcoef : ∀ χ, coef (e₁ t) o ω χ = lam ^ k * coef (e₁ t) o w1 χ := fun χ =>
      CoefBasic.coef_eq fun z J hJ => by
        have a := CoefBasic.isCoef_coef o hw1.1 χ (e₁ t) z J hJ
        rw [hw1.2 z J hJ, Units.val_one, _root_.mul_one] at a
        rw [hωl z J hJ]
        simp only [CoefBasic.cst_eq, map_mul] at a ⊢
        rw [_root_.mul_assoc, a]
        ring
    have hsum1 : SumF I F (coef (e₂ t') g wk) c := hlies (k * N ^ 2) hk'1 wk
      (fun z J hJ => by rw [hwkv _ _ z J hJ, TWM.val_powGen]) hwk t' (e₂ t') c hs' htv
    have hsum0 : SumF I F (coef (e₁ t) o w1) c :=
      (sumF_origin hL R I hI D A G hG U F).2.2 w₀ ρ hN k t (e₁ t) hs o w1 ho hw1 c htc
    have hre := ((GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (coef (e₂ t') g wk) (coef (e₂ t') g wk) c c).2.2
      D.toPre.X E.h hinj (fun β hβ => q₂ β hβ)).2 hsum1
    have e3 : (coef (e₂ t') g wk ∘ E.h) =
        fun χ => (lam ^ k - 1) * coef (e₁ t) o w1 χ + coef (e₁ t) o w1 χ := funext fun χ => by
      simp only [Function.comp_apply, q₁, hcoef]; ring
    rw [e3] at hre
    have hsc := (GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (coef (e₁ t) o w1) (coef (e₁ t) o w1) c c).2.1
      hsum0 hsum0 (lam ^ k - 1)
    have huniq := (GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X
      (fun χ => (lam ^ k - 1) * coef (e₁ t) o w1 χ + coef (e₁ t) o w1 χ) (coef (e₁ t) o w1) c
      ((lam ^ k - 1) * c + c)).1 hre hsc
    have h0 : (lam ^ k - 1) * c = 0 := by linear_combination -huniq
    rcases mul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hc0
  have h4 := key 4 le_rfl
  have h5 := key 5 (by norm_num)
  have hl : lam = 1 := by
    have h0 : lam ≠ 0 := by rintro rfl; norm_num at h4
    calc lam = lam ^ 5 / lam ^ 4 := by field_simp
    _ = 1 := by rw [h4, h5]; norm_num
  intro z J hJ
  apply Units.ext
  rw [hlam z J hJ, hl, Units.val_one, CoefBasic.cst_eq, map_one]

end GlobalTheory.Poinc.Tors.FrameTors
