import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefFE
open GlobalTheory.UT.CoefBasic

/- English proof (translation)
Introduce `hL R _ _ D F _ _ k y h o hh ho w w₁ hw hw₁ vw s α`. Take `⟨hb, hs⟩` from `(isIota_iff _ _).1 hh`. Take `⟨ob, os⟩` from `(isZero_iff _).1 ho`. Take `⟨⟨u, hu, hc⟩, -⟩` from `gen_fe (D := D) (F := F) hL.1.globalFns k y α`. Use `coef_eq fun z J hJ => ?_` and prove the remaining obligations.

Establish `e` using `(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _ (DegPre.zF D F).left z J hJ`. Establish `u₀` using `val_corr hJ hc (𝟙 _)`. Rewrite `u₀` using `[val_pull hJ, Category.id_comp]`. Establish `m` using `val_famMult (𝟙 (TF (R := R) F)) hJ k y α`. Establish `p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) ((𝟙 (TF (R` using `R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J = val (D.psi y) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _`.

Establish `p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((𝟙 (TF (R` using `R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J = val D.rigK ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _`. Rewrite `m` using `[p₁, p₂, Over.id_left, Category.id_comp]`. Establish `r : val D.rigK (jFK (R` using `R) F) z J = rigV D (TF (R := R) F).hom z J := val_pull hJ _ _ _`. Establish `z₁ : lift (𝟙 (TF (R` using `R) F)) o.b = DegPre.zF D F := by rw [ob]; rfl`. Establish `z₂ : DegPre.zF D F ≫ DegPre.trF D F y = lift (𝟙 (TF (R` using `R) F)) h.b := by`.

Establish `a₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _` using `lift_fst _ _`. Establish `a₂ : DegPre.zF D F ≫ DegPre.prB D F = 1` using `lift_snd _ _`. Rewrite using `[trF_eq]`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, tr_fst, a₁, lift_fst]`.

Rewrite using `[lift_snd, hb, Category.assoc]`. Use `(congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul, a₂, ← Category.assoc, a₁, Category.id_comp, _root_.one_mul]`. Rewrite `e` using `[← Over.comp_left, z₂, u₀]`. Establish `t` using `hs α z J hJ`.

Rewrite `t` using `[Category.id_comp]`. Rewrite using `[isCoef_coef h hw α s z J hJ, z₁, e, os _ z J hJ, hw₁.2 z J hJ, t, vw z J hJ]`. Establish `m'` using `congrArg Units.val m`. Rewrite `m'` using `[r]`. Simplify using `only [Units.val_one, _root_.mul_one, id, mul_pow, _root_.mul_assoc]`.

Conclude with `congrArg₂ (· * ·) rfl m'.symm`.
-/
theorem coef_fe : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (h o : GtPtF D F), GtPtF.IsIota y h → o.IsZero → ∀ (w : Frm D F k h.b) (w₁ : Frm D F k o.b), w.IsGen → FrmOne w₁ → (∀ z J, Good D.P.L z J → val w (𝟙 _) z J = (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi y) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) ^ k) → ∀ (s : Fam D F k) (α : D.X), coef s o w₁ (α + k • y) = coef s h w α := by
  intro hL R _ _ D F _ _ k y h o hh ho w w₁ hw hw₁ vw s α
  obtain ⟨hb, hs⟩ := (isIota_iff _ _).1 hh
  obtain ⟨ob, os⟩ := (isZero_iff _).1 ho
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hL.1.globalFns k y α
  refine coef_eq fun z J hJ => ?_
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe y α u hu hc) _ (DegPre.zF D F).left z J hJ
  have u₀ := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at u₀
  have m := val_famMult (𝟙 (TF (R := R) F)) hJ k y α
  have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi y) k) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J =
      val (D.psi y) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _
  have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J =
      val D.rigK ((𝟙 (TF (R := R) F) : _ ⟶ _).left ≫ jFK (R := R) F) z J ^ k := map_pow _ _ _
  rw [p₁, p₂, Over.id_left, Category.id_comp] at m
  have r : val D.rigK (jFK (R := R) F) z J = rigV D (TF (R := R) F).hom z J := val_pull hJ _ _ _
  have z₁ : lift (𝟙 (TF (R := R) F)) o.b = DegPre.zF D F := by rw [ob]; rfl
  have z₂ : DegPre.zF D F ≫ DegPre.trF D F y = lift (𝟙 (TF (R := R) F)) h.b := by
    have a₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    have a₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
    rw [trF_eq]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, a₁, lift_fst]
    · rw [lift_snd, hb, Category.assoc]
      refine (congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_
      rw [MonObj.comp_mul, a₂, ← Category.assoc, a₁, Category.id_comp, _root_.one_mul]
  rw [← Over.comp_left, z₂, u₀] at e
  have t := hs α z J hJ
  rw [Category.id_comp] at t
  rw [isCoef_coef h hw α s z J hJ, z₁, e, os _ z J hJ, hw₁.2 z J hJ, t, vw z J hJ]
  have m' := congrArg Units.val m
  rw [r] at m'
  simp only [Units.val_one, _root_.mul_one, id, mul_pow, _root_.mul_assoc]
  exact congrArg₂ (· * ·) rfl m'.symm

end GlobalTheory.UT.CoefFE
end
