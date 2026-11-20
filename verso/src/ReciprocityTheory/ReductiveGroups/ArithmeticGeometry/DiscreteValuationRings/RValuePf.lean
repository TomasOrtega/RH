import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RValue
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section RV

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

/- English proof (translation)
Establish `h` using `D.toPre.c_add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.1 h.symm`.
-/
theorem rv_c_zero : D.toPre.c 0 = 1 := by
  have h := D.toPre.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

/- English proof (translation)
Establish `e : (Over.homMk (jFK (R` using `V) F) rfl : TF (R := V) F ⟶ TK V) ≫ lift (toUnit (TK V) ≫ D.toPre.c x) (toUnit (TK V) ≫ D.toPre.c y) = lift (toUnit _ ≫ D.toPre.c x) (toUnit _ ≫ D.toPre.c y) := by`. Rewrite using `[comp_lift, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit (TK V)) (toUnit _)]`. Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem rv_pt (x y : D.toPre.X) :
    (lift (toUnit (TF (R := V) F) ≫ D.toPre.c x) (toUnit (TF (R := V) F) ≫ D.toPre.c y) :
      TF (R := V) F ⟶ D.toPre.P.A ⊗ D.toPre.P.A).left = jFK (R := V) F ≫ D.toPre.pt2 x y := by
  have e : (Over.homMk (jFK (R := V) F) rfl : TF (R := V) F ⟶ TK V) ≫
      lift (toUnit (TK V) ≫ D.toPre.c x) (toUnit (TK V) ≫ D.toPre.c y) =
      lift (toUnit _ ≫ D.toPre.c x) (toUnit _ ≫ D.toPre.c y) := by
    rw [comp_lift, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit (TK V)) (toUnit _)]
  rw [← e]; rfl

/- English proof (translation)
Unfold `DegPre.tau`. Rewrite using `[val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv, congrArg (fun w => val (D.toPre.psi w) r z J) (add_zero x), mul_inv_cancel, _root_.one_mul]`.
-/
theorem rv_val_tau_zero (x : D.toPre.X) {Z : Scheme.{0}} (r : Z ⟶ (TK V).left) (z : Z)
    {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} (hJ : Good D.toPre.P.L z J) :
    val (D.toPre.tau x 0) r z J = (val (D.toPre.psi 0) r z J)⁻¹ * (val D.toPre.rigK r z J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
    congrArg (fun w => val (D.toPre.psi w) r z J) (add_zero x), mul_inv_cancel, _root_.one_mul]

/- English proof (translation)
Establish `hL` using `D.toPre.P.isLB`. Establish `hb` using `oa.tau_bal (star a)`. Rewrite `hb` using `[star_star]`. Use `corr_of_val hL fun y J hJ => ?_` and prove the remaining obligations. Unfold `rFac`.

Rewrite using `[val_pull hJ, val_pull hJ, val_one]`. Establish `hc` using `val_corr hJ (hb uR huR hn χ 0) (jFK (R := V) F)`. Simplify using `only at hc`. Establish `h0 : a • (0 : D.toPre.X) = 0` using `smul_zero a`. Rewrite `hc` using `[h0]`.

Rewrite `hc` using `[val_mul hJ, val_pull hJ, rv_val_tau_zero _ _ _ hJ, rv_val_tau_zero _ _ _ hJ]`. Establish `hm : (𝟙 _ ≫ (DegPre.zF D.toPre F).left) ≫ (lift (cPB D F χ) (DegPre.prB D.toPre F)).left = jFK (R` using `V) F ≫ D.toPre.pt2 χ 0 := by`. Establish `z₁ : DegPre.zF D.toPre F ≫ cPB D F χ = toUnit _ ≫ D.toPre.c χ`. Rewrite using `[cPB, ← Category.assoc, comp_toUnit]`. Establish `z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1` using `lift_snd _ _`.

Rewrite using `[Category.id_comp, ← Over.comp_left, comp_lift, z₁, z₂, ← rv_pt, rv_c_zero, MonObj.comp_one]`. Rewrite using `[hm]`. Conclude with `mul_eq_left.1 hc`.
-/
theorem rFac_zero_pf (oa : D.toPre.OAct O) (a : O)
    (uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (huR : uR.IsGen)
    (hn : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uR (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (χ : D.toPre.X) :
    LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L _ _ (rFac D F oa a uR χ) (DegPre.zF D.toPre F).left) (LB.oneGen D.toPre.P.L) := by
  have hL := D.toPre.P.isLB
  have hb := oa.tau_bal (star a)
  rw [star_star] at hb
  refine corr_of_val hL fun y J hJ => ?_
  unfold rFac
  rw [val_pull hJ, val_pull hJ, val_one]
  have hc := val_corr hJ (hb uR huR hn χ 0) (jFK (R := V) F)
  simp only at hc
  have h0 : a • (0 : D.toPre.X) = 0 := smul_zero a
  rw [h0] at hc
  rw [val_mul hJ, val_pull hJ, rv_val_tau_zero _ _ _ hJ, rv_val_tau_zero _ _ _ hJ] at hc
  have hm : (𝟙 _ ≫ (DegPre.zF D.toPre F).left) ≫ (lift (cPB D F χ) (DegPre.prB D.toPre F)).left =
      jFK (R := V) F ≫ D.toPre.pt2 χ 0 := by
    have z₁ : DegPre.zF D.toPre F ≫ cPB D F χ = toUnit _ ≫ D.toPre.c χ := by
      rw [cPB, ← Category.assoc, comp_toUnit]
    have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
    rw [Category.id_comp, ← Over.comp_left, comp_lift, z₁, z₂, ← rv_pt, rv_c_zero, MonObj.comp_one]
  rw [hm]
  exact mul_eq_left.1 hc

end RV

end ReciprocityTheory.ChartRestriction.G.DVR
