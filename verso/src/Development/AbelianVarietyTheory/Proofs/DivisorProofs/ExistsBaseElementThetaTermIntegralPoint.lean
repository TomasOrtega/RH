import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm.IntPoint

/- English proof (translation)
Establish `hx : (toUnit (TF (R` using `V) (FractionRing V))).left = jFK (R := V) (FractionRing V) ≫ jK V := by`. Simplify using `using Over.w (toUnit (TF (R := V) (FractionRing V)))`. Rewrite using `[hx]`. Use `erw [GlobalTheory.ExpansionValueZero.cst_comp]`. Use `erw [H1.gs_spec]`.

Both sides reduce to the same expression.
-/
theorem cst_toUnit (V : Type) [CommRing V] [IsDomain V] (z : (TF (R := V) (FractionRing V)).left) (a : V) :
    Geo.Tor.cst (toUnit (TF (R := V) (FractionRing V))).left z a =
      GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  have hx : (toUnit (TF (R := V) (FractionRing V))).left = jFK (R := V) (FractionRing V) ≫ jK V := by
    simpa using Over.w (toUnit (TF (R := V) (FractionRing V)))
  rw [hx]
  erw [GlobalTheory.ExpansionValueZero.cst_comp]
  erw [H1.gs_spec]
  rfl

/- English proof (translation)
Establish `hu : toUnit (𝟙_ (Over (Sp V))) = 𝟙 _` using `toUnit_unique _ _`. Establish `c0` using `ThetaOne.c_zero D`. Establish `e2 : (toUnit D.P.A ≫ D.c 0) = toUnit D.P.A ≫ η[D.P.A]`. Rewrite using `[c0, MonObj.comp_one, Hom.one_def]`. Establish `e1 : (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ η[D.P.A])) = 𝟙 D.P.A`.

Rewrite using `[← e2, c0, MonObj.comp_one, padd, ← Hom.mul_def, _root_.mul_one]`. Establish `e3 : padd D.P.A (DegPre.cT D (𝟙_ _) mu) g.b = D.c mu * g.b`. Rewrite using `[padd, ← Hom.mul_def, DegPre.cT, hu, Category.id_comp]`. Establish `e4 : DegPre.cT D (𝟙_ _) mu = D.c mu` using `by rw [DegPre.cT, hu, Category.id_comp]`. Establish `e5 : DegPre.zeroT D (𝟙_ (Over (Sp V))) = η[D.P.A]` using `by rw [DegPre.zeroT, hu, Category.id_comp]`.

Introduce `U _ h`. Simplify using `[Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, DegPre.famφB, DegPre.gtφT, DegPre.famε, DegPre.gtε, DegPre.lineε, e1, e2, e3, e4, e5]`. Establish `e6 : padd D.P.A (D.c mu) g.b = D.c mu * g.b` using `by rw [padd, ← Hom.mul_def]`. Rewrite using `[e6]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem formEq_prod {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (g : GtPt D (𝟙_ (Over (Sp V)))) (mu : D.X) :
    FormEq (fun k => (D.c mu * g.b).left ≫ D.famφB 0 k) (DegPre.famε 1)
      (Sum.elim (Sum.elim (fun _ : PUnit => (D.c mu).left) (DegPre.gtφT D (𝟙_ _) g.b mu)) ![(η[D.P.A]).left, g.b.left])
      (fun k => -(Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) DegPre.gtε) (DegPre.lineε 1)) k) := by
    have hu : toUnit (𝟙_ (Over (Sp V))) = 𝟙 _ := toUnit_unique _ _
    have c0 := ThetaOne.c_zero D
    have e2 : (toUnit D.P.A ≫ D.c 0) = toUnit D.P.A ≫ η[D.P.A] := by
      rw [c0, MonObj.comp_one, Hom.one_def]
    have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ η[D.P.A])) = 𝟙 D.P.A := by
      rw [← e2, c0, MonObj.comp_one, padd, ← Hom.mul_def, _root_.mul_one]
    have e3 : padd D.P.A (DegPre.cT D (𝟙_ _) mu) g.b = D.c mu * g.b := by
      rw [padd, ← Hom.mul_def, DegPre.cT, hu, Category.id_comp]
    have e4 : DegPre.cT D (𝟙_ _) mu = D.c mu := by rw [DegPre.cT, hu, Category.id_comp]
    have e5 : DegPre.zeroT D (𝟙_ (Over (Sp V))) = η[D.P.A] := by rw [DegPre.zeroT, hu, Category.id_comp]
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, DegPre.famφB, DegPre.gtφT, DegPre.famε, DegPre.gtε,
      DegPre.lineε, e1, e2, e3, e4, e5]
    have e6 : padd D.P.A (D.c mu) g.b = D.c mu * g.b := by rw [padd, ← Hom.mul_def]
    rw [e6]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

/- English proof (translation)
Introduce `V _ _ _ D θ g g' w l hP hI mu gam hgam`. Take `⟨t, ht, htv⟩` from `hI`. Establish `hL` using `D.P.isLB`. Establish `hp` using `mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hgam (g.isGen mu)) ht`. Take `⟨a, ha⟩` from `GlobalTheory.ExpansionValueZero.exists_coeff (A := V) hL θ (D.c mu * g.b).left _ (invGen_isGen _ _ _ _ hp) (formEq_prod D g mu)`.

Use `⟨a, fun z J hJ => ?_, fun ⟨J, hJ, hU⟩ => ?_⟩` and prove the remaining obligations. Establish `hg' : g'.b = toUnit (TF (R` using `V) (FractionRing V)) ≫ g.b := Over.OverMorphism.ext hP.1`. Establish `hb : (padd D.P.A (DegPre.cT D _ mu) g'.b).left = (toUnit (TF (R` using `V) (FractionRing V))).left ≫ (D.c mu * g.b).left := by`. Rewrite using `[← Over.comp_left, hg', Hom.mul_def, padd, ← Category.assoc, comp_lift]`. Establish `hs : Geo.Tor.val (g'.s mu) (𝟙 _) z J = Geo.Tor.val (g.s mu) (toUnit (TF (R` using `V) (FractionRing V))).left z J := (val_corr hJ (hP.2 mu) (𝟙 _)).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))`.

Establish `e₁` using `ha _ (toUnit (TF (R := V) (FractionRing V))).left z J hJ`. Rewrite using `[hb, e₁, hs, cst_toUnit, val_inv, val_mul hJ, val_mul hJ]`. Establish `h₁` using `htv z J hJ`. Generalize the expression as in `GlobalTheory.UT.cst (FractionRing V) z l = c₁ at h₁ ⊢`. Generalize the expression as in `GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) = c₂`.

Generalize the expression as in `Geo.Tor.val w (𝟙 _) z J = u₁ at h₁ ⊢`. Generalize the expression as in `Geo.Tor.val t (toUnit (TF (R := V) (FractionRing V))).left z J = u₂ at h₁ ⊢`. Generalize the expression as in `Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J = u₃`. Generalize the expression as in `Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J = u₄`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h₁, mul_comm u₂.val, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, _root_.mul_one]`. Establish `e₁` using `ha (Sp V) (𝟙 _) (closedPoint V) J hJ`. Rewrite `e₁` using `[Category.id_comp]`. Rewrite `hU` using `[e₁]`. Conclude with `isUnit_of_mul_isUnit_left hU`.
-/
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1))), gam.IsGen → ∃ a : V, (∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z l * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a)) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a)) := by
  intro V _ _ _ D θ g g' w l hP hI mu gam hgam
  obtain ⟨t, ht, htv⟩ := hI
  have hL := D.P.isLB
  have hp := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hgam (g.isGen mu)) ht
  obtain ⟨a, ha⟩ := GlobalTheory.ExpansionValueZero.exists_coeff (A := V) hL θ (D.c mu * g.b).left _ (invGen_isGen _ _ _ _ hp)
    (formEq_prod D g mu)
  refine ⟨a, fun z J hJ => ?_, fun ⟨J, hJ, hU⟩ => ?_⟩
  · have hg' : g'.b = toUnit (TF (R := V) (FractionRing V)) ≫ g.b := Over.OverMorphism.ext hP.1
    have hb : (padd D.P.A (DegPre.cT D _ mu) g'.b).left =
        (toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu * g.b).left := by
      rw [← Over.comp_left, hg', Hom.mul_def, padd, ← Category.assoc, comp_lift]
    have hs : Geo.Tor.val (g'.s mu) (𝟙 _) z J = Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J :=
      (val_corr hJ (hP.2 mu) (𝟙 _)).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have e₁ := ha _ (toUnit (TF (R := V) (FractionRing V))).left z J hJ
    rw [hb, e₁, hs, cst_toUnit, val_inv, val_mul hJ, val_mul hJ]
    have h₁ := htv z J hJ
    generalize GlobalTheory.UT.cst (FractionRing V) z l = c₁ at h₁ ⊢
    generalize GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) = c₂
    generalize Geo.Tor.val w (𝟙 _) z J = u₁ at h₁ ⊢
    generalize Geo.Tor.val t (toUnit (TF (R := V) (FractionRing V))).left z J = u₂ at h₁ ⊢
    generalize Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J = u₃
    generalize Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J = u₄
    calc c₁ * u₃.val * (c₂ * ((u₃ * u₄ * u₂)⁻¹).val) * u₄.val * u₁.val
        = c₂ * ((c₁ * u₁.val) * (u₃.val * u₄.val) * ((u₃ * u₄ * u₂)⁻¹).val) := by ring
      _ = c₂ := by
        rw [h₁, mul_comm u₂.val, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          _root_.mul_one]
  · have e₁ := ha (Sp V) (𝟙 _) (closedPoint V) J hJ
    rw [Category.id_comp] at e₁
    rw [e₁] at hU
    exact isUnit_of_mul_isUnit_left hU

end GlobalTheory.Poinc.IntTerm.IntPoint
