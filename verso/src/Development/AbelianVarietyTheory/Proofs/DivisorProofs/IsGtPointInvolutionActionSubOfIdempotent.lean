import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TorusExt

noncomputable section

namespace GlobalTheory.Mum.IdemDiff

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))`.
-/
theorem val_act (oa : D.OAct O) (a : O)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (g : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))

/- English proof (translation)
Introduce `R _ _ D F _ _ O _ _ _ oa a ha g₀ g h t hg hh hadd`. Establish `hG : GlobalFnsSt` using `GlobalTheory.globalFns_holds`. Use `oa.onB.hom a` as an intermediate fact. Use `oa.onB.hom (star a)` as an intermediate fact. Establish `hs : star a * star a = star a` using `by rw [← star_mul, ha]`.

Establish `cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x` using `fun T x χ => by`. Rewrite using `[cP, oa.c_lin, ← Category.assoc]`. Both sides reduce to the same expression. Establish `aa : oa.onB.act a = oa.onB.act a ≫ oa.onB.act a` using `by rw [← oa.onB.map_mul, ha]`. Establish `ss : oa.onB.act (star a) = oa.onB.act (star a) ≫ oa.onB.act (star a)` using `by rw [← oa.onB.map_mul, hs]`.

Take `⟨b₁, v₁⟩` from `(isAdd_iff_val _ _ _).1 hadd`. Establish `gb : g.b = g.b ≫ oa.onB.act a` using `by rw [hg.1, Category.assoc, ← aa]`. Establish `tb : t.b = t.b ≫ oa.onB.act a`. Establish `e` using `gb`. Rewrite `e` using `[b₁, MonObj.mul_comp, ← hh.1]`.

Conclude with `mul_right_cancel e`. Use `⟨tb, fun u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => (val_act oa a u t χ hJ).trans ?_⟩` and prove the remaining obligations. Establish `vg : ∀ χ, charVal g χ y J = charVal g₀ (star a • χ) y J * val₂ u y J (cP D _ χ) g₀.b` using `fun χ => (val_corr hJ (hg.2 u hu u₀ χ) _).symm.trans (val_act oa a u g₀ χ hJ)`. Establish `vh : charVal h χ y J = charVal h (star a • χ) y J * val₂ u y J (cP D _ χ) h.b` using `(val_corr hJ (hh.2 u hu u₀ χ) _).symm.trans (val_act oa a u h χ hJ)`. Establish `vc` using `IsRos.val_comp hG D.P.isAb D.P.isLB ss aa ⟨hu, u₀⟩ ⟨hu, u₀⟩ ⟨hu, u₀⟩ hJ (cP D _ χ) g₀.b`.

Establish `vg' : charVal g χ y J = charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b`. Rewrite using `[vg χ, vg (star a • χ), ← mul_smul, hs, vc, cf, hg.1, _root_.mul_assoc]`. Establish `ra` using `(ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ t.b h.b (cP D _ χ)).2`. Rewrite `ra` using `[← tb, ← hh.1, ← b₁]`. Establish `e₂` using `v₁ (star a • χ) y J hJ`.

Rewrite `e₂` using `[cf]`. Establish `a₁` using `congrArg Additive.ofMul ra`. Establish `a₂` using `congrArg Additive.ofMul e₂`. Establish `a₃` using `congrArg Additive.ofMul (v₁ χ y J hJ)`. Establish `a₄` using `congrArg Additive.ofMul vg'`.

Establish `a₅` using `congrArg Additive.ofMul vh`. Use `show _ = charVal t χ y J`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, th] at a₁ a₂ a₃ a₄ a₅ ⊢`. Take the linear combination `(norm := abel) a₃ - a₄ + a₅ - a₁ - a₂`.
-/
theorem gtPtAct_of_isAdd : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O), a * a = a → ∀ g₀ g h t : GtPtF D F, GtPtAct oa a g₀ g → GtPtAct oa a h h → GtPtF.IsAdd t h g → GtPtAct oa a t t := by
  intro R _ _ D F _ _ O _ _ _ oa a ha g₀ g h t hg hh hadd
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hs : star a * star a = star a := by rw [← star_mul, ha]
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have aa : oa.onB.act a = oa.onB.act a ≫ oa.onB.act a := by rw [← oa.onB.map_mul, ha]
  have ss : oa.onB.act (star a) = oa.onB.act (star a) ≫ oa.onB.act (star a) := by rw [← oa.onB.map_mul, hs]
  obtain ⟨b₁, v₁⟩ := (isAdd_iff_val _ _ _).1 hadd
  have gb : g.b = g.b ≫ oa.onB.act a := by rw [hg.1, Category.assoc, ← aa]
  have tb : t.b = t.b ≫ oa.onB.act a := by
    have e := gb
    rw [b₁, MonObj.mul_comp, ← hh.1] at e
    exact mul_right_cancel e
  refine ⟨tb, fun u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => (val_act oa a u t χ hJ).trans ?_⟩
  have vg : ∀ χ, charVal g χ y J = charVal g₀ (star a • χ) y J * val₂ u y J (cP D _ χ) g₀.b := fun χ =>
    (val_corr hJ (hg.2 u hu u₀ χ) _).symm.trans (val_act oa a u g₀ χ hJ)
  have vh : charVal h χ y J = charVal h (star a • χ) y J * val₂ u y J (cP D _ χ) h.b :=
    (val_corr hJ (hh.2 u hu u₀ χ) _).symm.trans (val_act oa a u h χ hJ)
  have vc := IsRos.val_comp hG D.P.isAb D.P.isLB ss aa ⟨hu, u₀⟩ ⟨hu, u₀⟩ ⟨hu, u₀⟩ hJ (cP D _ χ) g₀.b
  have vg' : charVal g χ y J = charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := by
    rw [vg χ, vg (star a • χ), ← mul_smul, hs, vc, cf, hg.1, _root_.mul_assoc]
  have ra := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ t.b h.b (cP D _ χ)).2
  rw [← tb, ← hh.1, ← b₁] at ra
  have e₂ := v₁ (star a • χ) y J hJ
  rw [cf] at e₂
  have a₁ := congrArg Additive.ofMul ra
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul (v₁ χ y J hJ)
  have a₄ := congrArg Additive.ofMul vg'
  have a₅ := congrArg Additive.ofMul vh
  show _ = charVal t χ y J
  apply Additive.ofMul.injective
  simp only [ofMul_mul, th] at a₁ a₂ a₃ a₄ a₅ ⊢
  linear_combination (norm := abel) a₃ - a₄ + a₅ - a₁ - a₂

end GlobalTheory.Mum.IdemDiff
