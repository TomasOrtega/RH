import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPullbackThetaValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Ext

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre GlobalTheory.RayEv Formalism.L2.Pj

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (Y : Ext D)

/- English proof (translation)
Establish `h` using `((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1`. Rewrite `h` using `[Category.comp_id]`. Then use the resulting hypothesis.
-/
theorem Φ_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

/- English proof (translation)
The claim follows from `isMonHom_of_mul _ fun T x x' => by rw [← Φ_b, ← Φ_b, ← Φ_b]; exact ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x x')).1`.
-/
theorem isMonHom_q : IsMonHom Y.q :=
  isMonHom_of_mul _ fun T x x' => by
    rw [← Φ_b, ← Φ_b, ← Φ_b]; exact ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x x')).1

/- English proof (translation)
Set `F` to `fstG (⊥ : Ideal R) 0 Y.H`. Set `j` to `inv F.left`. Establish `hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0` using `Over.w F`. Set `ξ` to `Y.Φ Y.H (𝟙 _)`. Take `⟨x, hx⟩` from `GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ`.

Take `⟨ξ', hξ'⟩` from `GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by`. Rewrite using `[← hF]`. Conclude with `IsIso.inv_hom_id_assoc _ _)`. Set `b : Y.H ⟶ Y.H` to `(Y.Φ Y.H).symm ξ'`. Establish `hb : Y.Φ Y.H b = ξ'` using `Equiv.apply_symm_apply _ _`.

Set `a` to `x ≫ F.left`. Establish `ha : a ≫ Y.H.hom = Y.H.hom`. Rewrite using `[Category.assoc, hF]`. Conclude with `GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx`. Set `a' : Y.H ⟶ Y.H` to `Over.homMk a ha`.

Establish `haj : a ≫ j = x` using `by simp [a, j]`. Establish `e1 : b.left ≫ x = j`. Establish `h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _))` using `Y.rep.1 Y.H Y.H b (𝟙 _)`. Rewrite `h1` using `[Category.comp_id, hb]`. Conclude with `(GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'`.

Establish `e1' : b.left ≫ a = 𝟙 _`. Rewrite using `[← Category.assoc, e1]`. Simplify using `[j]`. Establish `e2 : a' ≫ b = 𝟙 _`. Establish `h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b))` using `Y.rep.1 Y.H Y.H a' b`.

Rewrite `h2` using `[hb]`. Establish `h3` using `GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2`. Rewrite `h3` using `[haj]`. Conclude with `(Y.Φ Y.H).injective (h3.unique_right c hx)`. Establish `e2' : a ≫ b.left = 𝟙 _` using `congrArg (·.left) e2`.

Establish `: IsIso a` using `⟨⟨b.left, e2', e1'⟩⟩`. Use `⟨a ≫ j, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[haj, ← GlobalTheory.TorusCoord.pG_left]`. Conclude with `hx.1`.
-/
theorem exists_q_eq (c : GtCoord (⊥ : Ideal R) D 0 Y.H) : ∃ a : Y.H.left ⟶ (thickObj R ⊥ 0 Y.H).left, IsIso a ∧
    Y.q.left = a ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  refine ⟨a ≫ j, inferInstance, ?_⟩
  rw [haj, ← GlobalTheory.TorusCoord.pG_left]
  exact hx.1

/- English proof (translation)
Take `⟨c⟩` from `GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0`. Use `smooth_gtCoord_q c` as an intermediate fact. Use `c.q_surj` as an intermediate fact. Use `c.q_affine` as an intermediate fact. Take `⟨a, _, h⟩` from `Y.exists_q_eq c`.

Rewrite using `[h]`. Conclude with `⟨inferInstance, inferInstance, inferInstance⟩`.
-/
theorem q_props : Smooth Y.q.left ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := smooth_gtCoord_q c
  have := c.q_surj
  have := c.q_affine
  obtain ⟨a, _, h⟩ := Y.exists_q_eq c
  rw [h]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/- English proof (translation)
Establish `e1 : Y.q ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = padd D.P.A (DegPre.cT D Y.H α) Y.q`. Simplify using `only [padd, comp_lift_assoc, Category.comp_id]`. Rewrite using `[← Hom.mul_def, ← Hom.mul_def, mul_comm, comp_toUnit_assoc]`. Establish `e2 : Y.q.left ≫ (toUnit D.P.A ≫ D.c α).left = (DegPre.cT D Y.H α).left`. Rewrite using `[← Over.comp_left, comp_toUnit_assoc]`.

Establish `e3 : Y.q.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (DegPre.zeroT D Y.H).left`. Rewrite using `[← Over.comp_left, comp_toUnit_assoc]`. Establish `e0 : Y.q.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (padd D.P.A (DegPre.cT D Y.H α) Y.q).left`. Rewrite using `[← Over.comp_left, e1]`. Introduce `U _ h`.

Rewrite using `[Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Simplify using `only [DegPre.famφB, DegPre.famε, DegPre.gtφT, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e0, e2, e3]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_zpow]`.

Use `module`.
-/
theorem formEq_term (k : ℕ) (α : D.X) :
    FormEq (Sum.elim (fun i => Y.q.left ≫ DegPre.famφB D α i) (DegPre.gtφT D Y.H Y.q α))
      (Sum.elim (DegPre.famε k) DegPre.gtε) (K' := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) := by
  have e1 : Y.q ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = padd D.P.A (DegPre.cT D Y.H α) Y.q := by
    simp only [padd, comp_lift_assoc, Category.comp_id]
    rw [← Hom.mul_def, ← Hom.mul_def, mul_comm, comp_toUnit_assoc]
  have e2 : Y.q.left ≫ (toUnit D.P.A ≫ D.c α).left = (DegPre.cT D Y.H α).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e3 : Y.q.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (DegPre.zeroT D Y.H).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e0 : Y.q.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (DegPre.cT D Y.H α) Y.q).left := by
    rw [← Over.comp_left, e1]
  intro U _ h
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp only [DegPre.famφB, DegPre.famε, DegPre.gtφT, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e0, e2, e3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

/- English proof (translation)
Take `⟨τ, hτ⟩` from `exists_sec D.P.isLB (Y.formEq_term k α) (pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α))`. Use `⟨τ, fun T x y J hJ => ?_⟩` and prove the remaining obligations. Use `(hτ _ _ y J hJ).trans ((sval_pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α) x.left y hJ).trans ?_)` and prove the remaining obligations. Take `⟨-, h₂⟩` from `(isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))`. Establish `e` using `h₂ α y J hJ`.

Rewrite `e` using `[Category.comp_id]`. Rewrite using `[Over.comp_left]`. Conclude with `congrArg _ (congrArg Units.val e.symm)`.
-/
theorem exists_isTermOf (k : ℕ) (α : D.X) (σ : D.SecB k α) : ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y σ τ := by
  obtain ⟨τ, hτ⟩ := exists_sec D.P.isLB (Y.formEq_term k α)
    (pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α))
  refine ⟨τ, fun T x y J hJ => ?_⟩
  refine (hτ _ _ y J hJ).trans ((sval_pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α)
    x.left y hJ).trans ?_)
  obtain ⟨-, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
  have e := h₂ α y J hJ
  rw [Category.comp_id] at e
  rw [Over.comp_left]
  exact congrArg _ (congrArg Units.val e.symm)

end GlobalTheory.Mum.Ext

namespace GlobalTheory.Mum

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `Y.q_props`. Use `⟨?_, h2, h3, Y.isMonHom_q, Y.exists_isTermOf⟩` and prove the remaining obligations. Establish `: Smooth D.P.A.hom` using `D.P.isAb.smooth`. Rewrite using `[← Over.w Y.q]`. Use `infer_instance`.
-/
theorem ext_smooth_affine_surj_terms (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) :
    Smooth Y.H.hom ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left ∧ IsMonHom Y.q ∧
      ∀ (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y b τ := by
  obtain ⟨h1, h2, h3⟩ := Y.q_props
  refine ⟨?_, h2, h3, Y.isMonHom_q, Y.exists_isTermOf⟩
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  rw [← Over.w Y.q]
  infer_instance

end GlobalTheory.Mum
