import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.MultiplicationEtaleTorsion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulLawsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationEtaleTorsion

/- English proof (translation)
Use `ext`. Simplify using `only [res, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W) (u : Γ(X, W)ˣ) :
    res h (res h' u) = res (h.trans h') u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Use `ext`. Simplify using `only [res, pullU, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]`. Both sides reduce to the same expression.
-/
theorem pullU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : U ≤ V) (u : Γ(X, V)ˣ) :
    pullU f U (res h u) = res (fun _ hy => h hy : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ V) (pullU f V u) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]
  rfl

def DualRefines {Y : Scheme.{0}} (M' M : LB Y) : Prop :=
  ∃ (e : M'.ι → M.ι) (hU : ∀ i, M'.U i ≤ M.U (e i)),
    ∀ i j, M'.g i j = (res (inf_le_inf (hU i) (hU j)) (M.g (e i) (e j)))⁻¹

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Take `⟨e, hU, hg⟩` from `h`. Use `⟨fun j k => e (j k), fun j y hy => Set.mem_iInter.2 fun k => hU _ (Set.mem_iInter.1 hy k), fun i j => ?_⟩` and prove the remaining obligations. Simplify using `only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one, hg, map_inv, res_res]`. Use `congr 1`. Use `erw [pullU_res, res_res]`.

Both sides reduce to the same expression.
-/
theorem DualRefines.pull {Y Z : Scheme.{0}} {M' M : LB Y} (h : DualRefines M' M) (f : Z ⟶ Y) :
    DualRefines (M'.pull f) (M.pull f) := by
  obtain ⟨e, hU, hg⟩ := h
  refine ⟨fun j k => e (j k), fun j y hy => Set.mem_iInter.2 fun k =>
    hU _ (Set.mem_iInter.1 hy k), fun i j => ?_⟩
  simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one, hg, map_inv, res_res]
  congr 1
  erw [pullU_res, res_res]
  rfl

variable {S : Scheme.{0}}

/- English proof (translation)
Rewrite using `[mulA, ← comp_mulN, Category.id_comp]`.
-/
theorem mulN_eq_mulA (A : Over S) [GrpObj A] (n : ℕ) : mulN A n = mulA A n := by
  rw [mulA, ← comp_mulN, Category.id_comp]

/- English proof (translation)
Take `⟨-, hc⟩` from `GlobalTheory.FinEt.card_points_eq_finrank (mulN A n).left t z`. Establish `h1 : 1 ≤ (mulN A n).left.finrank (t z)` using `(Scheme.Hom.one_le_finrank_iff_surjective (mulN A n).left).2 inferInstance _`. Rewrite `h1`, the goal using `[← hc]`. Set `t' : Over.mk (t ≫ A.hom) ⟶ A` to `Over.homMk t rfl`. Set `E : {x : Spec (CommRingCat.of k) ⟶ A.left // x ≫ (mulN A n).left = t} ≃ {y : Over.mk (t ≫ A.hom) ⟶ A // y ^ n = t'}` to `{ toFun := fun x => ⟨Over.homMk x.1 (by`.

Use `x.2 =≫ A.hom` as an intermediate fact. Rewrite `this` using `[Category.assoc, Over.w]`. Conclude with `this), by`. Rewrite using `[← comp_mulN]`. Use `ext`.

Conclude with `x.2⟩`. Use `invFun := fun y => ⟨y.1.left, by`. Use `y.2` as an intermediate fact. Rewrite `this` using `[← comp_mulN]`. Conclude with `congrArg (fun f => f.left) this⟩`.

Use `left_inv := fun _ => rfl`. Use `right_inv := fun _ => rfl }`. Take `⟨x₀⟩` from `(Nat.card_pos_iff.1 h1).1`. Take `⟨y₀, hy₀⟩` from `E x₀`. Rewrite using `[Nat.card_congr E]`.

Use `Nat.card_congr ((Equiv.mulRight y₀⁻¹).subtypeEquiv fun y => ?_)` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulRight, mul_pow, inv_pow, hy₀, mul_inv_eq_one]`.
-/
theorem finrank_mulN_eq_card (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    [IsFinite (mulN A n).left] [Etale (mulN A n).left] [Surjective (mulN A n).left]
    {k : Type} [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ A.left)
    (z : Spec (CommRingCat.of k)) :
    (mulN A n).left.finrank (t z) =
      Nat.card {y : Over.mk (t ≫ A.hom) ⟶ A // y ^ n = 1} := by
  obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank (mulN A n).left t z
  have h1 : 1 ≤ (mulN A n).left.finrank (t z) :=
    (Scheme.Hom.one_le_finrank_iff_surjective (mulN A n).left).2 inferInstance _
  rw [← hc] at h1 ⊢
  let t' : Over.mk (t ≫ A.hom) ⟶ A := Over.homMk t rfl
  let E : {x : Spec (CommRingCat.of k) ⟶ A.left // x ≫ (mulN A n).left = t} ≃
      {y : Over.mk (t ≫ A.hom) ⟶ A // y ^ n = t'} :=
    { toFun := fun x => ⟨Over.homMk x.1 (by
          have := x.2 =≫ A.hom
          rw [Category.assoc, Over.w] at this
          exact this), by
        rw [← comp_mulN]
        ext
        exact x.2⟩
      invFun := fun y => ⟨y.1.left, by
        have := y.2
        rw [← comp_mulN] at this
        exact congrArg (fun f => f.left) this⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨x₀⟩ := (Nat.card_pos_iff.1 h1).1
  obtain ⟨y₀, hy₀⟩ := E x₀
  rw [Nat.card_congr E]
  refine Nat.card_congr ((Equiv.mulRight y₀⁻¹).subtypeEquiv fun y => ?_)
  rw [Equiv.coe_mulRight, mul_pow, inv_pow, hy₀, mul_inv_eq_one]

end GlobalTheory.MulLawsCompare
