import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.DiagPow

/- English proof (translation)
Unfold `eSec`. Rewrite using `[← Over.comp_left, ← Over.comp_left]`. Use `congr 1`. Rewrite using `[comp_lift, comp_lift]`. Use `congr 1`.

Rewrite using `[Hom.one_def, ← Category.assoc, Category.comp_id, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]`.
-/
theorem eSec_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  unfold eSec
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift]
  congr 1
  rw [Hom.one_def, ← Category.assoc, Category.comp_id, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]

/- English proof (translation)
Introduce `S A _ _ Q hQ d hd`. Take `⟨hA, hQL, ⟨t₁, ht₁⟩, -, -, hamp⟩` from `hQ`. Establish `hM : (Q.pull (lift (𝟙 A) (𝟙 A)).left).IsLB` using `pull_isLB hQL _`. Establish `hD : (diagPow A Q d).IsLB` using `LB.isLB_linComb hQL _ _`. Establish `hcls : CechPic.cls _ hD = d • CechPic.cls _ hM`.

Use `(CechPic.cls_linComb hQL (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ)) hD).trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_unique, CechPic.cls_pull hQL _ hM]`. Conclude with `natCast_zsmul _ _`. Use `⟨hD, ?_, GlobalTheory.SiegelOfTheta.relAmple_of_pow hA hM hD hd hcls hamp⟩` and prove the remaining obligations. Establish `h₁ : CechPic.cls _ (pull_isLB hQL (lift (1 : A ⟶ A) (𝟙 A)).left) = 0` using `(CechPic.cls_eq_zero_iff _).2 ⟨t₁, ht₁⟩`.

Use `(CechPic.cls_eq_zero_iff (pull_isLB hD (eSec A))).1 ?_` and prove the remaining obligations. Rewrite using `[CechPic.cls_pull hD, hcls, map_nsmul, CechPic.cls_pull hQL, ← CechPic.pull_comp, eSec_diag, CechPic.pull_comp, ← CechPic.cls_pull hQL _ (pull_isLB hQL _), h₁, map_zero, nsmul_zero]`.
-/
theorem diagPow_isLB_rigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d →
      (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  intro S A _ _ Q hQ d hd
  obtain ⟨hA, hQL, ⟨t₁, ht₁⟩, -, -, hamp⟩ := hQ
  have hM : (Q.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hQL _
  have hD : (diagPow A Q d).IsLB := LB.isLB_linComb hQL _ _
  have hcls : CechPic.cls _ hD = d • CechPic.cls _ hM := by
    refine (CechPic.cls_linComb hQL (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ)) hD).trans ?_
    rw [Fintype.sum_unique, CechPic.cls_pull hQL _ hM]
    exact natCast_zsmul _ _
  refine ⟨hD, ?_, GlobalTheory.SiegelOfTheta.relAmple_of_pow hA hM hD hd hcls hamp⟩
  have h₁ : CechPic.cls _ (pull_isLB hQL (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 :=
    (CechPic.cls_eq_zero_iff _).2 ⟨t₁, ht₁⟩
  refine (CechPic.cls_eq_zero_iff (pull_isLB hD (eSec A))).1 ?_
  rw [CechPic.cls_pull hD, hcls, map_nsmul, CechPic.cls_pull hQL, ← CechPic.pull_comp, eSec_diag,
    CechPic.pull_comp, ← CechPic.cls_pull hQL _ (pull_isLB hQL _), h₁, map_zero, nsmul_zero]

end GlobalTheory.ActFin.DiagPow
