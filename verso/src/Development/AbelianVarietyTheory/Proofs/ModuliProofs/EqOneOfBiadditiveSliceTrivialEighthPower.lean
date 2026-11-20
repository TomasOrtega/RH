import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FormBundleKer

open GlobalTheory.CechPic in

/- English proof (translation)
Introduce `W S G A _ _ _ _ pr L P hpr huniv hL hP hsym hbi hLP hK T x hx`. Set `p : ∀ {T' : Over S}, (T' ⟶ A) → (T' ⟶ A) → Pic T'.left` to `fun a b => pull (lift a b).left (cls P hP)`. Establish `padd : ∀ {T' : Over S} (a a' b : T' ⟶ A), p (a * a') b = p a b + p a' b` using `fun {T'} a a' b => by`. Establish `e` using `(cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi T' a a' b).1`. Rewrite `e` using `[cls_linComb hP, Fin.sum_univ_three]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e`. Rewrite using `[← sub_eq_zero, ← e]`. Simplify using `only [p]`. Normalize the expressions using the abelian group laws. Establish `psym : ∀ {T' : Over S} (a b : T' ⟶ A), p a b = p b a` using `fun {T'} a b => by`.

Establish `e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP)` using `(cls_eq_iff hP (pull_isLB hP _)).2 hsym`. Establish `k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left`. Rewrite using `[← Over.comp_left, comp_lift, lift_fst, lift_snd]`. Use `show pull (lift a b).left (cls P hP) = pull (lift b a).left (cls P hP)`. Rewrite using `[← k, pull_comp, ← e]`.

Establish `pone : ∀ {T' : Over S} (b : T' ⟶ A), p 1 b = 0` using `fun b => by`. Use `padd 1 1 b` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `left_eq_add.1 this`. Establish `px : ∀ {T' : Over S} (τ : T' ⟶ T) (y : T' ⟶ A), p (τ ≫ x) y = 0` using `fun τ y => by`.

Establish `e` using `(cls_eq_zero_iff (pull_isLB hP _)).2 hx`. Rewrite `e` using `[cls_pull hP]`. Establish `k : (lift y τ).left ≫ (lift (snd A T ≫ x) (fst A T)).left = (lift (τ ≫ x) y).left`. Rewrite using `[← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]`. Use `show pull (lift (τ ≫ x) y).left (cls P hP) = 0`.

Rewrite using `[← k, pull_comp, e, map_zero]`. Establish `hl : ∀ {T' : Over S} (z : T' ⟶ G), pull z.left (cls L hL) = ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • p (z ≫ pr uv.1) (z ≫ pr uv.2)` using `fun z => by`. Establish `e` using `(cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP`. Rewrite `e` using `[cls_linComb hP]`. Rewrite using `[e, map_sum]`.

Use `Finset.sum_congr rfl fun uv _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift]`. Take `⟨x', hx', -⟩` from `huniv T fun v => if v = 0 then x else 1`. Establish `pz : ∀ u (y : T ⊗ G ⟶ A), p ((fst T G ≫ x') ≫ pr u) y = 0` using `fun u y => by`. Rewrite using `[Category.assoc, hx']`.

Use `split_ifs`. Conclude with `px _ _`. Rewrite using `[MonObj.comp_one]`. Conclude with `pone _`. Establish `key : pull (Out.translPt G x').left (cls L hL) = pull (snd T G).left (cls L hL)`.

Establish `e : Out.translPt G x' = (fst T G ≫ x') * snd T G` using `rfl`. Rewrite using `[hl, hl, e]`. Use `Finset.sum_congr rfl fun uv _ => ?_` and prove the remaining obligations. Use `hpr uv.1` as an intermediate fact. Use `hpr uv.2` as an intermediate fact.

Rewrite using `[MonObj.mul_comp, MonObj.mul_comp, padd, pz, zero_add, psym, padd, pz, zero_add, psym]`. Establish `H : KerPow.HasGen L (K` using `Fin 2) ![(Out.translPt G x').left, (snd T G).left] ![1, -1] := by`. Use `(cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_linComb hL, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, key, one_smul, neg_smul, add_neg_cancel]`.

Establish `h1 : x' = 1` using `KerPow.eq_one_of_locGen hK x' fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩`. Establish `h0` using `hx' 0`. Use `hpr 0` as an intermediate fact. Rewrite `h0` using `[h1, MonObj.one_comp, if_pos rfl]`. Conclude with `h0.symm`.
-/
theorem eq_one_of_slice_trivial : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro W S G A _ _ _ _ pr L P hpr huniv hL hP hsym hbi hLP hK T x hx
  let p : ∀ {T' : Over S}, (T' ⟶ A) → (T' ⟶ A) → Pic T'.left := fun a b => pull (lift a b).left (cls P hP)
  have padd : ∀ {T' : Over S} (a a' b : T' ⟶ A), p (a * a') b = p a b + p a' b := fun {T'} a a' b => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi T' a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [p]
    abel
  have psym : ∀ {T' : Over S} (a b : T' ⟶ A), p a b = p b a := fun {T'} a b => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsym
    have k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    show pull (lift a b).left (cls P hP) = pull (lift b a).left (cls P hP)
    rw [← k, pull_comp, ← e]
  have pone : ∀ {T' : Over S} (b : T' ⟶ A), p 1 b = 0 := fun b => by
    have := padd 1 1 b
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have px : ∀ {T' : Over S} (τ : T' ⟶ T) (y : T' ⟶ A), p (τ ≫ x) y = 0 := fun τ y => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 hx
    rw [cls_pull hP] at e
    have k : (lift y τ).left ≫ (lift (snd A T ≫ x) (fst A T)).left = (lift (τ ≫ x) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    show pull (lift (τ ≫ x) y).left (cls P hP) = 0
    rw [← k, pull_comp, e, map_zero]
  have hl : ∀ {T' : Over S} (z : T' ⟶ G), pull z.left (cls L hL) =
      ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • p (z ≫ pr uv.1) (z ≫ pr uv.2) := fun z => by
    have e := (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP
    rw [cls_linComb hP] at e
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift]
  obtain ⟨x', hx', -⟩ := huniv T fun v => if v = 0 then x else 1
  have pz : ∀ u (y : T ⊗ G ⟶ A), p ((fst T G ≫ x') ≫ pr u) y = 0 := fun u y => by
    rw [Category.assoc, hx']
    split_ifs
    · exact px _ _
    · rw [MonObj.comp_one]; exact pone _
  have key : pull (Out.translPt G x').left (cls L hL) = pull (snd T G).left (cls L hL) := by
    have e : Out.translPt G x' = (fst T G ≫ x') * snd T G := rfl
    rw [hl, hl, e]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have := hpr uv.1
    have := hpr uv.2
    rw [MonObj.mul_comp, MonObj.mul_comp, padd, pz, zero_add, psym, padd, pz, zero_add, psym]
  have H : KerPow.HasGen L (K := Fin 2) ![(Out.translPt G x').left, (snd T G).left] ![1, -1] := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, key, one_smul, neg_smul, add_neg_cancel]
  have h1 : x' = 1 := KerPow.eq_one_of_locGen hK x' fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have h0 := hx' 0
  have := hpr 0
  rw [h1, MonObj.one_comp, if_pos rfl] at h0
  exact h0.symm

end GlobalTheory.FormBundleKer
