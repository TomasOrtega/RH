import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilPull

section Algebra

variable {A U : Type} [AddCommGroup A] [AddCommGroup U] {q : A → U} {B : A →+ A →+ U}

/- English proof (translation)
Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => simpa using h0`. Consider the case `succ n ih`. Rewrite using `[add_smul, one_smul, hq, ih, map_zsmul, AddMonoidHom.zsmul_apply, h2]`. Use `module`.

Consider the case `pred n ih`. Establish `e` using `hq ((-(n : ℤ) - 1) • x) x`. Rewrite `e` using `[show (-(n : ℤ) - 1) • x + x = (-(n : ℤ)) • x by module, ih, map_zsmul, AddMonoidHom.zsmul_apply, h2]`. Establish `e' : q ((-(n : ℤ) - 1) • x) = (-(n : ℤ) * -(n : ℤ)) • q x - q x - (-(n : ℤ) - 1) • (q x + q x)`. Rewrite using `[e]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e']`. Use `module`.
-/
theorem quad_zsmul (h0 : q 0 = 0) (hq : ∀ x y, q (x + y) = q x + q y + B x y) (h2 : ∀ x, B x x = q x + q x)
    (n : ℤ) (x : A) : q (n • x) = (n * n) • q x := by
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih =>
    rw [add_smul, one_smul, hq, ih, map_zsmul, AddMonoidHom.zsmul_apply, h2]
    module
  | pred n ih =>
    have e := hq ((-(n : ℤ) - 1) • x) x
    rw [show (-(n : ℤ) - 1) • x + x = (-(n : ℤ)) • x by module, ih, map_zsmul, AddMonoidHom.zsmul_apply, h2] at e
    have e' : q ((-(n : ℤ) - 1) • x) = (-(n : ℤ) * -(n : ℤ)) • q x - q x - (-(n : ℤ) - 1) • (q x + q x) := by
      rw [e]; abel
    rw [e']
    module

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [h0]`. Consider the case `insert d s hd ih`. Simplify using `only [Finset.sum_insert hd, hq, Finset.sum_add_distrib, ih, quad_zsmul h0 hq h2, smul_add]`. Establish `e₁ : ∑ r, (al r d * al r d) • q (y d) = m • q (y d)`.

Rewrite using `[← Finset.sum_smul, hal, if_pos rfl]`. Establish `e₂ : ∑ r, B (al r d • y d) (∑ c ∈ s, al r c • y c) = 0`. Simplify using `only [map_sum, map_zsmul, AddMonoidHom.zsmul_apply, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun c hc => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_smul, hal, if_neg (fun e : c = d => hd (e ▸ hc)), zero_smul]`. Rewrite using `[e₁, e₂, add_zero]`.
-/
theorem sum_quad_rows (h0 : q 0 = 0) (hq : ∀ x y, q (x + y) = q x + q y + B x y) (h2 : ∀ x, B x x = q x + q x)
    (al : I → J → ℤ) (m : ℤ) (hal : ∀ c c', ∑ r, al r c * al r c' = if c = c' then m else 0) (y : J → A)
    (s : Finset J) : ∑ r, q (∑ c ∈ s, al r c • y c) = m • ∑ c ∈ s, q (y c) := by
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert d s hd ih =>
    simp only [Finset.sum_insert hd, hq, Finset.sum_add_distrib, ih, quad_zsmul h0 hq h2, smul_add]
    have e₁ : ∑ r, (al r d * al r d) • q (y d) = m • q (y d) := by
      rw [← Finset.sum_smul, hal, if_pos rfl]
    have e₂ : ∑ r, B (al r d • y d) (∑ c ∈ s, al r c • y c) = 0 := by
      simp only [map_sum, map_zsmul, AddMonoidHom.zsmul_apply, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [← Finset.sum_smul, hal, if_neg (fun e : c = d => hd (e ▸ hc)), zero_smul]
    rw [e₁, e₂, add_zero]

/- English proof (translation)
Simplify using `only [hq, hξ, add_zero, Finset.sum_add_distrib, sum_quad_rows h0 hq h2 al m hal y]`. Establish `e : ∑ r, B (∑ c, al r c • y c) (ξ r) = 0`. Simplify using `only [map_sum, map_zsmul, AddMonoidHom.finset_sum_apply, AddMonoidHom.zsmul_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Simplify using `only [← map_zsmul, ← map_sum, hk, map_zero]`. Rewrite using `[e, add_zero]`.
-/
theorem sum_quad_rows_add (h0 : q 0 = 0) (hq : ∀ x y, q (x + y) = q x + q y + B x y)
    (h2 : ∀ x, B x x = q x + q x)
    (al : I → J → ℤ) (m : ℤ) (hal : ∀ c c', ∑ r, al r c * al r c' = if c = c' then m else 0) (y : J → A)
    (ξ : I → A) (hξ : ∀ r, q (ξ r) = 0) (hk : ∀ c, ∑ r, al r c • ξ r = 0) :
    ∑ r, q (∑ c, al r c • y c + ξ r) = m • ∑ c, q (y c) := by
  simp only [hq, hξ, add_zero, Finset.sum_add_distrib, sum_quad_rows h0 hq h2 al m hal y]
  have e : ∑ r, B (∑ c, al r c • y c) (ξ r) = 0 := by
    simp only [map_sum, map_zsmul, AddMonoidHom.finset_sum_apply, AddMonoidHom.zsmul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp only [← map_zsmul, ← map_sum, hk, map_zero]
  rw [e, add_zero]

end Algebra

section Mul

open GlobalTheory.PrimNorm

variable {A U : Type} [CommGroup A] [CommGroup U] {q : A → U} {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]

/- English proof (translation)
Set `B : Additive A →+ Additive A →+ Additive U` to `AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun z => Additive.ofMul (diff₂ q x.toMul z.toMul)) (fun z z' => congrArg Additive.ofMul (diff₂_mul_right hc _ _ _))) (fun x x' => AddMonoidHom.ext fun z => congrArg Additive.ofMul (diff₂_mul_left hc _ _ _))`. Establish `hB : ∀ x z, B x z = Additive.ofMul (diff₂ q x.toMul z.toMul)` using `fun _ _ => rfl`. Establish `key` using `sum_quad_rows_add (q := fun x : Additive A => Additive.ofMul (q x.toMul)) (B := B) (congrArg Additive.ofMul h0) (fun x z => by`. Simplify using `only [hB, diff₂, h0, toMul_add, ofMul_mul, ofMul_inv, ofMul_one]`. Use the proof step `abel) (fun x => by`.

Simplify using `only [hB, diff₂, h0, ← sq, h2, ofMul_mul, ofMul_inv, ofMul_one, ofMul_pow]`. Use the proof step `abel) al m hal (fun c => Additive.ofMul (y c)) (fun r => Additive.ofMul (ξ r))`. Use the proof step `(fun r => congrArg Additive.ofMul (hξ r)) (fun c => by`. Simplify `congrArg Additive.ofMul (hk c))` using `only [ofMul_prod, ofMul_zpow, ofMul_one]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify `key` using `only [ofMul_prod, ofMul_zpow, toMul_add, toMul_sum, toMul_zsmul, toMul_ofMul]`.
-/
theorem prod_quad_rows_mul (hc : ∀ x y z, diff₃ q x y z = 1) (h0 : q 1 = 1) (h2 : ∀ x, q (x ^ 2) = q x ^ 4)
    (al : I → J → ℤ) (m : ℤ) (hal : ∀ c c', ∑ r, al r c * al r c' = if c = c' then m else 0) (y : J → A)
    (ξ : I → A) (hξ : ∀ r, q (ξ r) = 1) (hk : ∀ c, ∏ r, ξ r ^ al r c = 1) :
    ∏ r, q ((∏ c, y c ^ al r c) * ξ r) = (∏ c, q (y c)) ^ m := by
  let B : Additive A →+ Additive A →+ Additive U := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun z => Additive.ofMul (diff₂ q x.toMul z.toMul))
      (fun z z' => congrArg Additive.ofMul (diff₂_mul_right hc _ _ _)))
    (fun x x' => AddMonoidHom.ext fun z => congrArg Additive.ofMul (diff₂_mul_left hc _ _ _))
  have hB : ∀ x z, B x z = Additive.ofMul (diff₂ q x.toMul z.toMul) := fun _ _ => rfl
  have key := sum_quad_rows_add (q := fun x : Additive A => Additive.ofMul (q x.toMul)) (B := B)
    (congrArg Additive.ofMul h0) (fun x z => by
      simp only [hB, diff₂, h0, toMul_add, ofMul_mul, ofMul_inv, ofMul_one]
      abel) (fun x => by
      simp only [hB, diff₂, h0, ← sq, h2, ofMul_mul, ofMul_inv, ofMul_one, ofMul_pow]
      abel) al m hal (fun c => Additive.ofMul (y c)) (fun r => Additive.ofMul (ξ r))
    (fun r => congrArg Additive.ofMul (hξ r)) (fun c => by
      simpa only [ofMul_prod, ofMul_zpow, ofMul_one] using congrArg Additive.ofMul (hk c))
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow, toMul_add, toMul_sum, toMul_zsmul, toMul_ofMul] using key

end Mul

open GlobalTheory.PrimNorm GlobalTheory.MulPull

/- English proof (translation)
Introduce `laws R _ _ _ x m al ξ hal hk`. Establish `hL` using `x.P.isLB`. Set `T` to `Out.powObj x.P.A 4`. Take `⟨⟨cub⟩, -⟩` from `laws.cube _ x.P ⟨x.P.L, x.rig, hL, x.rig_gen⟩ rfl`. Establish `hconst : ∀ z : Pt x, ptCls x.P.L T (toUnit T ≫ z) = 1` using `fun z => by`.

Establish `h : HasGen x.P.L (K` using `PUnit) (fun _ => z.left) (fun _ => 1) := DVR.exists_gen_of_local (V := R) x.P.L hL (K := PUnit) (fun _ => z.left) (fun _ => 1)`. Establish `e` using `(hasGen_iff hL _ _).1 (h.pull (toUnit T).left)`. Rewrite `e` using `[Fintype.prod_unique, zpow_one]`. Conclude with `e`. Establish `h2 : ∀ y : T ⟶ x.P.A, ptCls x.P.L T (y ^ 2) = ptCls x.P.L T y ^ 4` using `fun y => by`.

Establish `h : HasGen x.P.L (K` using `Fin 2) ![𝟙 x.P.A.left, (Out.mulA x.P.A 2).left] ![((2 : ℕ) : ℤ) ^ 2, -1] := laws.mulPull _ x.P 2`. Establish `e` using `(hasGen_iff hL _ _).1 (h.pull y.left)`. Establish `e₂ : y ≫ Out.mulA x.P.A 2 = y ^ 2` using `by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]`. Simplify using `only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, ← Over.comp_left, e₂, zpow_neg, zpow_one, mul_inv_eq_one] at e`. Use `e.symm.trans ?_` and prove the remaining obligations.

Evaluate the numerical expressions. Establish `key` using `prod_quad_rows_mul (q := ptCls x.P.L T) (diff₃_ptCls hL ⟨cub.t, cub.isGen⟩) (by simpa only [MonObj.comp_one] using hconst 1) h2 (fun r c => al r c) (m : ℤ) (fun c c' => by`. Use `congrFun (congrFun hal c) c'` as an intermediate fact. Simplify `this)` using `[Matrix.mul_apply, Matrix.one_apply]`. Use the proof step `(fun c => Out.powPr x.P.A c) (fun r => toUnit T ≫ ξ r) (fun r => hconst _) (fun c => by`.

Establish `e` using `congrArg (fun z : Pt x => toUnit T ≫ z) (hk c)`. Simplify using `only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow, MonObj.comp_one] at e`. Simplify `e)` using `only [Fin.prod_univ_succ, Fin.prod_univ_zero]`. Use `(hasGen_iff hL _ _).2 ?_` and prove the remaining obligations. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one, zpow_neg, Finset.prod_inv_distrib, mul_inv_eq_one, Finset.prod_zpow]`.

Use `Eq.trans (Finset.prod_congr rfl fun r _ => ?_) key` and prove the remaining obligations. Rewrite using `[alMap, List.prod_ofFn]`.
-/
theorem exists_gen_similitude_pull : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x), al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → ∃ w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w.IsGen := by
  intro laws R _ _ _ x m al ξ hal hk
  have hL := x.P.isLB
  let T := Out.powObj x.P.A 4
  obtain ⟨⟨cub⟩, -⟩ := laws.cube _ x.P ⟨x.P.L, x.rig, hL, x.rig_gen⟩ rfl
  have hconst : ∀ z : Pt x, ptCls x.P.L T (toUnit T ≫ z) = 1 := fun z => by
    have h : HasGen x.P.L (K := PUnit) (fun _ => z.left) (fun _ => 1) :=
      DVR.exists_gen_of_local (V := R) x.P.L hL (K := PUnit) (fun _ => z.left) (fun _ => 1)
    have e := (hasGen_iff hL _ _).1 (h.pull (toUnit T).left)
    rw [Fintype.prod_unique, zpow_one] at e
    exact e
  have h2 : ∀ y : T ⟶ x.P.A, ptCls x.P.L T (y ^ 2) = ptCls x.P.L T y ^ 4 := fun y => by
    have h : HasGen x.P.L (K := Fin 2) ![𝟙 x.P.A.left, (Out.mulA x.P.A 2).left] ![((2 : ℕ) : ℤ) ^ 2, -1] :=
      laws.mulPull _ x.P 2
    have e := (hasGen_iff hL _ _).1 (h.pull y.left)
    have e₂ : y ≫ Out.mulA x.P.A 2 = y ^ 2 := by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      ← Over.comp_left, e₂, zpow_neg, zpow_one, mul_inv_eq_one] at e
    refine e.symm.trans ?_
    norm_num
  have key := prod_quad_rows_mul (q := ptCls x.P.L T) (diff₃_ptCls hL ⟨cub.t, cub.isGen⟩)
    (by simpa only [MonObj.comp_one] using hconst 1) h2 (fun r c => al r c) (m : ℤ)
    (fun c c' => by
      have := congrFun (congrFun hal c) c'
      simpa [Matrix.mul_apply, Matrix.one_apply] using this)
    (fun c => Out.powPr x.P.A c) (fun r => toUnit T ≫ ξ r) (fun r => hconst _) (fun c => by
      have e := congrArg (fun z : Pt x => toUnit T ≫ z) (hk c)
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
        MonObj.comp_one] at e
      simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero] using e)
  refine (hasGen_iff hL _ _).2 ?_
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_eq_one, Finset.prod_zpow]
  refine Eq.trans (Finset.prod_congr rfl fun r _ => ?_) key
  rw [alMap, List.prod_ofFn]

end GlobalTheory.SimilPull
