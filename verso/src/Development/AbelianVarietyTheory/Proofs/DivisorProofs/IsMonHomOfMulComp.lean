import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixRingAct

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensAct

open GlobalTheory.Mum

section Hom

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]

end Hom

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def matAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) : D'.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j)

/- English proof (translation)
The claim follows from `T.lim.fac (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j) ⟨i⟩`.
-/
theorem matAct_pr (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    matAct T A ≫ T.pr i = ∏ j, T.pr j ^ A i j :=
  T.lim.fac (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j) ⟨i⟩

/- English proof (translation)
The claim follows from `T.lim.hom_ext fun i ↦ h i.as`.
-/
theorem hom_ext (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} {a b : X ⟶ D'.P.A}
    (h : ∀ i, a ≫ T.pr i = b ≫ T.pr i) : a = b :=
  T.lim.hom_ext fun i ↦ h i.as

def latAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) : D'.X :=
  T.xe.symm fun i ↦ ∑ j, A i j • T.xe y j

/- English proof (translation)
Simplify using `[latAct]`.
-/
theorem xe_latAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (i : Fin r) :
    T.xe (latAct T A y) i = ∑ j, A i j • T.xe y j := by
  simp [latAct]

section Ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]`.
-/
theorem zpow_finsetSum {M : Type} [CommGroup M] (a : M) {K : Type} (s : Finset K) (f : K → ℤ) :
    a ^ (∑ k ∈ s, f k) = ∏ k ∈ s, a ^ f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

/- English proof (translation)
Establish `hp` using `T.pr_hom`. Use `GlobalTheory.MatrixAction.isMonHom_of_points _ (fun X ↦ hom_ext T fun i ↦ ?_) (fun X x y ↦ hom_ext T fun i ↦ ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, MonObj.one_comp (T.pr i)]`. Use `Finset.prod_eq_one fun l _ ↦ ?_` and prove the remaining obligations. Rewrite using `[GrpObj.comp_zpow, MonObj.one_comp, one_zpow]`.

Rewrite using `[MonObj.mul_comp _ _ (T.pr i), Category.assoc, Category.assoc, Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun l _ ↦ ?_` and prove the remaining obligations. Rewrite using `[GrpObj.comp_zpow, GrpObj.comp_zpow, GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]`.
-/
theorem matAct_hom (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (matAct T A) := by
  have hp := T.pr_hom
  refine GlobalTheory.MatrixAction.isMonHom_of_points _ (fun X ↦ hom_ext T fun i ↦ ?_) (fun X x y ↦ hom_ext T fun i ↦ ?_)
  · rw [Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, MonObj.one_comp (T.pr i)]
    refine Finset.prod_eq_one fun l _ ↦ ?_
    rw [GrpObj.comp_zpow, MonObj.one_comp, one_zpow]
  · rw [MonObj.mul_comp _ _ (T.pr i), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    rw [GrpObj.comp_zpow, GrpObj.comp_zpow, GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

/- English proof (translation)
Use `hom_ext T fun i ↦ ?_` and prove the remaining obligations. Rewrite using `[matAct_pr, Category.id_comp, Finset.prod_eq_single i]`. Rewrite using `[Matrix.one_apply_eq, zpow_one]`. Introduce `l _ hl`. Rewrite using `[Matrix.one_apply_ne hl.symm, zpow_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem matAct_one (T : Tens D D' W) : matAct T 1 = 𝟙 _ := by
  refine hom_ext T fun i ↦ ?_
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · rw [Matrix.one_apply_eq, zpow_one]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zpow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use `hom_ext T fun i ↦ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, matAct_pr, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]`. Establish `e1 : ∀ k, matAct T B ≫ T.pr k ^ A i k = ∏ l, T.pr l ^ (A i k * B k l)` using `fun k ↦ by`. Rewrite using `[GrpObj.comp_zpow, matAct_pr, ← Finset.prod_zpow]`. Use `Finset.prod_congr rfl fun l _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[← zpow_mul, mul_comm]`. Rewrite using `[Finset.prod_congr rfl fun k _ ↦ e1 k, Finset.prod_comm]`. Use `Finset.prod_congr rfl fun l _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, zpow_finsetSum]`.
-/
theorem matAct_mul (T : Tens D D' W) (A B : Matrix (Fin r) (Fin r) ℤ) :
    matAct T (A * B) = matAct T B ≫ matAct T A := by
  refine hom_ext T fun i ↦ ?_
  rw [Category.assoc, matAct_pr, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  have e1 : ∀ k, matAct T B ≫ T.pr k ^ A i k = ∏ l, T.pr l ^ (A i k * B k l) := fun k ↦ by
    rw [GrpObj.comp_zpow, matAct_pr, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    rw [← zpow_mul, mul_comm]
  rw [Finset.prod_congr rfl fun k _ ↦ e1 k, Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Matrix.mul_apply, zpow_finsetSum]

/- English proof (translation)
Use `hom_ext T fun i ↦ ?_` and prove the remaining obligations. Use `T.pr_hom i` as an intermediate fact. Rewrite using `[MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun l _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, zpow_add]`.
-/
theorem matAct_add (T : Tens D D' W) (A B : Matrix (Fin r) (Fin r) ℤ) :
    matAct T (A + B) = matAct T A * matAct T B := by
  refine hom_ext T fun i ↦ ?_
  have := T.pr_hom i
  rw [MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Matrix.add_apply, zpow_add]

def latEnd (T : Tens D D' W) : Matrix (Fin r) (Fin r) ℤ →+* Module.End ℤ D'.X where
  toFun A :=
    { toFun := latAct T A
      map_add' := fun y z ↦ T.xe.injective (funext fun i ↦ by
        simp only [xe_latAct, map_add, Pi.add_apply, smul_add, Finset.sum_add_distrib])
      map_smul' := fun n y ↦ T.xe.injective (funext fun i ↦ by
        simp only [xe_latAct, map_zsmul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _) }
  map_one' := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, Module.End.one_apply]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl.symm, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h)
  map_mul' A B := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, Module.End.mul_apply, Matrix.mul_apply,
      Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm)
  map_zero' := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp [xe_latAct])
  map_add' A B := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, LinearMap.add_apply, map_add, Pi.add_apply,
      Matrix.add_apply, add_smul, Finset.sum_add_distrib])

abbrev tensModule (T : Tens D D' W) {O : Type} [Ring O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : Module O D'.X :=
  Module.compHom D'.X ((latEnd T).comp ρ)

def ringAct (T : Tens D D' W) {O : Type} [Ring O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : RingAct D'.P.A O where
  act a := matAct T (ρ a)
  hom a := matAct_hom T (ρ a)
  map_one := by rw [map_one, matAct_one]
  map_mul a b := by rw [map_mul, matAct_mul]
  map_add a b := by rw [map_add, matAct_add]; rfl

def cHom (D : DegPre R) : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
  AddMonoidHom.mk' (fun x ↦ Additive.ofMul (D.c x)) fun a b ↦ by rw [D.c_add]; rfl

/- English proof (translation)
Use `hom_ext T fun i ↦ ?_` and prove the remaining obligations. Rewrite using `[T.c_pr, Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, xe_latAct]`. Establish `e` using `map_sum (cHom D) (fun j ↦ A i j • T.xe y j) Finset.univ`. Simplify using `only [map_zsmul] at e`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[ofMul_prod]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[GrpObj.comp_zpow, T.c_pr, ofMul_zpow]`. Both sides reduce to the same expression.
-/
theorem c_lin (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) :
    D'.c (latAct T A y) = D'.c y ≫ matAct T A := by
  refine hom_ext T fun i ↦ ?_
  rw [T.c_pr, Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, xe_latAct]
  have e := map_sum (cHom D) (fun j ↦ A i j • T.xe y j) Finset.univ
  simp only [map_zsmul] at e
  apply Additive.ofMul.injective
  refine e.trans ?_
  rw [ofMul_prod]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [GrpObj.comp_zpow, T.c_pr, ofMul_zpow]
  rfl

end Ring

end GlobalTheory.TensAct
