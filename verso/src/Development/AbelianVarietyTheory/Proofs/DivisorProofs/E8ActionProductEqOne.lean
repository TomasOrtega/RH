import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.PrimPic

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

def pt (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (x : T ⟶ B) : GlobalTheory.CechPic.Pic T.left := GlobalTheory.CechPic.pull x.left c

def lam (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (x y : T ⟶ B) : GlobalTheory.CechPic.Pic T.left :=
  pt c (x * y) - pt c x - pt c y + pt c 1

/- English proof (translation)
Establish `ht` using `DVR.pullGen_isGen _ _ _ _ cub.isGen (lift x (lift x' y)).left`. Establish `h0` using `(GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_linComb M.isLB _ _)).2 ⟨_, ht⟩`. Rewrite `h0` using `[GlobalTheory.CechPic.cls_linComb M.isLB]`. Establish `e` using `prod_cub x x' y (U := Multiplicative (FreeAbelianGroup (T.left ⟶ B.left))) (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))`. Establish `e'` using `congrArg (fun u => FreeAbelianGroup.lift (fun ψ => GlobalTheory.CechPic.pull ψ (GlobalTheory.CechPic.cls M.L M.isLB)) (Multiplicative.toAdd u)) e`.

Simplify using `only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul, toAdd_inv, map_sum, map_zsmul, map_add, map_neg, FreeAbelianGroup.lift_apply_of] at e'`. Establish `e''` using `e'.symm.trans h0`. Simplify using `only [lam, pt]`. Take the linear combination `(norm := abel) e''`.
-/
theorem lam_mul_left (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (x x' y : T ⟶ B) :
    lam (GlobalTheory.CechPic.cls M.L M.isLB) (x * x') y =
      lam (GlobalTheory.CechPic.cls M.L M.isLB) x y + lam (GlobalTheory.CechPic.cls M.L M.isLB) x' y := by
  have ht := DVR.pullGen_isGen _ _ _ _ cub.isGen (lift x (lift x' y)).left
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_linComb M.isLB _ _)).2 ⟨_, ht⟩
  rw [GlobalTheory.CechPic.cls_linComb M.isLB] at h0
  have e := prod_cub x x' y (U := Multiplicative (FreeAbelianGroup (T.left ⟶ B.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have e' := congrArg (fun u => FreeAbelianGroup.lift (fun ψ => GlobalTheory.CechPic.pull ψ (GlobalTheory.CechPic.cls M.L M.isLB))
    (Multiplicative.toAdd u)) e
  simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul, toAdd_inv, map_sum, map_zsmul, map_add, map_neg,
    FreeAbelianGroup.lift_apply_of] at e'
  have e'' := e'.symm.trans h0
  simp only [lam, pt]
  linear_combination (norm := abel) e''

/- English proof (translation)
Simplify using `only [lam]`. Rewrite using `[_root_.mul_comm x y]`. Normalize the expressions using the abelian group laws.
-/
theorem lam_comm (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (x y : T ⟶ B) : lam c x y = lam c y x := by
  simp only [lam]; rw [_root_.mul_comm x y]; abel

/- English proof (translation)
Simplify using `only [lam, _root_.one_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem lam_one_left (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (y : T ⟶ B) : lam c 1 y = 0 := by
  simp only [lam, _root_.one_mul]; abel

def lamHom (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (y : T ⟶ B) :
    Additive (T ⟶ B) →+ GlobalTheory.CechPic.Pic T.left :=
  AddMonoidHom.mk' (fun x => lam (GlobalTheory.CechPic.cls M.L M.isLB) (Additive.toMul x) y)
    (fun a b => lam_mul_left M cub (Additive.toMul a) (Additive.toMul b) y)

/- English proof (translation)
Establish `e` using `map_sum (lamHom M cub y) (fun i => m i • Additive.ofMul (s i)) Finset.univ`. Simplify using `only [map_zsmul] at e`. Use `Eq.trans ?_ e` and prove the remaining obligations. Use `show _ = lam _ (Additive.toMul (∑ i, m i • Additive.ofMul (s i))) y`. Use `congr 1`.
-/
theorem lam_prod_left (M : RigLB B) (cub : CubicalStr B M) {T : Over S} {Ix : Type} [Fintype Ix]
    (s : Ix → (T ⟶ B)) (m : Ix → ℤ) (y : T ⟶ B) :
    lam (GlobalTheory.CechPic.cls M.L M.isLB) (∏ i, s i ^ m i) y = ∑ i, m i • lam (GlobalTheory.CechPic.cls M.L M.isLB) (s i) y := by
  have e := map_sum (lamHom M cub y) (fun i => m i • Additive.ofMul (s i)) Finset.univ
  simp only [map_zsmul] at e
  refine Eq.trans ?_ e
  show _ = lam _ (Additive.toMul (∑ i, m i • Additive.ofMul (s i))) y
  congr 1

/- English proof (translation)
Rewrite using `[lam_comm, lam_prod_left M cub]`. Simplify using `only [lam_comm _ (s _) x]`.
-/
theorem lam_prod_right (M : RigLB B) (cub : CubicalStr B M) {T : Over S} {Ix : Type} [Fintype Ix]
    (x : T ⟶ B) (s : Ix → (T ⟶ B)) (m : Ix → ℤ) :
    lam (GlobalTheory.CechPic.cls M.L M.isLB) x (∏ i, s i ^ m i) = ∑ i, m i • lam (GlobalTheory.CechPic.cls M.L M.isLB) x (s i) := by
  rw [lam_comm, lam_prod_left M cub]
  simp only [lam_comm _ (s _) x]

/- English proof (translation)
Rewrite using `[lam_comm, lam_mul_left M cub, lam_comm _ y, lam_comm _ y']`.
-/
theorem lam_mul_right (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (x y y' : T ⟶ B) :
    lam (GlobalTheory.CechPic.cls M.L M.isLB) x (y * y') =
      lam (GlobalTheory.CechPic.cls M.L M.isLB) x y + lam (GlobalTheory.CechPic.cls M.L M.isLB) x y' := by
  rw [lam_comm, lam_mul_left M cub, lam_comm _ y, lam_comm _ y']

def bil (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (N : Matrix (Fin 8) (Fin 8) ℤ) (s t : Fin 8 → (T ⟶ B)) :
    GlobalTheory.CechPic.Pic T.left :=
  ∑ a, ∑ b, N a b • lam c (s a) (t b)

/- English proof (translation)
Simplify using `only [bil, lam_prod_left M cub, Matrix.mul_apply, Matrix.transpose_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[_root_.mul_comm]`.
-/
theorem bil_left (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (N m : Matrix (Fin 8) (Fin 8) ℤ)
    (s t : Fin 8 → (T ⟶ B)) :
    bil (GlobalTheory.CechPic.cls M.L M.isLB) N (fun a => ∏ k, s k ^ m a k) t =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) (m.transpose * N) s t := by
  simp only [bil, lam_prod_left M cub, Matrix.mul_apply, Matrix.transpose_apply, Finset.smul_sum, Finset.sum_smul,
    smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  rw [_root_.mul_comm]

/- English proof (translation)
Simplify using `only [bil, lam_prod_right M cub, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem bil_right (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (N m : Matrix (Fin 8) (Fin 8) ℤ)
    (s t : Fin 8 → (T ⟶ B)) :
    bil (GlobalTheory.CechPic.cls M.L M.isLB) N s (fun b => ∏ k, t k ^ m b k) =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) (N * m) s t := by
  simp only [bil, lam_prod_right M cub, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `h1 : bil (T` using `T) (GlobalTheory.CechPic.cls M.L M.isLB) W 1 1 = 0 := by`. Simplify using `[bil, lam_one_left]`. Establish `h2 : bil (GlobalTheory.CechPic.cls M.L M.isLB) W y x = bil (GlobalTheory.CechPic.cls M.L M.isLB) W.transpose x y`. Simplify using `only [bil, Matrix.transpose_apply]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [lam_comm _ (y _)]`. Establish `h3 : bil (GlobalTheory.CechPic.cls M.L M.isLB) W (x * y) (x * y) = bil (GlobalTheory.CechPic.cls M.L M.isLB) W x x + bil (GlobalTheory.CechPic.cls M.L M.isLB) W x y + bil (GlobalTheory.CechPic.cls M.L M.isLB) W y x + bil (GlobalTheory.CechPic.cls M.L M.isLB) W y y`. Simplify using `only [bil, Pi.mul_apply, lam_mul_left M cub, lam_mul_right M cub, smul_add, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Establish `h4 : bil (GlobalTheory.CechPic.cls M.L M.isLB) (W + W.transpose) x y = bil (GlobalTheory.CechPic.cls M.L M.isLB) W x y + bil (GlobalTheory.CechPic.cls M.L M.isLB) W.transpose x y`.

Simplify using `only [bil, Matrix.add_apply, add_smul, Finset.sum_add_distrib]`. Rewrite using `[h1, h3, h4, ← h2]`. Normalize the expressions using the abelian group laws.
-/
theorem bil_mul (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (W : Matrix (Fin 8) (Fin 8) ℤ)
    (x y : Fin 8 → (T ⟶ B)) :
    bil (GlobalTheory.CechPic.cls M.L M.isLB) W (x * y) (x * y) - bil (GlobalTheory.CechPic.cls M.L M.isLB) W x x -
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W y y + bil (GlobalTheory.CechPic.cls M.L M.isLB) W 1 1 =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) (W + W.transpose) x y := by
  have h1 : bil (T := T) (GlobalTheory.CechPic.cls M.L M.isLB) W 1 1 = 0 := by
    simp [bil, lam_one_left]
  have h2 : bil (GlobalTheory.CechPic.cls M.L M.isLB) W y x = bil (GlobalTheory.CechPic.cls M.L M.isLB) W.transpose x y := by
    simp only [bil, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [lam_comm _ (y _)]
  have h3 : bil (GlobalTheory.CechPic.cls M.L M.isLB) W (x * y) (x * y) = bil (GlobalTheory.CechPic.cls M.L M.isLB) W x x +
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W x y + bil (GlobalTheory.CechPic.cls M.L M.isLB) W y x +
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W y y := by
    simp only [bil, Pi.mul_apply, lam_mul_left M cub, lam_mul_right M cub, smul_add, Finset.sum_add_distrib]
    abel
  have h4 : bil (GlobalTheory.CechPic.cls M.L M.isLB) (W + W.transpose) x y = bil (GlobalTheory.CechPic.cls M.L M.isLB) W x y +
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W.transpose x y := by
    simp only [bil, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  rw [h1, h3, h4, ← h2]; abel

def preH {G T T' : Over S} [GrpObj G] (ρ : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun x := ρ ≫ x
  map_one' := MonObj.comp_one ρ
  map_mul' x y := MonObj.comp_mul ρ x y

/- English proof (translation)
Rewrite using `[(GlobalTheory.CechPic.cls_eq_iff hL (LB.isLB_linComb M.isLB (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2)))).2 h, GlobalTheory.CechPic.cls_linComb M.isLB, map_sum]`. Establish `hm : ∀ x y : A ⟶ B, s.left ≫ (x * y).left = ((s ≫ x) * (s ≫ y)).left` using `fun x y => by`. Rewrite using `[← Over.comp_left, MonObj.comp_mul]`. Establish `h1 : s.left ≫ (1 : A ⟶ B).left = (1 : T ⟶ B).left`. Rewrite using `[← Over.comp_left, MonObj.comp_one]`.

Establish `hx : ∀ x : A ⟶ B, s.left ≫ x.left = (s ≫ x).left` using `fun x => (Over.comp_left _ _ _ s x).symm`. Establish `v0 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 0 = p` using `fun _ _ _ _ => rfl`. Establish `v1 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 1 = q` using `fun _ _ _ _ => rfl`. Establish `v2 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 2 = r` using `fun _ _ _ _ => rfl`. Establish `v3 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 3 = t` using `fun _ _ _ _ => rfl`.

Simplify using `only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, Fintype.sum_prod_type, Fin.sum_univ_four, bil, lam, pt, lamPts, negε, v0, v1, v2, v3, hm, h1, hx]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [smul_add, smul_sub, mul_neg, _root_.mul_one, neg_neg, neg_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem cechPicard_pullback_e8Bundle_class (W : Matrix (Fin 8) (Fin 8) ℤ) {A : Over S} [GrpObj A] (pr : Fin 8 → (A ⟶ B))
    (L : LB A.left) (hL : L.IsLB) (M : RigLB B) (h : IsE8WeightedBundle W pr L M.L) {T : Over S} (s : T ⟶ A) :
    GlobalTheory.CechPic.pull s.left (GlobalTheory.CechPic.cls L hL) =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W (fun a => s ≫ pr a) (fun b => s ≫ pr b) := by
  rw [(GlobalTheory.CechPic.cls_eq_iff hL (LB.isLB_linComb M.isLB (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2)))).2 h,
    GlobalTheory.CechPic.cls_linComb M.isLB, map_sum]
  have hm : ∀ x y : A ⟶ B, s.left ≫ (x * y).left = ((s ≫ x) * (s ≫ y)).left := fun x y => by
    rw [← Over.comp_left, MonObj.comp_mul]
  have h1 : s.left ≫ (1 : A ⟶ B).left = (1 : T ⟶ B).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have hx : ∀ x : A ⟶ B, s.left ≫ x.left = (s ≫ x).left := fun x => (Over.comp_left _ _ _ s x).symm
  have v0 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 0 = p := fun _ _ _ _ => rfl
  have v1 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 1 = q := fun _ _ _ _ => rfl
  have v2 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 2 = r := fun _ _ _ _ => rfl
  have v3 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 3 = t := fun _ _ _ _ => rfl
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, Fintype.sum_prod_type, Fin.sum_univ_four, bil, lam, pt, lamPts,
    negε, v0, v1, v2, v3, hm, h1, hx]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_add, smul_sub, mul_neg, _root_.mul_one, neg_neg, neg_smul]
  abel

/- English proof (translation)
Use `(GlobalTheory.CechPic.cls_linComb hL (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum A ![u, v] I.down).left) (fun I => (-1) ^ (2 - I.down.card)) hc).trans ?_` and prove the remaining obligations. Use `(Fintype.sum_equiv Equiv.ulift _ (fun I => ((-1 : ℤ) ^ (2 - I.card)) • GlobalTheory.CechPic.pull (psum A ![u, v] I).left (GlobalTheory.CechPic.cls L hL)) (fun _ => rfl)).trans ?_` and prove the remaining obligations. Rewrite using `[show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]`. Establish `p₀ : psum A ![u, v] ∅ = 1` using `rfl`. Establish `p₁ : psum A ![u, v] {0} = u` using `_root_.mul_one u`.

Establish `p₂ : psum A ![u, v] {1} = v` using `_root_.mul_one v`. Establish `p₃ : psum A ![u, v] {0, 1} = u * v` using `congrArg (u * ·) (_root_.mul_one v)`. Establish `q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1` using `by decide`. Establish `q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1` using `by decide`. Establish `q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1` using `by decide`.

Rewrite using `[p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]`. Simplify using `only [one_smul, neg_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem cls_cube2 {A : Over S} [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB) {T : Over S}
    (u v : T ⟶ A) (hc : (cubeLB A ![u, v] L).IsLB) :
    GlobalTheory.CechPic.cls (cubeLB A ![u, v] L) hc =
      GlobalTheory.CechPic.pull (u * v).left (GlobalTheory.CechPic.cls L hL) - GlobalTheory.CechPic.pull u.left (GlobalTheory.CechPic.cls L hL) -
        GlobalTheory.CechPic.pull v.left (GlobalTheory.CechPic.cls L hL) + GlobalTheory.CechPic.pull (1 : T ⟶ A).left (GlobalTheory.CechPic.cls L hL) := by
  refine (GlobalTheory.CechPic.cls_linComb hL (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum A ![u, v] I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) hc).trans ?_
  refine (Fintype.sum_equiv Equiv.ulift _ (fun I => ((-1 : ℤ) ^ (2 - I.card)) •
    GlobalTheory.CechPic.pull (psum A ![u, v] I).left (GlobalTheory.CechPic.cls L hL)) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum A ![u, v] ∅ = 1 := rfl
  have p₁ : psum A ![u, v] {0} = u := _root_.mul_one u
  have p₂ : psum A ![u, v] {1} = v := _root_.mul_one v
  have p₃ : psum A ![u, v] {0, 1} = u * v := congrArg (u * ·) (_root_.mul_one v)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [one_smul, neg_smul]
  abel

/- English proof (translation)
Rewrite using `[cls_cube2 L hL u v hc, cechPicard_pullback_e8Bundle_class W pr L hL M h, cechPicard_pullback_e8Bundle_class W pr L hL M h, cechPicard_pullback_e8Bundle_class W pr L hL M h, cechPicard_pullback_e8Bundle_class W pr L hL M h]`. Establish `hm : (fun a => (u * v) ≫ pr a) = (fun a => u ≫ pr a) * (fun a => v ≫ pr a)` using `funext fun a => by haveI := hpr a; exact MonObj.mul_comp u v (pr a)`. Establish `h1 : (fun a => (1 : T ⟶ A) ≫ pr a) = 1` using `funext fun a => by haveI := hpr a; exact MonObj.one_comp (pr a)`. Rewrite using `[hm, h1]`. Conclude with `bil_mul M cub W _ _`.
-/
theorem cube_class_e8Bundle_eighth_power (W : Matrix (Fin 8) (Fin 8) ℤ) {A : Over S} [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (A ⟶ B))
    (hpr : ∀ a, IsMonHom (pr a)) (L : LB A.left) (hL : L.IsLB) (M : RigLB B) (cub : CubicalStr B M)
    (h : IsE8WeightedBundle W pr L M.L) {T : Over S} (u v : T ⟶ A) (hc : (cubeLB A ![u, v] L).IsLB) :
    GlobalTheory.CechPic.cls (cubeLB A ![u, v] L) hc =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) (e8 W) (fun a => u ≫ pr a) (fun b => v ≫ pr b) := by
  rw [cls_cube2 L hL u v hc, cechPicard_pullback_e8Bundle_class W pr L hL M h, cechPicard_pullback_e8Bundle_class W pr L hL M h, cechPicard_pullback_e8Bundle_class W pr L hL M h,
    cechPicard_pullback_e8Bundle_class W pr L hL M h]
  have hm : (fun a => (u * v) ≫ pr a) = (fun a => u ≫ pr a) * (fun a => v ≫ pr a) := funext fun a => by
    haveI := hpr a; exact MonObj.mul_comp u v (pr a)
  have h1 : (fun a => (1 : T ⟶ A) ≫ pr a) = 1 := funext fun a => by
    haveI := hpr a; exact MonObj.one_comp (pr a)
  rw [hm, h1]
  exact bil_mul M cub W _ _

/- English proof (translation)
Simplify using `only [e8, Matrix.transpose_add, Matrix.transpose_transpose]`. Conclude with `add_comm _ _`.
-/
theorem e8_transpose' (W : Matrix (Fin 8) (Fin 8) ℤ) : (e8 W).transpose = e8 W := by
  simp only [e8, Matrix.transpose_add, Matrix.transpose_transpose]; exact add_comm _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actMat_zero (W : Matrix (Fin 8) (Fin 8) ℤ) : actMat W 0 = (e8 W).adjugate * W := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actMat_one (W : Matrix (Fin 8) (Fin 8) ℤ) : actMat W 1 = (e8 W).adjugate * W.transpose := rfl

/- English proof (translation)
Establish `hd : (e8 W).det = 1` using `hW.2`. Rewrite using `[actMat_zero, actMat_one, Matrix.transpose_mul, Matrix.adjugate_transpose, e8_transpose', Matrix.mul_assoc, Matrix.adjugate_mul, ← Matrix.mul_assoc, Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem mat_adj (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    (actMat W 0).transpose * e8 W = e8 W * actMat W 1 := by
  have hd : (e8 W).det = 1 := hW.2
  rw [actMat_zero, actMat_one, Matrix.transpose_mul, Matrix.adjugate_transpose, e8_transpose', Matrix.mul_assoc,
    Matrix.adjugate_mul, ← Matrix.mul_assoc, Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Establish `hd : (e8 W).det = 1` using `hW.2`. Rewrite using `[actMat_zero, ← Matrix.mul_assoc, Matrix.mul_adjugate, hd, one_smul, Matrix.one_mul]`.
-/
theorem mat_prim (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) : e8 W * actMat W 0 = W := by
  have hd : (e8 W).det = 1 := hW.2
  rw [actMat_zero, ← Matrix.mul_assoc, Matrix.mul_adjugate, hd, one_smul, Matrix.one_mul]

/- English proof (translation)
Establish `hd : (e8 W).det = 1` using `hW.2`. Rewrite using `[actMat_zero, actMat_one, ← Matrix.mul_add]`. Use `show (e8 W).adjugate * e8 W = 1`. Rewrite using `[Matrix.adjugate_mul, hd, one_smul]`.
-/
theorem mat_sum (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) : actMat W 0 + actMat W 1 = 1 := by
  have hd : (e8 W).det = 1 := hW.2
  rw [actMat_zero, actMat_one, ← Matrix.mul_add]
  show (e8 W).adjugate * e8 W = 1
  rw [Matrix.adjugate_mul, hd, one_smul]

/- English proof (translation)
Introduce `W hW gQ K _ P' B _ _ M pr hF hP hE act hact hacts`. Use `letI := P'.isAb.comm`. Take `⟨cub⟩` from `hF.2.2.1`. Establish `hmon : ∀ a, IsMonHom (pr a)` using `hP.1`. Establish `hpre : ∀ {T : Over (Sp K)} (s : T ⟶ P'.A) (i : Fin 2), (fun a => (s ≫ act i) ≫ pr a) = fun a => ∏ k, (s ≫ pr k) ^ actMat W i a k` using `fun s i => funext fun a => by`.

Rewrite using `[Category.assoc, hacts i a]`. Conclude with `(map_prod (preH (G := B) s) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (preH (G := B) s) _ _)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, -, hx⟩` from `hP.2 P'.A pr`. Establish `h1 : ∀ a, (act 0 * act 1) ≫ pr a = pr a`.

Introduce `a`. Use `haveI := hmon a`. Rewrite using `[MonObj.mul_comp, hacts 0 a, hacts 1 a, ← Finset.prod_mul_distrib]`. Establish `hs` using `mat_sum W hW`. Rewrite using `[Finset.prod_eq_single a]`.

Rewrite using `[← zpow_add, ← Matrix.add_apply, hs, Matrix.one_apply_eq, zpow_one]`. Introduce `b _ hb`. Rewrite using `[← zpow_add, ← Matrix.add_apply, hs, Matrix.one_apply_ne (Ne.symm hb), zpow_zero]`. Introduce `ha`. Conclude with `absurd (Finset.mem_univ a) ha`.

Conclude with `(hx _ h1).trans (hx _ fun a => Category.id_comp _).symm`. Establish `hc1 : (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L).IsLB` using `LB.isLB_linComb P'.isLB _ _`. Establish `hc2 : (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L).IsLB` using `LB.isLB_linComb P'.isLB _ _`. Use `(GlobalTheory.CechPic.cls_eq_iff hc1 hc2).1 ?_` and prove the remaining obligations. Rewrite using `[cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE, cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE, hpre (fst P'.A P'.A) 0, hpre (snd P'.A P'.A) 1, bil_left M cub, bil_right M cub, mat_adj W hW]`.

Establish `hc3 : (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L).IsLB` using `LB.isLB_linComb P'.isLB _ _`. Use `(GlobalTheory.CechPic.cls_eq_iff P'.isLB hc3).1 ?_` and prove the remaining obligations. Rewrite using `[cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE]`. Establish `e1` using `cechPicard_pullback_e8Bundle_class W pr P'.L P'.isLB M hE (𝟙 P'.A)`. Rewrite `e1` using `[Over.id_left, GlobalTheory.CechPic.pull_id]`.

Rewrite using `[e1]`. Establish `h2 : (fun b => act 0 ≫ pr b) = fun b => ∏ k, pr k ^ actMat W 0 b k` using `funext fun b => hacts 0 b`. Simplify using `only [Category.id_comp]`. Rewrite using `[h2, bil_right M cub, mat_prim W hW]`.
-/
theorem e8_act_endomorphism_prod_eq_id : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  letI := P'.isAb.comm
  act 0 * act 1 = 𝟙 P'.A ∧
  LBIso (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L) (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L) ∧
  LBIso P'.L (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L) := by
  intro W hW gQ K _ P' B _ _ M pr hF hP hE act hact hacts
  letI := P'.isAb.comm
  obtain ⟨cub⟩ := hF.2.2.1
  have hmon : ∀ a, IsMonHom (pr a) := hP.1
  have hpre : ∀ {T : Over (Sp K)} (s : T ⟶ P'.A) (i : Fin 2),
      (fun a => (s ≫ act i) ≫ pr a) = fun a => ∏ k, (s ≫ pr k) ^ actMat W i a k := fun s i => funext fun a => by
    rw [Category.assoc, hacts i a]
    exact (map_prod (preH (G := B) s) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (preH (G := B) s) _ _)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := hP.2 P'.A pr
    have h1 : ∀ a, (act 0 * act 1) ≫ pr a = pr a := by
      intro a
      haveI := hmon a
      rw [MonObj.mul_comp, hacts 0 a, hacts 1 a, ← Finset.prod_mul_distrib]
      have hs := mat_sum W hW
      rw [Finset.prod_eq_single a]
      · rw [← zpow_add, ← Matrix.add_apply, hs, Matrix.one_apply_eq, zpow_one]
      · intro b _ hb
        rw [← zpow_add, ← Matrix.add_apply, hs, Matrix.one_apply_ne (Ne.symm hb), zpow_zero]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    exact (hx _ h1).trans (hx _ fun a => Category.id_comp _).symm
  · have hc1 : (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
    have hc2 : (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hc1 hc2).1 ?_
    rw [cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE, cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE,
      hpre (fst P'.A P'.A) 0, hpre (snd P'.A P'.A) 1, bil_left M cub, bil_right M cub, mat_adj W hW]
  · have hc3 : (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
    refine (GlobalTheory.CechPic.cls_eq_iff P'.isLB hc3).1 ?_
    rw [cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE]
    have e1 := cechPicard_pullback_e8Bundle_class W pr P'.L P'.isLB M hE (𝟙 P'.A)
    rw [Over.id_left, GlobalTheory.CechPic.pull_id] at e1
    rw [e1]
    have h2 : (fun b => act 0 ≫ pr b) = fun b => ∏ k, pr k ^ actMat W 0 b k := funext fun b => hacts 0 b
    simp only [Category.id_comp]
    rw [h2, bil_right M cub, mat_prim W hW]

end GlobalTheory.Poinc.Sep.E8Fibration.PrimPic
