import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section pre

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r)

def rdsVp (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) A :=
  (((List.finRange r).take i).reverse.map fun l => L.Tl Y l).prod

def rdsVvp (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) A :=
  (((List.finRange r).take i).reverse.map fun l => L.Tvl Y l).prod

/- English proof (translation)
Simplify using `[rdsVp]`.
-/
theorem rdsVp_zero (Y : ℂ) : rdsVp L Y 0 = 1 := by simp [rdsVp]

/- English proof (translation)
Simplify using `[rdsVvp]`.
-/
theorem rdsVvp_zero (Y : ℂ) : rdsVvp L Y 0 = 1 := by simp [rdsVvp]

/- English proof (translation)
Simplify using `[rdsVp, List.take_add_one, h]`.
-/
theorem rdsVp_succ (Y : ℂ) (i : ℕ) (h : i < r) : rdsVp L Y (i + 1) = L.Tl Y ⟨i, h⟩ * rdsVp L Y i := by
  simp [rdsVp, List.take_add_one, h]

/- English proof (translation)
Simplify using `[rdsVvp, List.take_add_one, h]`.
-/
theorem rdsVvp_succ (Y : ℂ) (i : ℕ) (h : i < r) : rdsVvp L Y (i + 1) = L.Tvl Y ⟨i, h⟩ * rdsVvp L Y i := by
  simp [rdsVvp, List.take_add_one, h]

/- English proof (translation)
Simplify using `[R.LevelData.Tprod, rdsVp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]`.
-/
theorem rds_tprod (Y : ℂ) : L.Tprod Y = rdsVp L Y r := by
  simp [R.LevelData.Tprod, rdsVp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

/- English proof (translation)
Simplify using `[R.LevelData.Tvprod, rdsVvp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]`.
-/
theorem rds_tvprod (Y : ℂ) : L.Tvprod Y = rdsVvp L Y r := by
  simp [R.LevelData.Tvprod, rdsVvp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

/- English proof (translation)
Simplify using `[R.LevelData.Tl, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem rds_Tl_mul_0 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tl Y l * V) 0 0 = (algebraMap ℂ A Y + L.p l) * V 0 0 + -L.c l * V 1 0 := by
  simp [R.LevelData.Tl, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[R.LevelData.Tl, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem rds_Tl_mul_1 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tl Y l * V) 1 0 = L.ci l * V 0 0 := by
  simp [R.LevelData.Tl, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem rds_Tvl_mul_0 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tvl Y l * V) 0 0 = (algebraMap ℂ A Y - L.pb l) * V 0 0 + -L.cb l * V 1 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem rds_Tvl_mul_1 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tvl Y l * V) 1 0 = L.cbi l * V 0 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

end pre

section rad

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rdsR_fst_neg (a : Pr V) : (-a).1 = -a.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rdsR_fst_sub (a b : Pr V) : (a - b).1 = a.1 - b.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rdsR_fst_one : (1 : Pr V).1 = 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rdsR_fst_zero : (0 : Pr V).1 = 0 := rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)

/- English proof (translation)
The claim follows from `X.op_apply l i Φ`.
-/
theorem rds_op_coe (l : Fin r) (i : Fin 6) (Φ : RadSp k r z z' π π') :
    ((X.op l i Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn k r (Wq →L[ℂ] Wp)) :=
  X.op_apply l i Φ

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ Φ`. Rewrite using `[rdsVp_zero]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `c g`. Simplify using `only [Matrix.one_apply_eq, rdsR_fst_one, Module.End.one_apply]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `c g`.

Simplify using `only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), rdsR_fst_zero, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply]`. Both sides reduce to the same expression. Consider the case `succ i ih`. Introduce `hi Φ`. Establish `h : i < r` using `hi`.

Take `⟨hA, hB⟩` from `ih (Nat.le_of_lt h) Φ`. Establish `hp : (L.p ⟨i, h⟩).1 = X.op ⟨i, h⟩ 0` using `by rw [hL.1 ⟨i, h⟩]; rfl`. Establish `hc : (L.c ⟨i, h⟩).1 = X.op ⟨i, h⟩ 1` using `by rw [hL.2.2.1 ⟨i, h⟩]; rfl`. Establish `hci : (L.ci ⟨i, h⟩).1 = X.op ⟨i, h⟩ 2` using `by rw [hL.2.2.2.1 ⟨i, h⟩]; rfl`. Rewrite using `[rdsVp_succ L Y i h, rds_Tl_mul_0, rds_Tl_mul_1]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : (((algebraMap ℂ (Pr (RadSp k r z z' π π')) Y + L.p ⟨i, h⟩) * rdsVp L Y i 0 0 + -L.c ⟨i, h⟩ * rdsVp L Y i 1 0).1 Φ : RadSp k r z z' π π') = Y • ((rdsVp L Y i 0 0).1 Φ) + X.op ⟨i, h⟩ 0 ((rdsVp L Y i 0 0).1 Φ) - X.op ⟨i, h⟩ 1 ((rdsVp L Y i 1 0).1 Φ)`. Rewrite using `[rds_fst_add, rds_fst_mul, rds_fst_mul, rds_fst_add, rds_fst_alg, rdsR_fst_neg, hp, hc]`. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply, Module.algebraMap_end_apply, sub_eq_add_neg]`. Rewrite using `[e, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, rds_op_coe, rds_op_coe, hA, hB]`.

Use function extensionality and compare the values at `c g`. Simplify using `only [crd, Q.cmp, Q.vAB, dif_pos h, if_true, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]`. Both sides reduce to the same expression. Establish `e : ((L.ci ⟨i, h⟩ * rdsVp L Y i 0 0).1 Φ : RadSp k r z z' π π') = X.op ⟨i, h⟩ 2 ((rdsVp L Y i 0 0).1 Φ)`. Rewrite using `[rds_fst_mul, hci]`.

Both sides reduce to the same expression. Rewrite using `[e, rds_op_coe, hA]`. Use function extensionality and compare the values at `c g`. Simplify using `only [crd, Q.cmp, Q.vAB, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem rds_vab_ind (hL : IsActualLevel X L) (Y : ℂ) : ∀ i : ℕ, i ≤ r → ∀ Φ : RadSp k r z z' π π',
    ((((rdsVp L Y i) 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (Q.vAB r Y i) 0) (Φ : Fn k r (Wq →L[ℂ] Wp)) ∧
      ((((rdsVp L Y i) 1 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (Q.vAB r Y i) 1) (Φ : Fn k r (Wq →L[ℂ] Wp)) := by
  intro i
  induction i with
  | zero =>
    intro _ Φ
    rw [rdsVp_zero]
    refine ⟨?_, ?_⟩
    · funext c g
      simp only [Matrix.one_apply_eq, rdsR_fst_one, Module.End.one_apply]
      rfl
    · funext c g
      simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), rdsR_fst_zero, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rfl
  | succ i ih =>
    intro hi Φ
    have h : i < r := hi
    obtain ⟨hA, hB⟩ := ih (Nat.le_of_lt h) Φ
    have hp : (L.p ⟨i, h⟩).1 = X.op ⟨i, h⟩ 0 := by rw [hL.1 ⟨i, h⟩]; rfl
    have hc : (L.c ⟨i, h⟩).1 = X.op ⟨i, h⟩ 1 := by rw [hL.2.2.1 ⟨i, h⟩]; rfl
    have hci : (L.ci ⟨i, h⟩).1 = X.op ⟨i, h⟩ 2 := by rw [hL.2.2.2.1 ⟨i, h⟩]; rfl
    rw [rdsVp_succ L Y i h, rds_Tl_mul_0, rds_Tl_mul_1]
    refine ⟨?_, ?_⟩
    · have e : (((algebraMap ℂ (Pr (RadSp k r z z' π π')) Y + L.p ⟨i, h⟩) * rdsVp L Y i 0 0 +
          -L.c ⟨i, h⟩ * rdsVp L Y i 1 0).1 Φ : RadSp k r z z' π π') =
          Y • ((rdsVp L Y i 0 0).1 Φ) + X.op ⟨i, h⟩ 0 ((rdsVp L Y i 0 0).1 Φ) -
            X.op ⟨i, h⟩ 1 ((rdsVp L Y i 1 0).1 Φ) := by
        rw [rds_fst_add, rds_fst_mul, rds_fst_mul, rds_fst_add, rds_fst_alg, rdsR_fst_neg, hp, hc]
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
          sub_eq_add_neg]
      rw [e, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, rds_op_coe, rds_op_coe, hA, hB]
      funext c g
      simp only [crd, Q.cmp, Q.vAB, dif_pos h, if_true, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      rfl
    · have e : ((L.ci ⟨i, h⟩ * rdsVp L Y i 0 0).1 Φ : RadSp k r z z' π π') =
          X.op ⟨i, h⟩ 2 ((rdsVp L Y i 0 0).1 Φ) := by
        rw [rds_fst_mul, hci]
        rfl
      rw [e, rds_op_coe, hA]
      funext c g
      simp only [crd, Q.cmp, Q.vAB, dif_pos h]
      rfl

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ Φ`. Rewrite using `[rdsVvp_zero]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `c g`. Simplify using `only [Matrix.one_apply_eq, rdsR_fst_one, Module.End.one_apply]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `c g`.

Simplify using `only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), rdsR_fst_zero, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply]`. Both sides reduce to the same expression. Consider the case `succ i ih`. Introduce `hi Φ`. Establish `h : i < r` using `hi`.

Take `⟨hA, hB⟩` from `ih (Nat.le_of_lt h) Φ`. Establish `hp : (L.pb ⟨i, h⟩).1 = X.op ⟨i, h⟩ 3` using `by rw [hL.2.1 ⟨i, h⟩]; rfl`. Establish `hc : (L.cb ⟨i, h⟩).1 = X.op ⟨i, h⟩ 4` using `by rw [hL.2.2.2.2.1 ⟨i, h⟩]; rfl`. Establish `hci : (L.cbi ⟨i, h⟩).1 = X.op ⟨i, h⟩ 5` using `by rw [hL.2.2.2.2.2.1 ⟨i, h⟩]; rfl`. Rewrite using `[rdsVvp_succ L Y i h, rds_Tvl_mul_0, rds_Tvl_mul_1]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : (((algebraMap ℂ (Pr (RadSp k r z z' π π')) Y - L.pb ⟨i, h⟩) * rdsVvp L Y i 0 0 + -L.cb ⟨i, h⟩ * rdsVvp L Y i 1 0).1 Φ : RadSp k r z z' π π') = Y • ((rdsVvp L Y i 0 0).1 Φ) - X.op ⟨i, h⟩ 3 ((rdsVvp L Y i 0 0).1 Φ) - X.op ⟨i, h⟩ 4 ((rdsVvp L Y i 1 0).1 Φ)`. Rewrite using `[rds_fst_add, rds_fst_mul, rds_fst_mul, rdsR_fst_sub, rds_fst_alg, rdsR_fst_neg, hp, hc]`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, Module.algebraMap_end_apply, sub_eq_add_neg]`. Rewrite using `[e, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul, rds_op_coe, rds_op_coe, hA, hB]`.

Use function extensionality and compare the values at `c g`. Simplify using `only [crd, Q.cmp, CutMP.vABm, dif_pos h, if_true, Pi.sub_apply, Pi.smul_apply]`. Both sides reduce to the same expression. Establish `e : ((L.cbi ⟨i, h⟩ * rdsVvp L Y i 0 0).1 Φ : RadSp k r z z' π π') = X.op ⟨i, h⟩ 5 ((rdsVvp L Y i 0 0).1 Φ)`. Rewrite using `[rds_fst_mul, hci]`.

Both sides reduce to the same expression. Rewrite using `[e, rds_op_coe, hA]`. Use function extensionality and compare the values at `c g`. Simplify using `only [crd, Q.cmp, CutMP.vABm, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem rds_vabm_ind (hL : IsActualLevel X L) (Y : ℂ) : ∀ i : ℕ, i ≤ r → ∀ Φ : RadSp k r z z' π π',
    ((((rdsVvp L Y i) 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (CutMP.vABm r Y i) 0) (Φ : Fn k r (Wq →L[ℂ] Wp)) ∧
      ((((rdsVvp L Y i) 1 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (CutMP.vABm r Y i) 1) (Φ : Fn k r (Wq →L[ℂ] Wp)) := by
  intro i
  induction i with
  | zero =>
    intro _ Φ
    rw [rdsVvp_zero]
    refine ⟨?_, ?_⟩
    · funext c g
      simp only [Matrix.one_apply_eq, rdsR_fst_one, Module.End.one_apply]
      rfl
    · funext c g
      simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), rdsR_fst_zero, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rfl
  | succ i ih =>
    intro hi Φ
    have h : i < r := hi
    obtain ⟨hA, hB⟩ := ih (Nat.le_of_lt h) Φ
    have hp : (L.pb ⟨i, h⟩).1 = X.op ⟨i, h⟩ 3 := by rw [hL.2.1 ⟨i, h⟩]; rfl
    have hc : (L.cb ⟨i, h⟩).1 = X.op ⟨i, h⟩ 4 := by rw [hL.2.2.2.2.1 ⟨i, h⟩]; rfl
    have hci : (L.cbi ⟨i, h⟩).1 = X.op ⟨i, h⟩ 5 := by rw [hL.2.2.2.2.2.1 ⟨i, h⟩]; rfl
    rw [rdsVvp_succ L Y i h, rds_Tvl_mul_0, rds_Tvl_mul_1]
    refine ⟨?_, ?_⟩
    · have e : (((algebraMap ℂ (Pr (RadSp k r z z' π π')) Y - L.pb ⟨i, h⟩) * rdsVvp L Y i 0 0 +
          -L.cb ⟨i, h⟩ * rdsVvp L Y i 1 0).1 Φ : RadSp k r z z' π π') =
          Y • ((rdsVvp L Y i 0 0).1 Φ) - X.op ⟨i, h⟩ 3 ((rdsVvp L Y i 0 0).1 Φ) -
            X.op ⟨i, h⟩ 4 ((rdsVvp L Y i 1 0).1 Φ) := by
        rw [rds_fst_add, rds_fst_mul, rds_fst_mul, rdsR_fst_sub, rds_fst_alg, rdsR_fst_neg, hp, hc]
        simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
          Module.algebraMap_end_apply, sub_eq_add_neg]
      rw [e, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul, rds_op_coe, rds_op_coe, hA, hB]
      funext c g
      simp only [crd, Q.cmp, CutMP.vABm, dif_pos h, if_true, Pi.sub_apply, Pi.smul_apply]
      rfl
    · have e : ((L.cbi ⟨i, h⟩ * rdsVvp L Y i 0 0).1 Φ : RadSp k r z z' π π') =
          X.op ⟨i, h⟩ 5 ((rdsVvp L Y i 0 0).1 Φ) := by
        rw [rds_fst_mul, hci]
        rfl
      rw [e, rds_op_coe, hA]
      funext c g
      simp only [crd, Q.cmp, CutMP.vABm, dif_pos h]
      rfl

/- English proof (translation)
Introduce `ls`. Proceed by induction on `ls with`. Consider the case `nil`. Introduce `Φ`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> (funext c g; simp only [List.map_nil, List.prod_nil, one_smul]; rfl)`.

Consider the case `cons a ls ih`. Introduce `Φ`. Take `⟨h1, h2⟩` from `ih Φ`. Establish `hc : (L.c a).1 = X.op a 1` using `by rw [hL.2.2.1 a]; rfl`. Establish `hcb : (L.cb a).1 = X.op a 4` using `by rw [hL.2.2.2.2.1 a]; rfl`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_cons, List.prod_cons, rds_fst_mul, hc, Module.End.mul_apply, rds_op_coe, h1]`. Use function extensionality and compare the values at `c g`. Simplify using `only [crd, opL, cOp, List.map_cons, List.prod_cons, smul_smul]`. Rewrite using `[List.map_cons, List.prod_cons, rds_fst_mul, hcb, Module.End.mul_apply, rds_op_coe, h2]`.

Use function extensionality and compare the values at `c g`. Simplify using `only [crd, opL, cbOp, List.map_cons, List.prod_cons, smul_smul]`.
-/
theorem rds_cprod (hL : IsActualLevel X L) : ∀ (ls : List (Fin r)) (Φ : RadSp k r z z' π π'),
    ((((ls.map L.c).prod).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        (fun c g => (ls.map fun l => c l).prod • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) ∧
      ((((ls.map L.cb).prod).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        (fun c g => (ls.map fun l => star (c l)).prod • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) := by
  intro ls
  induction ls with
  | nil =>
    intro Φ
    refine ⟨?_, ?_⟩ <;> (funext c g; simp only [List.map_nil, List.prod_nil, one_smul]; rfl)
  | cons a ls ih =>
    intro Φ
    obtain ⟨h1, h2⟩ := ih Φ
    have hc : (L.c a).1 = X.op a 1 := by rw [hL.2.2.1 a]; rfl
    have hcb : (L.cb a).1 = X.op a 4 := by rw [hL.2.2.2.2.1 a]; rfl
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, rds_fst_mul, hc, Module.End.mul_apply, rds_op_coe, h1]
      funext c g
      simp only [crd, opL, cOp, List.map_cons, List.prod_cons, smul_smul]
    · rw [List.map_cons, List.prod_cons, rds_fst_mul, hcb, Module.End.mul_apply, rds_op_coe, h2]
      funext c g
      simp only [crd, opL, cbOp, List.map_cons, List.prod_cons, smul_smul]

end rad

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' X L hL y Φ`. Establish `hDr : ∀ Ψ : RadSp P.k P.r z z' π π', (((L.Dr).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) = CutMP.dMul (CutMP.drF P.r) (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp))`. Introduce `Ψ`. Rewrite using `[R.LevelData.Dr, List.ofFn_eq_map, (rds_cprod X L hL _ Ψ).1]`. Use function extensionality and compare the values at `c g`.

Simplify using `only [CutMP.dMul, CutMP.drF, List.map_map, Function.comp_def]`. Rewrite using `[← List.ofFn_eq_map, List.prod_ofFn]`. Establish `hDrb : ∀ Ψ : RadSp P.k P.r z z' π π', (((L.Drb).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) = CutMP.dMul (CutMP.drbF P.r) (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp))`. Introduce `Ψ`. Rewrite using `[R.LevelData.Drb, List.ofFn_eq_map, (rds_cprod X L hL _ Ψ).2]`.

Use function extensionality and compare the values at `c g`. Simplify using `only [CutMP.dMul, CutMP.drbF, List.map_map, Function.comp_def]`. Rewrite using `[← List.ofFn_eq_map, List.prod_ofFn, map_prod]`. Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[R.LevelData.Ahat, rds_fst_mul, Module.End.mul_apply, hDr, R.LevelData.Ar, rds_tprod, (rds_vab_ind X L hL y P.r le_rfl Φ).1]`. Rewrite using `[R.LevelData.Ahatv, rds_fst_mul, Module.End.mul_apply, hDrb, R.LevelData.Avr, rds_tvprod, (rds_vabm_ind X L hL y P.r le_rfl Φ).1]`.
-/
theorem spectral_radial_action : RDSARad := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X L hL y Φ
  have hDr : ∀ Ψ : RadSp P.k P.r z z' π π',
      (((L.Dr).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
        CutMP.dMul (CutMP.drF P.r) (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Ψ
    rw [R.LevelData.Dr, List.ofFn_eq_map, (rds_cprod X L hL _ Ψ).1]
    funext c g
    simp only [CutMP.dMul, CutMP.drF, List.map_map, Function.comp_def]
    rw [← List.ofFn_eq_map, List.prod_ofFn]
  have hDrb : ∀ Ψ : RadSp P.k P.r z z' π π',
      (((L.Drb).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
        CutMP.dMul (CutMP.drbF P.r) (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Ψ
    rw [R.LevelData.Drb, List.ofFn_eq_map, (rds_cprod X L hL _ Ψ).2]
    funext c g
    simp only [CutMP.dMul, CutMP.drbF, List.map_map, Function.comp_def]
    rw [← List.ofFn_eq_map, List.prod_ofFn, map_prod]
    rfl
  refine ⟨?_, ?_⟩
  · rw [R.LevelData.Ahat, rds_fst_mul, Module.End.mul_apply, hDr, R.LevelData.Ar, rds_tprod,
      (rds_vab_ind X L hL y P.r le_rfl Φ).1]
  · rw [R.LevelData.Ahatv, rds_fst_mul, Module.End.mul_apply, hDrb, R.LevelData.Avr, rds_tvprod,
      (rds_vabm_ind X L hL y P.r le_rfl Φ).1]

end Formalism.FourierDecayAlt.P.CutSE
