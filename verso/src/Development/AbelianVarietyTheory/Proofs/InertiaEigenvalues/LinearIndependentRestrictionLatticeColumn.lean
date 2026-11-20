import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

open Fin.NatCast in

/- English proof (translation)
Introduce `l _ P r ω hω hdet n _ _ U x hx c hc hsum`. Use `haveI : NeZero r := ⟨fun h => by subst h; exact x.1.elim0⟩`. Use `set Q : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)).val with hQ`. Establish `hQp : Q * resMat n ω = 1` using `(resGL n ω hdet).inv_mul`. Use `set d := Matrix.vecMul c Q with hd_def`.

Establish `hcd : c = Matrix.vecMul d (resMat n ω)`. Rewrite using `[hd_def, Matrix.vecMul_vecMul, hQp, Matrix.vecMul_one]`. Establish `hexp : ∀ i k, c (i, k) = ∑ m : Fin r, d (i, m) * fr l m (ω k)`. Introduce `i k`. Use `conv_lhs => rw [hcd]`.

Simplify using `only [Matrix.vecMul, dotProduct, resMat_apply, Fintype.sum_prod_type, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[hj]`.

Simplify using the standard rewrite rules. Establish `hrel : ∀ i (m : Fin r), d (i, m + 1) = fr l 1 (d (i, m))`. Introduce `i`. Establish `hv : Matrix.vecMul (fun m' : Fin r => fr l 1 (d (i, m' - 1)) - d (i, m')) (frobMat ω) = 0`. Use function extensionality and compare the values at `k`.

Simplify using `only [Matrix.vecMul, dotProduct, frobMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply]`. Rewrite using `[← hexp i k]`. Establish `h1 : ∑ m' : Fin r, fr l 1 (d (i, m' - 1)) * fr l m' (ω k) = ∑ m : Fin r, fr l 1 (d (i, m)) * fr l 1 (fr l m (ω k))`. Use `(Fintype.sum_equiv (Equiv.addRight (1 : Fin r)) _ _ fun m => ?_).symm` and prove the remaining obligations. Simplify using `only [Equiv.coe_addRight, add_sub_cancel_right]`.

Use `congr 1`. Rewrite using `[← fr_add, ← fr_mod (hω k) ((m + 1 : Fin r) : ℕ), ← fr_mod (hω k) (1 + (m : ℕ))]`. Use `congr 1`. Rewrite using `[Fin.val_add, Nat.mod_mod, add_comm]`. Break down `Nat.lt_or_ge 1 r with h | h` into its components or cases.

Rewrite using `[Fin.val_one', Nat.mod_eq_of_lt h]`. Establish `: r = 1` using `by have := NeZero.ne r; omega`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[h1]`.

Repeatedly rewrite using `[← map_mul]`. Rewrite using `[← map_sum, ← hexp i k, hc (i, k), sub_self]`. Establish `h0` using `Matrix.eq_zero_of_vecMul_eq_zero hdet hv`. Introduce `m`. Use `congrFun h0 (m + 1)` as an intermediate fact.

Simplify using `only [add_sub_cancel_right, Pi.zero_apply, sub_eq_zero] at this`. Conclude with `this.symm`. Establish `hprop : ∀ i (k : ℕ), d (i, x.1 + (k : Fin r)) = fr l k (d (i, x.1))`. Introduce `i k`. Proceed by induction on `k with`.

Consider the case `zero => simp [fr_zero]`. Consider the case `succ k ih => rw [Nat.cast_succ, ← add_assoc, hrel, ih, ← fr_add, add_comm]`. Establish `hfix : ∀ i, fr l r (d (i, x.1)) = d (i, x.1)`. Introduce `i`. Rewrite using `[← hprop, Fin.natCast_self, add_zero]`.

Establish `hU0 : (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = Q.map (kd P) * Matrix.blockDiagonal (fun m => (U m : Matrix n n P.R.BdR))` using `rfl`. Establish `hid : ∑ a, kd P (c a) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) a (x.2, x.1) = ∑ j, kd P (d (j, x.1)) * (U x.1 : Matrix n n P.R.BdR) j x.2`. Establish `step : ∀ a, kd P (c a) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) a (x.2, x.1) = ∑ j, kd P (c a) * kd P (Q a (j, x.1)) * (U x.1 : Matrix n n P.R.BdR) j x.2`. Introduce `a`. Rewrite using `[hU0]`.

Simplify using `only [Matrix.mul_apply, Matrix.blockDiagonal_apply, Matrix.map_apply, Fintype.sum_prod_type, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]`. Rewrite using `[Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hd_def, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul]`. Establish `hzero : (fun j => d (j, x.1)) = 0` using `hx _ hfix (hid ▸ hsum)`.

Establish `hd0 : d = 0`. Use function extensionality and compare the values at `⟨i, m⟩`. Establish `hm : m = x.1 + (((m - x.1 : Fin r) : ℕ) : Fin r)` using `by simp`. Rewrite using `[hm, hprop, show d (i, x.1) = 0 from congrFun hzero i, map_zero]`. Both sides reduce to the same expression.

Rewrite using `[hcd, hd0, Matrix.zero_vecMul]`.
-/
theorem eq_zero_of_sum_kd_mul_U0_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x : Fin r × n), (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) → ∀ c : n × Fin r → ↥(MaximalUnramifiedExtension l), (∀ i, fr l 1 (c i) = c i) → ∑ i, kd P (c i) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i (x.2, x.1) ∈ Fil P 1 → c = 0 := by
  intro l _ P r ω hω hdet n _ _ U x hx c hc hsum
  haveI : NeZero r := ⟨fun h => by subst h; exact x.1.elim0⟩
  set Q : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)).val with hQ
  have hQp : Q * resMat n ω = 1 := (resGL n ω hdet).inv_mul
  set d := Matrix.vecMul c Q with hd_def
  have hcd : c = Matrix.vecMul d (resMat n ω) := by
    rw [hd_def, Matrix.vecMul_vecMul, hQp, Matrix.vecMul_one]
  have hexp : ∀ i k, c (i, k) = ∑ m : Fin r, d (i, m) * fr l m (ω k) := by
    intro i k
    conv_lhs => rw [hcd]
    simp only [Matrix.vecMul, dotProduct, resMat_apply, Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have hrel : ∀ i (m : Fin r), d (i, m + 1) = fr l 1 (d (i, m)) := by
    intro i
    have hv : Matrix.vecMul (fun m' : Fin r => fr l 1 (d (i, m' - 1)) - d (i, m')) (frobMat ω) = 0 := by
      funext k
      simp only [Matrix.vecMul, dotProduct, frobMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply]
      rw [← hexp i k]
      have h1 : ∑ m' : Fin r, fr l 1 (d (i, m' - 1)) * fr l m' (ω k)
          = ∑ m : Fin r, fr l 1 (d (i, m)) * fr l 1 (fr l m (ω k)) := by
        refine (Fintype.sum_equiv (Equiv.addRight (1 : Fin r)) _ _ fun m => ?_).symm
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
        congr 1
        rw [← fr_add, ← fr_mod (hω k) ((m + 1 : Fin r) : ℕ), ← fr_mod (hω k) (1 + (m : ℕ))]
        congr 1
        rw [Fin.val_add, Nat.mod_mod, add_comm]
        rcases Nat.lt_or_ge 1 r with h | h
        · rw [Fin.val_one', Nat.mod_eq_of_lt h]
        · have : r = 1 := by have := NeZero.ne r; omega
          subst this; simp
      rw [h1]
      simp_rw [← map_mul]
      rw [← map_sum, ← hexp i k, hc (i, k), sub_self]
    have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
    intro m
    have := congrFun h0 (m + 1)
    simp only [add_sub_cancel_right, Pi.zero_apply, sub_eq_zero] at this
    exact this.symm
  have hprop : ∀ i (k : ℕ), d (i, x.1 + (k : Fin r)) = fr l k (d (i, x.1)) := by
    intro i k
    induction k with
    | zero => simp [fr_zero]
    | succ k ih => rw [Nat.cast_succ, ← add_assoc, hrel, ih, ← fr_add, add_comm]
  have hfix : ∀ i, fr l r (d (i, x.1)) = d (i, x.1) := by
    intro i; rw [← hprop, Fin.natCast_self, add_zero]
  have hU0 : (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR)
      = Q.map (kd P) * Matrix.blockDiagonal (fun m => (U m : Matrix n n P.R.BdR)) := rfl
  have hid : ∑ a, kd P (c a) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) a (x.2, x.1)
      = ∑ j, kd P (d (j, x.1)) * (U x.1 : Matrix n n P.R.BdR) j x.2 := by
    have step : ∀ a, kd P (c a) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) a (x.2, x.1)
        = ∑ j, kd P (c a) * kd P (Q a (j, x.1)) * (U x.1 : Matrix n n P.R.BdR) j x.2 := by
      intro a
      rw [hU0]
      simp only [Matrix.mul_apply, Matrix.blockDiagonal_apply, Matrix.map_apply, Fintype.sum_prod_type, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hd_def, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul]
  have hzero : (fun j => d (j, x.1)) = 0 := hx _ hfix (hid ▸ hsum)
  have hd0 : d = 0 := by
    funext ⟨i, m⟩
    have hm : m = x.1 + (((m - x.1 : Fin r) : ℕ) : Fin r) := by simp
    rw [hm, hprop, show d (i, x.1) = 0 from congrFun hzero i, map_zero]
    rfl
  rw [hcd, hd0, Matrix.zero_vecMul]

end GlobalTheory.PMon.ResR
