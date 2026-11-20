import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

noncomputable section

open Finset GroundTheory.Automorphic GroundTheory.Automorphic.Spherical AddMonoidAlgebra

namespace PositivityTheory.RgJS

namespace SchurJacobiTrudiEvaluation

variable {m : ℕ}

def hL (m p : ℕ) : LaurentRing m := ∑ k ∈ Finset.Nat.antidiagonalTuple m p, monomial (fun i => (k i : ℤ))

def hLZ (m : ℕ) (z : ℤ) : LaurentRing m := if z < 0 then 0 else hL m z.toNat

def jL (m : ℕ) (l : Fin m → ℕ) : LaurentRing m := (Matrix.of fun i j : Fin m => hLZ m ((l j : ℤ) - j + i)).det

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem evalAt_monomial_eq_prod_zpow (z : Fin m → ℂˣ) (v : Fin m → ℤ) :
    evalAt z (monomial v) = ∏ i, ((z i : ℂ) ^ v i) := by
  rw [evalAt_apply]
  simp [monomialChar]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem evalAt_monomial_nat (z : Fin m → ℂˣ) (k : Fin m → ℕ) :
    evalAt z (monomial (fun i => (k i : ℤ))) = ∏ i, (z i : ℂ) ^ k i := by
  rw [evalAt_monomial_eq_prod_zpow]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem evalAt_hL (z : Fin m → ℂˣ) (p : ℕ) : evalAt z (hL m p) = hN p (fun i => (z i : ℂ)) := by
  unfold hL hN
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact evalAt_monomial_nat z k

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem evalAt_hLZ (z : Fin m → ℂˣ) (w : ℤ) : evalAt z (hLZ m w) = hZ w (fun i => (z i : ℂ)) := by
  unfold hLZ hZ
  split_ifs
  · simp
  · exact evalAt_hL z _

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem evalAt_jL (z : Fin m → ℂˣ) (l : Fin m → ℕ) : evalAt z (jL m l) = jt (fun i => (z i : ℂ)) l := by
  unfold jL jt
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [evalAt_hLZ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem evalAt_alternant_nat (z : Fin m → ℂˣ) (μ : Fin m → ℕ) :
    evalAt z (alternant fun i => (μ i : ℤ)) = altN (fun i => (z i : ℂ)) μ := by
  rw [alternant_eq_det, AlgHom.map_det]
  unfold altN
  congr 1
  ext a b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [evalAt_monomial_eq_prod_zpow, Fintype.prod_eq_single a]
  · simp
  · intro i hi
    simp [Pi.single_apply, hi]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem staircase_eq : staircase m = fun i => ((stair m i : ℕ) : ℤ) := by
  funext i
  simp only [staircase, stair]
  have := i.isLt
  omega

end SchurJacobiTrudiEvaluation

open SchurJacobiTrudiEvaluation in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem schur_jacobi_trudi_of_alternating : AltJT → SchurJT := by
  intro h m z l
  have key : alternant (staircase m) * schur (fun i => (l i : ℤ)) = alternant (staircase m) * jL m l := by
    rw [alternant_mul_schur]
    apply eq_of_forall_evalAt
    intro w
    rw [map_mul, evalAt_jL, staircase_eq]
    have e : (fun i => (l i : ℤ)) + (fun i => ((stair m i : ℕ) : ℤ)) = fun i => (((l + stair m) i : ℕ) : ℤ) := by
      funext i
      simp
    rw [e, evalAt_alternant_nat, evalAt_alternant_nat]
    exact h m _ l
  rw [mul_left_cancel₀ alternant_staircase_ne_zero key]
  exact evalAt_jL z l

end PositivityTheory.RgJS
