import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeelAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.DensExactInertOf

open Finset

noncomputable section

namespace DensInertW

def arF (q i : ℕ) : ℝ := 1 - (-1 : ℝ) ^ i * ((q : ℝ) ^ i)⁻¹

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ar_densProd_eq (q n m c : ℕ) :
    Formalism.L2.SG.DensExact.densProd q (-1) n m c = ∏ i ∈ Icc (n + 1 - (m + c)) n, arF q i := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ar_f_zero (q : ℕ) : arF q 0 = 0 := by
  simp [arF]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem ar_valN (q n : ℕ) (hq : 0 < q) :
    ((valN q (n + 1) : ℤ) : ℝ) = (q : ℝ) ^ (2 * n + 1) * arF q (n + 1) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hb : (q : ℝ) ^ (n + 1) * ((q : ℝ) ^ (n + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq')
  simp only [valN, arF, Nat.add_sub_cancel]
  push_cast
  linear_combination ((-1 : ℝ) ^ (n + 1) * (q : ℝ) ^ n) * hb

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ar_valN_zero (q : ℕ) : valN q 0 = 0 := by
  simp [valN]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem ar_valZ (q N : ℕ) (hq : 0 < q) :
    ((valZ q (N + 2) : ℤ) : ℝ) - 1 = (q : ℝ) ^ (2 * N + 3) * arF q (N + 2) * arF q (N + 1) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have ha : (q : ℝ) ^ (N + 2) * ((q : ℝ) ^ (N + 2))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq')
  have hb : (q : ℝ) ^ (N + 1) * ((q : ℝ) ^ (N + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq')
  have hs : (-1 : ℝ) ^ N * (-1 : ℝ) ^ N = 1 := by rw [← mul_pow]; norm_num
  simp only [valZ, arF]
  rw [show 2 * (N + 2) - 1 = 2 * N + 3 by omega, show N + 2 - 1 = N + 1 by omega]
  push_cast
  linear_combination hs + (-((-1 : ℝ) ^ N) * (q : ℝ) ^ (N + 2) + ((-1 : ℝ) ^ N) ^ 2) * hb +
    ((-1 : ℝ) ^ N * (q : ℝ) ^ (N + 1) + ((-1 : ℝ) ^ N) ^ 2 +
      ((-1 : ℝ) ^ N) ^ 2 * ((q : ℝ) ^ (N + 1) * ((q : ℝ) ^ (N + 1))⁻¹ - 1)) * ha

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ar_valZ_zero (q : ℕ) : valZ q 0 - 1 = 0 := by
  simp [valZ]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ar_valZ_one (q : ℕ) : valZ q 1 - 1 = 0 := by
  simp [valZ]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem densityProduct_succ_succ_add (q n r c : ℕ) :
    Formalism.L2.SG.DensExact.densProd q (-1) (n + 1) (r + 1 + c) c =
      arF q (n + 1) * Formalism.L2.SG.DensExact.densProd q (-1) n (r + c) c := by
  unfold Formalism.L2.SG.DensExact.densProd
  rw [show n + 1 + 1 - (r + 1 + c + c) = n + 1 - (r + c + c) by omega,
    Finset.prod_Icc_succ_top (by omega), mul_comm]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem densityProduct_add_two_succ_succ (q N c : ℕ) :
    Formalism.L2.SG.DensExact.densProd q (-1) (N + 2) (c + 1) (c + 1) =
      arF q (N + 2) * arF q (N + 1) * Formalism.L2.SG.DensExact.densProd q (-1) N c c := by
  unfold Formalism.L2.SG.DensExact.densProd arF
  rw [show N + 2 + 1 - (c + 1 + (c + 1)) = N + 1 - (c + c) by omega, show N + 2 = N + 1 + 1 from rfl,
    Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega)]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem ar_zero_prod (q n m c : ℕ) (h : n + 1 ≤ m + c) :
    Formalism.L2.SG.DensExact.densProd q (-1) n m c = 0 := by
  unfold Formalism.L2.SG.DensExact.densProd
  exact Finset.prod_eq_zero (i := 0) (Finset.mem_Icc.mpr ⟨by omega, Nat.zero_le _⟩) (by simp)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem frameCount_zero_mul_pow (q : ℕ) (hq : 0 < q) : ∀ c n : ℕ,
    ((Fr q n 0 c : ℤ) : ℝ) * (q : ℝ) ^ (c ^ 2) =
      (q : ℝ) ^ (2 * n * c) * Formalism.L2.SG.DensExact.densProd q (-1) n c c := by
  intro c
  induction c with
  | zero =>
    intro n
    have h0 : Fr q n 0 0 = 1 := by simp [Fr]
    unfold Formalism.L2.SG.DensExact.densProd
    rw [h0, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    simp
  | succ c ih =>
    intro n
    match n with
    | 0 =>
      rw [ar_zero_prod q 0 (c + 1) (c + 1) (by omega)]
      have h0 : Fr q 0 0 (c + 1) = 0 := by simp only [Fr, ar_valZ_zero, zero_mul]
      rw [h0]
      simp
    | 1 =>
      rw [ar_zero_prod q 1 (c + 1) (c + 1) (by omega)]
      have h0 : Fr q 1 0 (c + 1) = 0 := by simp only [Fr, ar_valZ_one, zero_mul]
      rw [h0]
      simp
    | N + 2 =>
      have hF : ((Fr q (N + 2) 0 (c + 1) : ℤ) : ℝ) =
          (((valZ q (N + 2) : ℤ) : ℝ) - 1) * (q : ℝ) ^ (2 * c) * ((Fr q N 0 c : ℤ) : ℝ) := by
        simp [Fr]
      rw [hF, ar_valZ q N hq, densityProduct_add_two_succ_succ]
      have e2 := ih N
      calc _ = (q : ℝ) ^ (2 * N + 4 * c + 4) * arF q (N + 2) * arF q (N + 1) *
            (((Fr q N 0 c : ℤ) : ℝ) * (q : ℝ) ^ (c ^ 2)) := by ring
        _ = _ := by rw [e2]; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem ar_main (q : ℕ) (hq : 0 < q) : ∀ r c n : ℕ,
    ((Fr q n r c : ℤ) : ℝ) * (q : ℝ) ^ ((r + c) ^ 2) =
      (q : ℝ) ^ (2 * n * (r + c)) * Formalism.L2.SG.DensExact.densProd q (-1) n (r + c) c := by
  intro r
  induction r with
  | zero =>
    intro c n
    simpa only [zero_add] using frameCount_zero_mul_pow q hq c n
  | succ r ih =>
    intro c n
    match n with
    | 0 =>
      rw [ar_zero_prod q 0 (r + 1 + c) c (by omega)]
      have h0 : Fr q 0 (r + 1) c = 0 := by simp only [Fr, ar_valN_zero, zero_mul]
      rw [h0]
      simp
    | N + 1 =>
      have hF : ((Fr q (N + 1) (r + 1) c : ℤ) : ℝ) = ((valN q (N + 1) : ℤ) : ℝ) * ((Fr q N r c : ℤ) : ℝ) := by
        simp [Fr]
      rw [hF, ar_valN q N hq, densityProduct_succ_succ_add]
      have e2 := ih c N
      calc _ = (q : ℝ) ^ (2 * N + 2 * r + 2 * c + 2) * arF q (N + 1) *
            (((Fr q N r c : ℤ) : ℝ) * (q : ℝ) ^ ((r + c) ^ 2)) := by ring
        _ = _ := by rw [e2]; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities.
-/
theorem quadraticDifferenceArith : Arith := by
  intro q n m r hq hrm
  have hq0 : 0 < q := by omega
  have e := ar_main q hq0 r (m - r) n
  rw [show r + (m - r) = m by omega] at e
  have hA : (q : ℝ) ^ (2 * n * m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  rw [div_div_eq_mul_div, e, mul_div_cancel_left₀ _ hA]

end DensInertW
