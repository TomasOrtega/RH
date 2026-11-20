import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

variable {N : ℕ}

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next c =>`. Simplify using `[rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`. Use `next p q hp hq =>`. Rewrite using `[map_add, Polynomial.coeff_add, hp, hq]`.

Use `next p v hp =>`. Rewrite using `[map_mul, Polynomial.mul_coeff_zero, hp]`. Simplify using `only [rowGen, MvPolynomial.aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem rowGen_coeff_zero (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    (rowGen ℚ a b f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on
  · next c =>
    simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · next p q hp hq =>
    rw [map_add, Polynomial.coeff_add, hp, hq]
  · next p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    simp only [rowGen, MvPolynomial.aeval_X]
    split_ifs <;> simp

/- English proof (translation)
Establish `hX : rowGen ℚ a b (X v : MvPolynomial (Fin N × Fin N) ℚ) = Polynomial.C (X v) + (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)`. Simplify using `only [rowGen, MvPolynomial.aeval_X]`. Establish `h0` using `rowGen_coeff_zero a b p`. Simplify using `only [rowDiv, map_mul, hX, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0]`. Apply the tactic sequence `split_ifs with h <;> simp [Polynomial.coeff_C, Polynomial.coeff_X_mul, add_comm]`.
-/
theorem rowDiv_one_mul_X (a b : Fin N) (p : MvPolynomial (Fin N × Fin N) ℚ) (v : Fin N × Fin N) :
    rowDiv ℚ a b 1 (p * X v) = rowDiv ℚ a b 1 p * X v + p * (if v.1 = b then X (a, v.2) else 0) := by
  have hX : rowGen ℚ a b (X v : MvPolynomial (Fin N × Fin N) ℚ) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
    simp only [rowGen, MvPolynomial.aeval_X]
  have h0 := rowGen_coeff_zero a b p
  simp only [rowDiv, map_mul, hX, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0]
  split_ifs with h <;> simp [Polynomial.coeff_C, Polynomial.coeff_X_mul, add_comm]

/- English proof (translation)
Simplify using `[polE, LinearMap.sum_apply]`.
-/
theorem polE_apply (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) ℚ) :
    polE N a b f = ∑ s : Fin N, X (a, s) * pderiv (b, s) f := by
  simp [polE, LinearMap.sum_apply]

/- English proof (translation)
Establish `key : ∀ s : Fin N, X (a, s) * pderiv (b, s) (p * X v) = X (a, s) * pderiv (b, s) p * X v + p * (if v = (b, s) then X (a, s) else 0)`. Introduce `s`. Rewrite using `[Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp only [smul_eq_mul] <;> ring`. Establish `hs : (∑ s : Fin N, (if v = (b, s) then (X (a, s) : MvPolynomial (Fin N × Fin N) ℚ) else 0)) = if v.1 = b then X (a, v.2) else 0`.

Take `⟨v1, v2⟩` from `v`. Distinguish the cases in `h : v1 = b`. Substitute `h` using the available equality. Simplify using `[Prod.ext_iff, eq_comm]`. Simplify using `[h]`.

Rewrite using `[polE_apply, polE_apply, Finset.sum_mul]`. Simplify using `only [key, Finset.sum_add_distrib, ← Finset.mul_sum, hs]`.
-/
theorem polE_mul_X (a b : Fin N) (p : MvPolynomial (Fin N × Fin N) ℚ) (v : Fin N × Fin N) :
    polE N a b (p * X v) = polE N a b p * X v + p * (if v.1 = b then X (a, v.2) else 0) := by
  have key : ∀ s : Fin N, X (a, s) * pderiv (b, s) (p * X v) =
      X (a, s) * pderiv (b, s) p * X v + p * (if v = (b, s) then X (a, s) else 0) := by
    intro s
    rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp only [smul_eq_mul] <;> ring
  have hs : (∑ s : Fin N, (if v = (b, s) then (X (a, s) : MvPolynomial (Fin N × Fin N) ℚ) else 0)) =
      if v.1 = b then X (a, v.2) else 0 := by
    obtain ⟨v1, v2⟩ := v
    by_cases h : v1 = b
    · subst h
      simp [Prod.ext_iff, eq_comm]
    · simp [h]
  rw [polE_apply, polE_apply, Finset.sum_mul]
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum, hs]

/- English proof (translation)
Introduce `N a b f`. Proceed by induction on `f using MvPolynomial.induction_on`. Use `next c =>`. Rewrite using `[polE_apply]`. Simplify using `[rowDiv, rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`.

Use `next p q hp hq =>`. Rewrite using `[map_add, hp, hq]`. Simplify using `only [rowDiv, map_add, Polynomial.coeff_add]`. Use `next p v hp =>`. Rewrite using `[polE_mul_X, rowDiv_one_mul_X, hp]`.
-/
theorem polynomial_eq_divisibility : PolEqRowDiv := by
  intro N a b f
  induction f using MvPolynomial.induction_on
  · next c =>
    rw [polE_apply]
    simp [rowDiv, rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · next p q hp hq =>
    rw [map_add, hp, hq]
    simp only [rowDiv, map_add, Polynomial.coeff_add]
  · next p v hp =>
    rw [polE_mul_X, rowDiv_one_mul_X, hp]

/- English proof (translation)
Simplify using `only [fockQ, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockQ_smul_right {σ : Type*} (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ f (c • g) = c * fockQ f g := by
  simp only [fockQ, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/- English proof (translation)
Introduce `hAdj hDD hPol hHw N ν hν`. Establish `hν' : Antitone (fun i : Fin N => ν i + 1)` using `fun a b hab => Nat.add_le_add_right (hν hab) 1`. Establish `hG'` using `hHw N ν hν`. Establish `heul : ∀ a : Fin N, rowDiv ℚ a a 1 (hw ℚ le_rfl (fun i => ν i + 1)) = (((ν a + 1 : ℕ) : ℚ)) • hw ℚ le_rfl (fun i => ν i + 1)`. Introduce `a`.

Use extensionality with `m`. Rewrite using `[lgraded_coeff_euler, MvPolynomial.coeff_smul, smul_eq_mul]`. Distinguish the cases in `hm : coeff m (hw ℚ le_rfl (fun i : Fin N => ν i + 1)) = 0`. Simplify using `[hm]`. Establish `hW` using `hwRowWeight ℚ N N le_rfl _ hν' hm`.

Establish `hWa` using `congrFun hW a`. Establish `hr : rowNu (r` using `N) (fun i : Fin N => ν i + 1) a = ν a + 1 := by`. Simplify using `[rowNu]`. Rewrite `hWa` using `[hr]`. Use `congr 1`.

Rewrite using `[← hWa]`. Use `norm_cast`. Simplify using `[Finsupp.weight_apply, Finsupp.sum, lgraded_wa, rowW, Pi.single_apply, eq_comm]`. Establish `hcap` using `Formalism.CohomologicalDescent.HeightDescentMinors.c2_holds_alt ℚ (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) (MvPolynomial (Fin N × Fin N) ℚ) N (polE N) ((N : ℚ) - 1) (fun i => ((ν i + 1 : ℕ) : ℚ)) (hw ℚ le_rfl (fun i => ν i + 1)) (fun i j hij => by`. Rewrite using `[Module.End.smul_def, hPol]`.

Conclude with `hwRaise ℚ N N le_rfl _ i j 1 hij le_rfl)`. Use the proof step `(fun i => by rw [Module.End.smul_def, hPol, heul])`. Rewrite `hcap` using `[← hDD N, Module.End.smul_def, Module.End.mul_apply, LinearMap.mulLeft_apply]`. Establish `hdet0 : detX N ≠ 0`. Introduce `h0`.

Establish `h1` using `hHw N (fun _ => 0) (fun _ _ _ => le_rfl)`. Rewrite `h1` using `[h0, zero_mul]`. Conclude with `hwNe ℚ N N le_rfl _ h1`. Establish `hD : detD N (detX N * hw ℚ le_rfl ν) = (∏ i : Fin N, ((N : ℚ) - 1 + ((ν i + 1 : ℕ) : ℚ) - ((i : ℕ) : ℚ))) • hw ℚ le_rfl ν`. Apply `mul_left_cancel₀ hdet0` to reduce the goal to its premises.

Rewrite using `[← hG', hcap, hG', mul_smul_comm]`. Rewrite using `[hAdj N (hw ℚ le_rfl ν) (detX N * hw ℚ le_rfl ν), hD, fockQ_smul_right]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi : (i : ℕ) ≤ ν i + N` using `by omega`.

Rewrite using `[Nat.cast_sub hi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem determinant_shift_norm : DetShiftNormOf := by
  intro hAdj hDD hPol hHw N ν hν
  have hν' : Antitone (fun i : Fin N => ν i + 1) := fun a b hab => Nat.add_le_add_right (hν hab) 1
  have hG' := hHw N ν hν

  have heul : ∀ a : Fin N, rowDiv ℚ a a 1 (hw ℚ le_rfl (fun i => ν i + 1)) =
      (((ν a + 1 : ℕ) : ℚ)) • hw ℚ le_rfl (fun i => ν i + 1) := by
    intro a
    ext m
    rw [lgraded_coeff_euler, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : coeff m (hw ℚ le_rfl (fun i : Fin N => ν i + 1)) = 0
    · simp [hm]
    · have hW := hwRowWeight ℚ N N le_rfl _ hν' hm
      have hWa := congrFun hW a
      have hr : rowNu (r := N) (fun i : Fin N => ν i + 1) a = ν a + 1 := by
        simp [rowNu]
      rw [hr] at hWa
      congr 1
      rw [← hWa]
      norm_cast
      simp [Finsupp.weight_apply, Finsupp.sum, lgraded_wa, rowW, Pi.single_apply, eq_comm]
  have hcap := Formalism.CohomologicalDescent.HeightDescentMinors.c2_holds_alt ℚ (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
    (MvPolynomial (Fin N × Fin N) ℚ) N (polE N) ((N : ℚ) - 1) (fun i => ((ν i + 1 : ℕ) : ℚ))
    (hw ℚ le_rfl (fun i => ν i + 1))
    (fun i j hij => by
      rw [Module.End.smul_def, hPol]
      exact hwRaise ℚ N N le_rfl _ i j 1 hij le_rfl)
    (fun i => by rw [Module.End.smul_def, hPol, heul])
  rw [← hDD N, Module.End.smul_def, Module.End.mul_apply, LinearMap.mulLeft_apply] at hcap
  have hdet0 : detX N ≠ 0 := by
    intro h0
    have h1 := hHw N (fun _ => 0) (fun _ _ _ => le_rfl)
    rw [h0, zero_mul] at h1
    exact hwNe ℚ N N le_rfl _ h1
  have hD : detD N (detX N * hw ℚ le_rfl ν) =
      (∏ i : Fin N, ((N : ℚ) - 1 + ((ν i + 1 : ℕ) : ℚ) - ((i : ℕ) : ℚ))) • hw ℚ le_rfl ν := by
    apply mul_left_cancel₀ hdet0
    rw [← hG', hcap, hG', mul_smul_comm]
  rw [hAdj N (hw ℚ le_rfl ν) (detX N * hw ℚ le_rfl ν), hD, fockQ_smul_right]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ ν i + N := by omega
  rw [Nat.cast_sub hi]
  push_cast
  ring

end PI.HookSteps
