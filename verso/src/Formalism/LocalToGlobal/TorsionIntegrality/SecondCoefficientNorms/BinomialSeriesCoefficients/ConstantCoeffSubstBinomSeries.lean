import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.C

variable {K : Type} [Field K] [CharZero K] {σ : Type}

/- English proof (translation)
Simplify using `[binom]`.
-/
theorem binom_zero (z : K) : binom z 0 = 1 := by simp [binom]

/- English proof (translation)
Unfold `binom`. Rewrite using `[Finset.prod_range_succ, Nat.factorial_succ]`. Establish `h0 : (n.factorial : K) ≠ 0` using `Nat.cast_ne_zero.2 n.factorial_ne_zero`. Establish `h1 : ((n : K) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem binom_succ (z : K) (n : ℕ) : ((n : K) + 1) * binom z (n + 1) = (z - n) * binom z n := by
  unfold binom
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  have h0 : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have h1 : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/- English proof (translation)
Unfold `binom`. Rewrite using `[Finset.prod_range_succ' (fun i : ℕ => z + 1 - (i : K)), Finset.prod_range_succ (fun i : ℕ => z - (i : K)), Nat.factorial_succ]`. Establish `h0 : (k.factorial : K) ≠ 0` using `Nat.cast_ne_zero.2 k.factorial_ne_zero`. Establish `h1 : ((k : K) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Establish `e : ∏ i ∈ range k, (z + 1 - ((i + 1 : ℕ) : K)) = ∏ i ∈ range k, (z - (i : K))` using `Finset.prod_congr rfl fun i _ => by push_cast; ring`.

Rewrite using `[e]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem binom_pascal (z : K) (k : ℕ) :
    binom (z + 1) (k + 1) = binom z (k + 1) + binom z k := by
  unfold binom
  rw [Finset.prod_range_succ' (fun i : ℕ => z + 1 - (i : K)),
    Finset.prod_range_succ (fun i : ℕ => z - (i : K)), Nat.factorial_succ]
  have h0 : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h1 : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have e : ∏ i ∈ range k, (z + 1 - ((i + 1 : ℕ) : K)) = ∏ i ∈ range k, (z - (i : K)) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [e]
  push_cast
  field_simp
  ring

/- English proof (translation)
Unfold `binom`. Rewrite using `[Finset.prod_range_succ']`. Simplify using the standard rewrite rules.
-/
theorem binom_zero_succ (k : ℕ) : binom (0 : K) (k + 1) = 0 := by
  unfold binom
  rw [Finset.prod_range_succ']
  simp

def binomSeries (z : K) : PowerSeries K := PowerSeries.mk (binom z)

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[add_mul, one_mul, map_add, PowerSeries.coeff_derivative, PowerSeries.coeff_smul]`. Consider the cases of `n with`. Consider the case `zero`. Establish `h` using `binom_succ z 0`.

Simplify using `only [binomSeries, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, smul_eq_mul]`. Move the coercions through the operations in `at h ⊢`. Take the linear combination `h`. Consider the case `succ n`. Establish `h` using `binom_succ z (n + 1)`.

Rewrite using `[PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]`. Simplify using `only [binomSeries, PowerSeries.coeff_mk, smul_eq_mul]`. Move the coercions through the operations in `at h ⊢`. Take the linear combination `h`.
-/
theorem binomSeries_ode (z : K) :
    (1 + PowerSeries.X) * PowerSeries.derivative K (binomSeries z) = z • binomSeries z := by
  ext n
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_derivative, PowerSeries.coeff_smul]
  cases n with
  | zero =>
    have h := binom_succ z 0
    simp only [binomSeries, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, smul_eq_mul]
    push_cast at h ⊢
    linear_combination h
  | succ n =>
    have h := binom_succ z (n + 1)
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp only [binomSeries, PowerSeries.coeff_mk, smul_eq_mul]
    push_cast at h ⊢
    linear_combination h

/- English proof (translation)
Establish `h` using `IntegralMvPolynomialLemmas.coeff_subst_congr (g := binomSeries z) (h := PowerSeries.C (1 : K)) hg 0 (fun k hk => by`. Establish `: k = 0` using `by simpa using hk`. Substitute `this` using the available equality. Simplify using `[binomSeries, binom_zero])`. Rewrite `h` using `[PowerSeries.subst_C]`.

Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_subst_binomSeries (z : K) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst g (binomSeries z)) = 1 := by
  have h := IntegralMvPolynomialLemmas.coeff_subst_congr (g := binomSeries z) (h := PowerSeries.C (1 : K)) hg 0
    (fun k hk => by
      have : k = 0 := by simpa using hk
      subst this
      simp [binomSeries, binom_zero])
  rw [PowerSeries.subst_C] at h
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp

/- English proof (translation)
Establish `hg : MvPowerSeries.constantCoeff (mvExp f - 1) = 0`. Rewrite using `[map_sub, constantCoeff_mvExp hf, map_one, sub_self]`. Establish `hs : PowerSeries.HasSubst (mvExp f - 1)` using `hasSubst_of_cc hg`. Establish `hzf : MvPowerSeries.constantCoeff (z • f) = 0`. Rewrite using `[MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]`.

Establish `hnzf : MvPowerSeries.constantCoeff (-(z • f)) = 0` using `by rw [map_neg, hzf, neg_zero]`. Use `set B := PowerSeries.subst (mvExp f - 1) (binomSeries z) with hB`. Establish `hode : mvExp f * PowerSeries.subst (mvExp f - 1) (PowerSeries.derivative K (binomSeries z)) = z • B`. Establish `h` using `congrArg (PowerSeries.subst (mvExp f - 1)) (binomSeries_ode z)`. Rewrite `h` using `[PowerSeries.subst_mul hs, PowerSeries.subst_add hs, PowerSeries.subst_X hs, PowerSeries.subst_smul hs, ← PowerSeries.coe_substAlgHom hs, map_one, PowerSeries.coe_substAlgHom hs]`.

Rewrite using `[hB, ← h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : ∀ i, MvPowerSeries.pderiv K i B = MvPowerSeries.C z * MvPowerSeries.pderiv K i f * B`. Introduce `i`. Apply `(isUnit_mvExp hf).mul_left_cancel` to reduce the goal to its premises.

Rewrite using `[hB, IntegralMvPolynomialLemmas.pderiv_subst _ hg, ← mul_assoc, hode, map_sub, MvPowerSeries.pderiv_one, sub_zero, pderiv_mvExp hf, MvPowerSeries.smul_eq_C_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : B * mvExp (-(z • f)) = 1`. Use `MvPowerSeries.pderiv.ext (fun i => ?_) ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, pderiv_mvExp hnzf, hd, map_neg, MvPowerSeries.smul_eq_C_mul, Derivation.leibniz, MvPowerSeries.pderiv_C, MvPowerSeries.pderiv_one]`.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, constantCoeff_mvExp hnzf, hB, constantCoeff_subst_binomSeries z hg, map_one, mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem subst_binomSeries_eq_mvExp (z : K) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (mvExp f - 1) (binomSeries z) = mvExp (z • f) := by
  have hg : MvPowerSeries.constantCoeff (mvExp f - 1) = 0 := by
    rw [map_sub, constantCoeff_mvExp hf, map_one, sub_self]
  have hs : PowerSeries.HasSubst (mvExp f - 1) := hasSubst_of_cc hg
  have hzf : MvPowerSeries.constantCoeff (z • f) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
  have hnzf : MvPowerSeries.constantCoeff (-(z • f)) = 0 := by rw [map_neg, hzf, neg_zero]
  set B := PowerSeries.subst (mvExp f - 1) (binomSeries z) with hB
  have hode : mvExp f * PowerSeries.subst (mvExp f - 1) (PowerSeries.derivative K (binomSeries z))
      = z • B := by
    have h := congrArg (PowerSeries.subst (mvExp f - 1)) (binomSeries_ode z)
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs, PowerSeries.subst_X hs,
      PowerSeries.subst_smul hs, ← PowerSeries.coe_substAlgHom hs, map_one,
      PowerSeries.coe_substAlgHom hs] at h
    rw [hB, ← h]
    ring
  have hd : ∀ i, MvPowerSeries.pderiv K i B =
      MvPowerSeries.C z * MvPowerSeries.pderiv K i f * B := by
    intro i
    apply (isUnit_mvExp hf).mul_left_cancel
    rw [hB, IntegralMvPolynomialLemmas.pderiv_subst _ hg, ← mul_assoc, hode, map_sub, MvPowerSeries.pderiv_one, sub_zero,
      pderiv_mvExp hf, MvPowerSeries.smul_eq_C_mul]
    ring
  have key : B * mvExp (-(z • f)) = 1 := by
    refine MvPowerSeries.pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, pderiv_mvExp hnzf, hd, map_neg, MvPowerSeries.smul_eq_C_mul,
        Derivation.leibniz, MvPowerSeries.pderiv_C, MvPowerSeries.pderiv_one]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, constantCoeff_mvExp hnzf, hB, constantCoeff_subst_binomSeries z hg, map_one,
        mul_one]
  calc B = B * (mvExp (-(z • f)) * mvExp (z • f)) := by rw [mvExp_neg hzf, mul_one]
    _ = mvExp (z • f) := by rw [← mul_assoc, key, one_mul]

/- English proof (translation)
Introduce `K _ _ R σ z hz f hf`. Use `⟨by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf.1, mul_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[← subst_binomSeries_eq_mvExp z hf.1]`. Use `IntegralMvPolynomialLemmas.intMv_subst (fun n => ?_) ⟨?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[binomSeries, PowerSeries.coeff_mk]`.

Conclude with `hz n`. Rewrite using `[map_sub, constantCoeff_mvExp hf.1, map_one, sub_self]`. Rewrite using `[map_sub]`. Conclude with `R.sub_mem (hf.2 n) (IntegralMvPolynomialLemmas.intMv_one n)`.
-/
theorem expIntegralBinomial' : LGBinom := by
  intro K _ _ R σ z hz f hf
  refine ⟨by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf.1, mul_zero], ?_⟩
  rw [← subst_binomSeries_eq_mvExp z hf.1]
  refine IntegralMvPolynomialLemmas.intMv_subst (fun n => ?_) ⟨?_, fun n => ?_⟩
  · rw [binomSeries, PowerSeries.coeff_mk]
    exact hz n
  · rw [map_sub, constantCoeff_mvExp hf.1, map_one, sub_self]
  · rw [map_sub]
    exact R.sub_mem (hf.2 n) (IntegralMvPolynomialLemmas.intMv_one n)

/- English proof (translation)
Introduce `K _ _ R n k`. Proceed by induction on `k generalizing n with`. Consider the case `zero => rw [binom_zero]`. Conclude with `R.one_mem`. Consider the case `succ k ih`.

Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => rw [Int.cast_zero, binom_zero_succ]`. Conclude with `R.zero_mem`. Consider the case `succ m hm`. Establish `h` using `binom_pascal ((m : ℤ) : K) k`.

Establish `e : (((m : ℤ) + 1 : ℤ) : K) = ((m : ℤ) : K) + 1` using `by push_cast; ring`. Rewrite using `[e, h]`. Conclude with `R.add_mem hm (ih _)`. Consider the case `pred m hm`. Establish `h` using `binom_pascal (((-(m : ℤ) - 1 : ℤ)) : K) k`.

Establish `e : (((-(m : ℤ) - 1 : ℤ)) : K) + 1 = ((-(m : ℤ) : ℤ) : K)` using `by push_cast; ring`. Rewrite `h` using `[e]`. Establish `h2 : binom (((-(m : ℤ) - 1 : ℤ)) : K) (k + 1) = binom ((-(m : ℤ) : ℤ) : K) (k + 1) - binom (((-(m : ℤ) - 1 : ℤ)) : K) k`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2]`. Conclude with `R.sub_mem hm (ih _)`.
-/
theorem intBinomialScalar' : IntBinomScalar := by
  intro K _ _ R n k
  induction k generalizing n with
  | zero => rw [binom_zero]; exact R.one_mem
  | succ k ih =>
    induction n using Int.induction_on with
    | zero => rw [Int.cast_zero, binom_zero_succ]; exact R.zero_mem
    | succ m hm =>
      have h := binom_pascal ((m : ℤ) : K) k
      have e : (((m : ℤ) + 1 : ℤ) : K) = ((m : ℤ) : K) + 1 := by push_cast; ring
      rw [e, h]
      exact R.add_mem hm (ih _)
    | pred m hm =>
      have h := binom_pascal (((-(m : ℤ) - 1 : ℤ)) : K) k
      have e : (((-(m : ℤ) - 1 : ℤ)) : K) + 1 = ((-(m : ℤ) : ℤ) : K) := by push_cast; ring
      rw [e] at h
      have h2 : binom (((-(m : ℤ) - 1 : ℤ)) : K) (k + 1) =
          binom ((-(m : ℤ) : ℤ) : K) (k + 1) - binom (((-(m : ℤ) - 1 : ℤ)) : K) k := by
        rw [h]; ring
      rw [h2]
      exact R.sub_mem hm (ih _)

end Formalism.L2.Th1.C
