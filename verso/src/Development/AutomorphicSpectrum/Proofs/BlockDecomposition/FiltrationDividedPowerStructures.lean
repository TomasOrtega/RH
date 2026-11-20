import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturatedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerIdealTorsionFree
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

/- English proof (translation)
Take `⟨w, hw⟩` from `ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) hn hk`. Use `⟨algebraMap A.W A.Acr0 (A.sW w), ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun t => algebraMap A.W A.Acr0 (A.sW t)) hw`. Simplify using `using h`.
-/
theorem exists_natCast_mul_eq_l_pow {n k : ℕ} (hn : n ≠ 0) (hk : n.factorization l ≤ k) :
    ∃ w : A.Acr0, (n : A.Acr0) * w = (l : A.Acr0) ^ k := by
  obtain ⟨w, hw⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) hn hk
  refine ⟨algebraMap A.W A.Acr0 (A.sW w), ?_⟩
  have h := congrArg (fun t => algebraMap A.W A.Acr0 (A.sW t)) hw
  simpa using h

/- English proof (translation)
Take `⟨-, -, hf, -⟩` from `GlobalTheory.T.crystalline_filtration_multiplicative A`. Use `⟨(Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j), Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k * j, Nat.mul_pos (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hj), rfl⟩), ?_⟩` and prove the remaining obligations. Establish `hnz` using `A.acris_torsion_free (j.factorial ^ k) (pow_ne_zero k j.factorial_ne_zero)`. Use `(mul_cancel_left_mem_nonZeroDivisors hnz).1 ?_` and prove the remaining obligations. Establish `h1 : ((j.factorial ^ k : ℕ) : A.Acr0) * ((k.factorial : A.Acr0) * ((Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j))) = ((k * j).factorial : A.Acr0) * A.dxi0 (k * j)`.

Rewrite using `[← Nat.uniformBell_mul_eq k hj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, hf, pow_mul', ← hf j]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_divided_power_of_dividedXi {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) :
    ∃ y ∈ A.Fil0 1, (k.factorial : A.Acr0) * y = A.dxi0 j ^ k := by
  obtain ⟨-, -, hf, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  refine ⟨(Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j),
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k * j, Nat.mul_pos (Nat.pos_of_ne_zero hk)
      (Nat.pos_of_ne_zero hj), rfl⟩), ?_⟩
  have hnz := A.acris_torsion_free (j.factorial ^ k) (pow_ne_zero k j.factorial_ne_zero)
  refine (mul_cancel_left_mem_nonZeroDivisors hnz).1 ?_
  have h1 : ((j.factorial ^ k : ℕ) : A.Acr0) *
      ((k.factorial : A.Acr0) * ((Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j))) =
      ((k * j).factorial : A.Acr0) * A.dxi0 (k * j) := by
    rw [← Nat.uniformBell_mul_eq k hj]
    push_cast
    ring
  rw [h1, hf, pow_mul', ← hf j]
  push_cast
  ring

/- English proof (translation)
Establish `hv : k.factorial.factorization l ≤ k - 1`. Rewrite using `[Nat.factorization_def _ Fact.out]`. Establish `h` using `sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := l) hk`. Establish `h2 : 1 ≤ l - 1` using `Nat.le_sub_of_add_le (Fact.out : l.Prime).two_le`. Establish `h3 : padicValNat l k.factorial ≤ (l - 1) * padicValNat l k.factorial` using `Nat.le_mul_of_pos_left _ h2`.

Use linear arithmetic over natural numbers and integers. Take `⟨w, hw⟩` from `exists_natCast_mul_eq_l_pow A k.factorial_ne_zero hv`. Use `⟨(l : A.Acr0) * w, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hk`. Rewrite using `[mul_left_comm, hw]`.

Simplify using `only [Nat.succ_eq_add_one, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_l_pow {k : ℕ} (hk : k ≠ 0) :
    ∃ y ∈ Ideal.span {(l : A.Acr0)}, (k.factorial : A.Acr0) * y = (l : A.Acr0) ^ k := by
  have hv : k.factorial.factorization l ≤ k - 1 := by
    rw [Nat.factorization_def _ Fact.out]
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := l) hk
    have h2 : 1 ≤ l - 1 := Nat.le_sub_of_add_le (Fact.out : l.Prime).two_le
    have h3 : padicValNat l k.factorial ≤ (l - 1) * padicValNat l k.factorial :=
      Nat.le_mul_of_pos_left _ h2
    omega
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_l_pow A k.factorial_ne_zero hv
  refine ⟨(l : A.Acr0) * w, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [mul_left_comm, hw]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem filtration_one_eq_span_dividedXi : A.Fil0 1 = Ideal.span {z | ∃ k, 1 ≤ k ∧ z = A.dxi0 k} := rfl

/- English proof (translation)
Rewrite using `[Ideal.span_union]`. Both sides reduce to the same expression.
-/
theorem pFil0_eq : A.PFil0 = Ideal.span ({(l : A.Acr0)} ∪ {z | ∃ k, 1 ≤ k ∧ z = A.dxi0 k}) := by
  rw [Ideal.span_union]
  rfl

/- English proof (translation)
Rewrite using `[filtration_one_eq_span_dividedXi]`. Use `GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, hj, rfl⟩ k hk`. Conclude with `exists_divided_power_of_dividedXi A (by omega) hk`.
-/
theorem filtration_one_has_divided_powers : R.PdI (A.Fil0 1) := by
  rw [filtration_one_eq_span_dividedXi]
  refine GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_
  rintro _ ⟨j, hj, rfl⟩ k hk
  exact exists_divided_power_of_dividedXi A (by omega) hk

/- English proof (translation)
Rewrite using `[pFil0_eq]`. Use `GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_` and prove the remaining obligations. Rewrite using `[← pFil0_eq]`. Introduce and unpack `x (rfl | ⟨j, hj, rfl⟩) k hk`. Take `⟨y, hy, e⟩` from `exists_l_pow A hk`.

Conclude with `⟨y, (le_sup_left : _ ≤ A.PFil0) hy, e⟩`. Take `⟨y, hy, e⟩` from `exists_divided_power_of_dividedXi A (by omega : j ≠ 0) hk`. Conclude with `⟨y, (le_sup_right : _ ≤ A.PFil0) hy, e⟩`.
-/
theorem pdI_pFil0 : R.PdI A.PFil0 := by
  rw [pFil0_eq]
  refine GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_
  rw [← pFil0_eq]
  rintro x (rfl | ⟨j, hj, rfl⟩) k hk
  · obtain ⟨y, hy, e⟩ := exists_l_pow A hk
    exact ⟨y, (le_sup_left : _ ≤ A.PFil0) hy, e⟩
  · obtain ⟨y, hy, e⟩ := exists_divided_power_of_dividedXi A (by omega : j ≠ 0) hk
    exact ⟨y, (le_sup_right : _ ≤ A.PFil0) hy, e⟩

/- English proof (translation)
Take `⟨h0, -, -, hm, -⟩` from `GlobalTheory.T.crystalline_filtration_multiplicative A`. Proceed by induction on `k with`. Consider the case `zero => rw [h0]`. Conclude with `Submodule.mem_top`. Consider the case `succ k ih => rw [pow_succ]`.

Conclude with `hm k 1 (Ideal.mul_mem_mul ih hx)`.
-/
theorem pow_mem_filtration_of_mem_one {x : A.Acr0} (hx : x ∈ A.Fil0 1) (k : ℕ) : x ^ k ∈ A.Fil0 k := by
  obtain ⟨h0, -, -, hm, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  induction k with
  | zero => rw [h0]; exact Submodule.mem_top
  | succ k ih => rw [pow_succ]; exact hm k 1 (Ideal.mul_mem_mul ih hx)

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simpa using h`. Consider the case `succ N ih`. Use `ih (GlobalTheory.T.crystalline_filtration_saturated A r _ ?_)` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← pow_succ']`.

Conclude with `h`.
-/
theorem mem_filtration_of_prime_pow_mul_mem (r N : ℕ) (z : A.Acr0) (h : (l : A.Acr0) ^ N * z ∈ A.Fil0 r) :
    z ∈ A.Fil0 r := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih (GlobalTheory.T.crystalline_filtration_saturated A r _ ?_)
    rw [← mul_assoc, ← pow_succ']
    exact h

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_natCast_mul_eq_l_pow A k.factorial_ne_zero le_rfl`. Use `mem_filtration_of_prime_pow_mul_mem A k (k.factorial.factorization l) y ?_` and prove the remaining obligations. Rewrite using `[← hw, mul_right_comm, e, mul_comm]`. Conclude with `Ideal.mul_mem_left _ _ (pow_mem_filtration_of_mem_one A hx k)`.
-/
theorem mem_filtration_of_factorial_mul_eq_pow {x : A.Acr0} (hx : x ∈ A.Fil0 1) (k : ℕ) (y : A.Acr0)
    (e : (k.factorial : A.Acr0) * y = x ^ k) : y ∈ A.Fil0 k := by
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_l_pow A k.factorial_ne_zero le_rfl
  refine mem_filtration_of_prime_pow_mul_mem A k (k.factorial.factorization l) y ?_
  rw [← hw, mul_right_comm, e, mul_comm]
  exact Ideal.mul_mem_left _ _ (pow_mem_filtration_of_mem_one A hx k)

/- English proof (translation)
Introduce `A` and use `⟨filtration_one_has_divided_powers A, pdI_pFil0 A, fun _ hx k y e => mem_filtration_of_factorial_mul_eq_pow A hx k y e⟩`.
-/
theorem pdI_main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧
    ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k :=
  fun A => ⟨filtration_one_has_divided_powers A, pdI_pFil0 A, fun _ hx k y e => mem_filtration_of_factorial_mul_eq_pow A hx k y e⟩

end GlobalTheory.CompanionTheory.PerfFil
