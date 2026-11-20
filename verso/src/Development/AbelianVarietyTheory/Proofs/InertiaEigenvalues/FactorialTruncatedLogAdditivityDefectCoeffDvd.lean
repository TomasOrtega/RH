import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect

open GlobalTheory.LogU MvPolynomial Finset

namespace GlobalTheory.LogUIntg

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h0` using `congrArg (fun f => f 0) h`. Establish `h1` using `congrArg (fun f => f 1) h`. Simplify using `at h0 h1`.

Conclude with `⟨h0, h1⟩`. Introduce and unpack `⟨rfl, rfl⟩`. Both sides reduce to the same expression.
-/
lemma single_add_single_eq_iff {i j i' j' : ℕ} :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j = Finsupp.single 0 i' + Finsupp.single 1 j') ↔
      (i = i' ∧ j = j') := by
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

/- English proof (translation)
Rewrite using `[coeff_monomial]`. Simplify using `only [single_add_single_eq_iff]`.
-/
lemma coeff_monomial_two (i j p q : ℕ) (c : ℤ) :
    coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        (monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c) =
      if p = i ∧ q = j then c else 0 := by
  rw [coeff_monomial]
  simp only [single_add_single_eq_iff]

/- English proof (translation)
Rewrite using `[X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul]`. Simplify using the standard rewrite rules.
-/
lemma monomial_two_eq (p q : ℕ) (c : ℤ) :
    monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c = C c * X 0 ^ p * X 1 ^ q := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul]
  simp

/- English proof (translation)
Establish `e1` using `Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s a)`. Rewrite `e1` using `[Nat.add_sub_cancel_left]`. Establish `e2` using `Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s (K - s - a))`. Rewrite `e2` using `[Nat.add_sub_cancel_left]`. Establish `e3` using `Nat.choose_mul_factorial_mul_factorial ha`.

Establish `e4` using `Nat.choose_mul_factorial_mul_factorial hs`. Establish `e5 : n.factorial / K * K.factorial = n.factorial * (K - 1).factorial`. Rewrite using `[← Nat.mul_factorial_pred (by omega : K ≠ 0), ← mul_assoc, Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hKn)]`. Rewrite using `[← e1, ← e2]`. Establish `key : (s + a).choose s * s.factorial * a.factorial * ((s + (K - s - a)).choose s * s.factorial * (K - s - a).factorial) * (n.factorial / K * (K.choose s * (K - s).choose a)) = n.factorial * ((K - 1).factorial * ((s + a).choose s * (s + (K - s - a)).choose s * s.factorial))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key]`. Conclude with `mul_dvd_mul (dvd_refl _) (dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial (by omega)) _)`.
-/
lemma factorial_dvd_term (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s)
    (hn : n ≤ (s + a) + (s + (K - s - a))) :
    n.factorial * ((n - 1) / 2).factorial ∣
      (s + a).factorial * (s + (K - s - a)).factorial *
        (n.factorial / K * (K.choose s * (K - s).choose a)) := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s a)
  rw [Nat.add_sub_cancel_left] at e1
  have e2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s (K - s - a))
  rw [Nat.add_sub_cancel_left] at e2
  have e3 := Nat.choose_mul_factorial_mul_factorial ha
  have e4 := Nat.choose_mul_factorial_mul_factorial hs
  have e5 : n.factorial / K * K.factorial = n.factorial * (K - 1).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : K ≠ 0), ← mul_assoc,
      Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hKn)]
  rw [← e1, ← e2]
  have key : (s + a).choose s * s.factorial * a.factorial *
      ((s + (K - s - a)).choose s * s.factorial * (K - s - a).factorial) *
        (n.factorial / K * (K.choose s * (K - s).choose a)) =
      n.factorial * ((K - 1).factorial * ((s + a).choose s * (s + (K - s - a)).choose s * s.factorial)) := by
    calc _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          ((K.choose s * s.factorial * ((K - s).choose a * a.factorial * (K - s - a).factorial)) *
            (n.factorial / K)) := by ring
      _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          (n.factorial / K * K.factorial) := by rw [e3, e4]; ring
      _ = _ := by rw [e5]; ring
  rw [key]
  exact mul_dvd_mul (dvd_refl _)
    (dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial (by omega)) _)

def Good (n : ℕ) (f : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∀ i j : ℕ, n ≤ i + j → ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) ∣
    ((i.factorial * j.factorial : ℕ) : ℤ) * coeff (Finsupp.single 0 i + Finsupp.single 1 j) f

/- English proof (translation)
Introduce `i j h`. Rewrite using `[coeff_sub, mul_sub]`. Conclude with `dvd_sub (hf i j h) (hg i j h)`.
-/
lemma good_sub {n : ℕ} {f g : MvPolynomial (Fin 2) ℤ} (hf : Good n f) (hg : Good n g) :
    Good n (f - g) := by
  intro i j h
  rw [coeff_sub, mul_sub]
  exact dvd_sub (hf i j h) (hg i j h)

/- English proof (translation)
Introduce `i j h`. Rewrite using `[coeff_sum, Finset.mul_sum]`. Conclude with `Finset.dvd_sum fun x hx => hf x hx i j h`.
-/
lemma good_sum {n : ℕ} {ι : Type} (t : Finset ι) (f : ι → MvPolynomial (Fin 2) ℤ)
    (hf : ∀ x ∈ t, Good n (f x)) : Good n (∑ x ∈ t, f x) := by
  intro i j h
  rw [coeff_sum, Finset.mul_sum]
  exact Finset.dvd_sum fun x hx => hf x hx i j h

/- English proof (translation)
Introduce `i j h`. Rewrite using `[coeff_C_mul, mul_left_comm]`. Conclude with `Dvd.dvd.mul_left (hf i j h) c`.
-/
lemma good_C_mul {n : ℕ} (c : ℤ) {f : MvPolynomial (Fin 2) ℤ} (hf : Good n f) :
    Good n (C c * f) := by
  intro i j h
  rw [coeff_C_mul, mul_left_comm]
  exact Dvd.dvd.mul_left (hf i j h) c

/- English proof (translation)
Introduce `i j h`. Rewrite using `[coeff_monomial_two]`. Use `split_ifs with hij`. Take `⟨rfl, rfl⟩` from `hij`. Rewrite using `[← Nat.cast_mul]`.

Conclude with `Int.natCast_dvd_natCast.mpr (factorial_dvd_term n K s a hK1 hKn hs ha h)`. Simplify using the standard rewrite rules.
-/
lemma good_atom (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s) :
    Good n (monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
      ((n.factorial / K * (K.choose s * (K - s).choose a) : ℕ) : ℤ)) := by
  intro i j h
  rw [coeff_monomial_two]
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rw [← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.mpr (factorial_dvd_term n K s a hK1 hKn hs ha h)
  · simp

/- English proof (translation)
Rewrite using `[show (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = X 0 * X 1 + (X 0 + X 1) by ring, add_pow, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[add_pow]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[monomial_two_eq]`. Simplify using `only [Nat.cast_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma C_mul_pow_u (m K : ℕ) :
    C (m : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K =
      ∑ s ∈ range (K + 1), ∑ a ∈ range (K - s + 1),
        monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
          ((m * (K.choose s * (K - s).choose a) : ℕ) : ℤ) := by
  rw [show (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = X 0 * X 1 + (X 0 + X 1) by ring,
    add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [monomial_two_eq]
  simp only [Nat.cast_mul, map_mul, map_natCast]
  ring

/- English proof (translation)
Rewrite using `[C_mul_pow_u]`. Use `good_sum _ _ fun s hs => good_sum _ _ fun a ha => ?_` and prove the remaining obligations. Rewrite `hs`, `ha` using `[Finset.mem_range]`. Conclude with `good_atom n K s a hK1 hKn (by omega) (by omega)`.
-/
lemma good_C_mul_pow_u (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  rw [C_mul_pow_u]
  refine good_sum _ _ fun s hs => good_sum _ _ fun a ha => ?_
  rw [Finset.mem_range] at hs ha
  exact good_atom n K s a hK1 hKn (by omega) (by omega)

/- English proof (translation)
Establish `h` using `good_atom n K 0 K hK1 hKn (by omega) (by omega)`. Rewrite `h` using `[monomial_two_eq]`. Simplify using `using h`.
-/
lemma logPolynomialDefectDivisible_C_mul_X_zero_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 K hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

/- English proof (translation)
Establish `h` using `good_atom n K 0 0 hK1 hKn (by omega) (by omega)`. Rewrite `h` using `[monomial_two_eq]`. Simplify using `using h`.
-/
lemma logPolynomialDefectDivisible_C_mul_X_one_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 0 hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

/- English proof (translation)
Unfold `truncLogF`. Use `good_sum _ _ fun k hk => ?_` and prove the remaining obligations. Rewrite `hk` using `[Finset.mem_range]`. Establish `e : ((-1 : MvPolynomial (Fin 2) ℤ) ^ k * ((n.factorial / (k + 1) : ℕ) : MvPolynomial (Fin 2) ℤ) * u ^ (k + 1)) = C ((-1) ^ k) * (C ((n.factorial / (k + 1) : ℕ) : ℤ) * u ^ (k + 1))`. Simplify using `only [map_pow, map_neg, map_one, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `good_C_mul _ (hu (k + 1) (by omega) (by omega))`.
-/
lemma good_truncLogF (n : ℕ) (u : MvPolynomial (Fin 2) ℤ)
    (hu : ∀ K, 1 ≤ K → K ≤ n → Good n (C ((n.factorial / K : ℕ) : ℤ) * u ^ K)) :
    Good n (truncLogF n u) := by
  unfold truncLogF
  refine good_sum _ _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  have e : ((-1 : MvPolynomial (Fin 2) ℤ) ^ k * ((n.factorial / (k + 1) : ℕ) : MvPolynomial (Fin 2) ℤ) *
      u ^ (k + 1)) = C ((-1) ^ k) * (C ((n.factorial / (k + 1) : ℕ) : ℤ) * u ^ (k + 1)) := by
    simp only [map_pow, map_neg, map_one, map_natCast]; ring
  rw [e]
  exact good_C_mul _ (hu (k + 1) (by omega) (by omega))

/- English proof (translation)
Unfold `logDefect`. Use `good_sub (good_sub ?_ ?_) ?_` and prove the remaining obligations. Conclude with `good_truncLogF n _ fun K h1 h2 => good_C_mul_pow_u n K h1 h2`. Conclude with `good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_zero_pow n K h1 h2`. Conclude with `good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_one_pow n K h1 h2`.
-/
theorem good_logDefect (n : ℕ) : Good n (logDefect n) := by
  unfold logDefect
  refine good_sub (good_sub ?_ ?_) ?_
  · exact good_truncLogF n _ fun K h1 h2 => good_C_mul_pow_u n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_zero_pow n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_one_pow n K h1 h2

/- English proof (translation)
Introduce `n i j h`. Conclude with `good_logDefect n i j h`.
-/
theorem logDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ,
    ((i.factorial * j.factorial : ℕ) : ℤ) *
        MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 j) (GlobalTheory.LogU.logDefect n) =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  intro n i j h
  exact good_logDefect n i j h

end GlobalTheory.LogUIntg
