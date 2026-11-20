import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassA
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassB

namespace KStar.IdealCounting

open NumberField

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)` using `by positivity`. Establish `h1 : (2 : ℝ) ≤ (1 + (((n + 1 : ℕ) : ℝ))⁻¹) ^ (n + 1)`.

Use `one_add_mul_le_pow (a := (((n + 1 : ℕ) : ℝ))⁻¹) (le_trans (by norm_num) (inv_nonneg.mpr hp.le)) (n + 1)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hp.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 2 * ((n + 1 : ℕ) : ℝ) ^ (n + 1) ≤ ((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1)`. Establish `e : ((n + 1 + 1 : ℕ) : ℝ) = (1 + (((n + 1 : ℕ) : ℝ))⁻¹) * ((n + 1 : ℕ) : ℝ)`.

Rewrite using `[add_mul, inv_mul_cancel₀ hp.ne']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, mul_pow]`. Use `gcongr`.

Establish `hq : (0 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.factorial_succ (n + 1), Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ((n + 1 + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by gcongr`.

Use `_ ≤ ((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1) := by gcongr`. Use `_ = _ := by ring`.
-/
private theorem classC_fact (n : ℕ) :
    (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h1 : (2 : ℝ) ≤ (1 + (((n + 1 : ℕ) : ℝ))⁻¹) ^ (n + 1) := by
      have := one_add_mul_le_pow (a := (((n + 1 : ℕ) : ℝ))⁻¹)
        (le_trans (by norm_num) (inv_nonneg.mpr hp.le)) (n + 1)
      rw [mul_inv_cancel₀ hp.ne'] at this
      linarith
    have h2 : 2 * ((n + 1 : ℕ) : ℝ) ^ (n + 1) ≤ ((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1) := by
      have e : ((n + 1 + 1 : ℕ) : ℝ) = (1 + (((n + 1 : ℕ) : ℝ))⁻¹) * ((n + 1 : ℕ) : ℝ) := by
        rw [add_mul, inv_mul_cancel₀ hp.ne']; push_cast; ring
      rw [e, mul_pow]
      gcongr
    have hq : (0 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by positivity
    calc (2 : ℝ) ^ (n + 1) * ((n + 1 + 1).factorial : ℝ)
        = ((n + 1 + 1 : ℕ) : ℝ) * (2 * (2 ^ n * ((n + 1).factorial : ℝ))) := by
          rw [Nat.factorial_succ (n + 1), Nat.cast_mul]; ring
      _ ≤ ((n + 1 + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by gcongr
      _ ≤ ((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1) := by gcongr
      _ = _ := by ring

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Establish `h1 : (4 / Real.pi) ≤ 2`. Rewrite using `[div_le_iff₀ Real.pi_pos]`. Combine the linear relations using `[Real.pi_gt_three]`. Establish `h2 : (4 / Real.pi) ^ r ≤ (2 : ℝ) ^ m` using `(pow_le_pow_left₀ (by positivity) h1 r).trans (pow_le_pow_right₀ (by norm_num) (by omega))`.

Rewrite using `[← mul_div_assoc, div_le_one (by positivity)]`. Use `le_trans ?_ (classC_fact m)` and prove the remaining obligations. Use `gcongr`.
-/
private theorem classC_const (n r : ℕ) (hn : 0 < n) (hr : 2 * r ≤ n) :
    (4 / Real.pi) ^ r * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : (4 / Real.pi) ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
  have h2 : (4 / Real.pi) ^ r ≤ (2 : ℝ) ^ m :=
    (pow_le_pow_left₀ (by positivity) h1 r).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  rw [← mul_div_assoc, div_le_one (by positivity)]
  refine le_trans ?_ (classC_fact m)
  gcongr

/- English proof (translation)
Establish `hfin : Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊√|(discr K : ℝ)|⌋₊}` using `(Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊√|(discr K : ℝ)|⌋₊).subset fun _ h => h.2`. Rewrite using `[classNumber, ← Nat.card_eq_fintype_card]`. Use `Nat.card_le_card_of_surjective (fun I => ClassGroup.mk0 (⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩ : nonZeroDivisors (Ideal (𝓞 K)))) ?_` and prove the remaining obligations. Introduce `C`. Take `⟨I, hI, hn⟩` from `exists_ideal_in_class_of_norm_le C`.

Use `⟨⟨I.1, nonZeroDivisors.coe_ne_zero I, ?_⟩, hI⟩` and prove the remaining obligations. Apply `Nat.le_floor` to reduce the goal to its premises. Use `hn.trans ?_` and prove the remaining obligations. Establish `hc` using `classC_const (Module.finrank ℚ K) (InfinitePlace.nrComplexPlaces K) Module.finrank_pos (by have := InfinitePlace.card_add_two_mul_card_eq_rank K; omega)`. Rewrite using `[← mul_assoc]`.

Simplify using `using mul_le_of_le_one_left (Real.sqrt_nonneg |(discr K : ℝ)|) hc`.
-/
theorem classNumber_le_card_ideals (K : Type*) [Field K] [NumberField K] :
    classNumber K ≤
      Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊√|(discr K : ℝ)|⌋₊} := by
  classical
  have hfin : Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊√|(discr K : ℝ)|⌋₊} :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊√|(discr K : ℝ)|⌋₊).subset fun _ h => h.2
  rw [classNumber, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_surjective
    (fun I => ClassGroup.mk0 (⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩ :
      nonZeroDivisors (Ideal (𝓞 K)))) ?_
  intro C
  obtain ⟨I, hI, hn⟩ := exists_ideal_in_class_of_norm_le C
  refine ⟨⟨I.1, nonZeroDivisors.coe_ne_zero I, ?_⟩, hI⟩
  apply Nat.le_floor
  refine hn.trans ?_
  have hc := classC_const (Module.finrank ℚ K) (InfinitePlace.nrComplexPlaces K)
    Module.finrank_pos (by have := InfinitePlace.card_add_two_mul_card_eq_rank K; omega)
  rw [← mul_assoc]
  simpa using mul_le_of_le_one_left (Real.sqrt_nonneg |(discr K : ℝ)|) hc

/- English proof (translation)
Establish `hd : (1 : ℝ) ≤ |(discr K : ℝ)|`. Conclude with `Int.one_le_abs (discr_ne_zero K)` after adjusting the coercions. Establish `h1` using `classNumber_le_card_ideals K`. Establish `hpos : (0 : ℝ) < classNumber K` using `Nat.cast_pos.mpr (classNumber_pos K)`. Generalize the expression as in `classNumber K = c at h1 hpos ⊢`.

Establish `h2` using `card_ideals_le_tuples K ⌊√|(discr K : ℝ)|⌋₊`. Take `⟨m, hm⟩ : ∃ m, Module.finrank ℚ K = m + 1` from `⟨Module.finrank ℚ K - 1, by have := Module.finrank_pos (R := ℚ) (M := K); omega⟩`. Rewrite `h2`, the goal using `[hm]`. Use `set s : ℝ := √|(discr K : ℝ)| with hs`. Establish `hs1 : 1 ≤ s` using `Real.one_le_sqrt.mpr hd`.

Establish `hM : 1 ≤ ⌊s⌋₊` using `Nat.le_floor (by simpa using hs1)`. Establish `h3` using `card_tuples_le m ⌊s⌋₊ hM`. Establish `hMs : ((⌊s⌋₊ : ℕ) : ℝ) ≤ s` using `Nat.floor_le (by linarith)`. Establish `hM' : (1 : ℝ) ≤ ((⌊s⌋₊ : ℕ) : ℝ)` using `by exact_mod_cast hM`. Establish `hlog : Real.log |(discr K : ℝ)| / 2 = Real.log s`.

Rewrite using `[hs, Real.log_sqrt (abs_nonneg _)]`. Rewrite using `[hlog]`. Establish `hl0 : 0 ≤ Real.log ((⌊s⌋₊ : ℕ) : ℝ)` using `Real.log_nonneg hM'`. Establish `hl1 : Real.log ((⌊s⌋₊ : ℕ) : ℝ) ≤ Real.log s` using `Real.log_le_log (by linarith) hMs`. Establish `h4 : (c : ℝ) ≤ s * (1 + Real.log s) ^ (m + 1)`.

Use `le_trans (Nat.cast_le.mpr (h1.trans h2)) (h3.trans ?_)` and prove the remaining obligations. Establish `: (1 + Real.log ((⌊s⌋₊ : ℕ) : ℝ)) ^ m ≤ (1 + Real.log s) ^ (m + 1)` using `(pow_le_pow_left₀ (by linarith) (by linarith) m).trans (pow_le_pow_right₀ (by linarith) (by omega))`. Use `gcongr`. Use `(Real.log_le_log hpos h4).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.log_mul (by linarith) (pow_ne_zero _ (by linarith)), Real.log_pow]`.
-/
theorem log_classNumber_le (K : Type*) [Field K] [NumberField K] :
    Real.log (classNumber K) ≤ Real.log |(discr K : ℝ)| / 2 +
      Module.finrank ℚ K * Real.log (1 + Real.log |(discr K : ℝ)| / 2) := by
  have hd : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have h1 := classNumber_le_card_ideals K
  have hpos : (0 : ℝ) < classNumber K := Nat.cast_pos.mpr (classNumber_pos K)
  generalize classNumber K = c at h1 hpos ⊢
  have h2 := card_ideals_le_tuples K ⌊√|(discr K : ℝ)|⌋₊
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank ℚ K = m + 1 :=
    ⟨Module.finrank ℚ K - 1, by have := Module.finrank_pos (R := ℚ) (M := K); omega⟩
  rw [hm] at h2 ⊢
  set s : ℝ := √|(discr K : ℝ)| with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hd
  have hM : 1 ≤ ⌊s⌋₊ := Nat.le_floor (by simpa using hs1)
  have h3 := card_tuples_le m ⌊s⌋₊ hM
  have hMs : ((⌊s⌋₊ : ℕ) : ℝ) ≤ s := Nat.floor_le (by linarith)
  have hM' : (1 : ℝ) ≤ ((⌊s⌋₊ : ℕ) : ℝ) := by exact_mod_cast hM
  have hlog : Real.log |(discr K : ℝ)| / 2 = Real.log s := by
    rw [hs, Real.log_sqrt (abs_nonneg _)]
  rw [hlog]
  have hl0 : 0 ≤ Real.log ((⌊s⌋₊ : ℕ) : ℝ) := Real.log_nonneg hM'
  have hl1 : Real.log ((⌊s⌋₊ : ℕ) : ℝ) ≤ Real.log s := Real.log_le_log (by linarith) hMs
  have h4 : (c : ℝ) ≤ s * (1 + Real.log s) ^ (m + 1) := by
    refine le_trans (Nat.cast_le.mpr (h1.trans h2)) (h3.trans ?_)
    have : (1 + Real.log ((⌊s⌋₊ : ℕ) : ℝ)) ^ m ≤ (1 + Real.log s) ^ (m + 1) :=
      (pow_le_pow_left₀ (by linarith) (by linarith) m).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    gcongr
  refine (Real.log_le_log hpos h4).trans (le_of_eq ?_)
  rw [Real.log_mul (by linarith) (pow_ne_zero _ (by linarith)), Real.log_pow]

end KStar.IdealCounting
