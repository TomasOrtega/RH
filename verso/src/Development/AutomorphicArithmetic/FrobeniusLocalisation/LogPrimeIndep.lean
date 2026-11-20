import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Rewrite using `[Nat.factorization_prod (fun l hl => pow_ne_zero _ (hS l hl).ne_zero), Finsupp.finset_sum_apply, Finset.sum_eq_single p]`. Rewrite using `[(hS p hp).factorization_pow]`. Simplify using the standard rewrite rules. Introduce `l hl hne`. Rewrite using `[(hS l hl).factorization_pow]`.

Simplify using `[Finsupp.single_apply, hne]`. Introduce `h`. Conclude with `absurd hp h`.
-/
private theorem UpperTheory.HF.log_prime_indep_fact (S : Finset ℕ) (u : ℕ → ℕ) (hS : ∀ l ∈ S, l.Prime)
    (p : ℕ) (hp : p ∈ S) : (∏ l ∈ S, l ^ u l).factorization p = u p := by
  rw [Nat.factorization_prod (fun l hl => pow_ne_zero _ (hS l hl).ne_zero), Finsupp.finset_sum_apply,
    Finset.sum_eq_single p]
  · rw [(hS p hp).factorization_pow]; simp
  · intro l hl hne
    rw [(hS l hl).factorization_pow]; simp [Finsupp.single_apply, hne]
  · intro h; exact absurd hp h

/- English proof (translation)
Establish `key : ∀ w : ℕ → ℕ, ∑ l ∈ S, (w l : ℝ) * Real.log l = Real.log ((∏ l ∈ S, l ^ w l : ℕ) : ℝ)`. Introduce `w`. Use `push_cast`. Rewrite using `[Real.log_prod (fun l hl => pow_ne_zero _ (by exact_mod_cast (hS l hl).ne_zero))]`. Conclude with `Finset.sum_congr rfl (fun l _ => (Real.log_pow _ _).symm)`.

Establish `pos : ∀ w : ℕ → ℕ, (0 : ℝ) < ((∏ l ∈ S, l ^ w l : ℕ) : ℝ)`. Introduce `w`. Conclude with `Finset.prod_pos (fun l hl => pow_pos (hS l hl).pos _)` after adjusting the coercions. Rewrite `h` using `[key u, key v]`. Establish `h2` using `Real.log_injOn_pos (Set.mem_Ioi.2 (pos u)) (Set.mem_Ioi.2 (pos v)) h`.

Establish `h3 : (∏ l ∈ S, l ^ u l) = ∏ l ∈ S, l ^ v l` using `by exact_mod_cast h2`. Introduce `p hp`. Rewrite using `[← UpperTheory.HF.log_prime_indep_fact S u hS p hp, ← UpperTheory.HF.log_prime_indep_fact S v hS p hp, h3]`.
-/
private theorem UpperTheory.HF.log_prime_indep_nat (S : Finset ℕ) (u v : ℕ → ℕ) (hS : ∀ l ∈ S, l.Prime)
    (h : ∑ l ∈ S, (u l : ℝ) * Real.log l = ∑ l ∈ S, (v l : ℝ) * Real.log l) :
    ∀ l ∈ S, u l = v l := by
  have key : ∀ w : ℕ → ℕ, ∑ l ∈ S, (w l : ℝ) * Real.log l
      = Real.log ((∏ l ∈ S, l ^ w l : ℕ) : ℝ) := by
    intro w
    push_cast
    rw [Real.log_prod (fun l hl => pow_ne_zero _ (by exact_mod_cast (hS l hl).ne_zero))]
    exact Finset.sum_congr rfl (fun l _ => (Real.log_pow _ _).symm)
  have pos : ∀ w : ℕ → ℕ, (0 : ℝ) < ((∏ l ∈ S, l ^ w l : ℕ) : ℝ) := by
    intro w
    exact_mod_cast Finset.prod_pos (fun l hl => pow_pos (hS l hl).pos _)
  rw [key u, key v] at h
  have h2 := Real.log_injOn_pos (Set.mem_Ioi.2 (pos u)) (Set.mem_Ioi.2 (pos v)) h
  have h3 : (∏ l ∈ S, l ^ u l) = ∏ l ∈ S, l ^ v l := by exact_mod_cast h2
  intro p hp
  rw [← UpperTheory.HF.log_prime_indep_fact S u hS p hp, ← UpperTheory.HF.log_prime_indep_fact S v hS p hp, h3]

/- English proof (translation)
Establish `h1` using `UpperTheory.HF.log_prime_indep_nat S (fun l => (m l).toNat) (fun l => (-m l).toNat) hS (by`. Rewrite using `[← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[← sub_mul]`. Use `congr 1`.

Establish `: (((m l).toNat : ℤ)) - ((-m l).toNat : ℤ) = m l` using `Int.toNat_sub_toNat_neg _`. Conclude with `this)` after adjusting the coercions. Introduce `l hl`. Use `h1 l hl` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem UpperTheory.HF.log_prime_indep_int (S : Finset ℕ) (m : ℕ → ℤ) (hS : ∀ l ∈ S, l.Prime)
    (h : ∑ l ∈ S, (m l : ℝ) * Real.log l = 0) : ∀ l ∈ S, m l = 0 := by
  have h1 := UpperTheory.HF.log_prime_indep_nat S (fun l => (m l).toNat) (fun l => (-m l).toNat) hS (by
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← sub_mul]
    congr 1
    have : (((m l).toNat : ℤ)) - ((-m l).toNat : ℤ) = m l := Int.toNat_sub_toNat_neg _
    exact_mod_cast this)
  intro l hl
  have := h1 l hl
  omega

/- English proof (translation)
Introduce `S a b hS h`. Use `set D : ℕ := ∏ l ∈ S, (a l - b l).den with hD`. Establish `hD0 : D ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun l _ => (a l - b l).den_nz)`. Establish `hex : ∀ l, ∃ z : ℤ, l ∈ S → (z : ℚ) = (a l - b l) * D`. Introduce `l`.

Distinguish the cases in `hl : l ∈ S`. Take `⟨k, hk⟩ : (a l - b l).den ∣ D` from `Finset.dvd_prod_of_mem (fun l => (a l - b l).den) hl`. Use `⟨(a l - b l).num * k, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Use `push_cast`.

Rewrite using `[← mul_assoc, Rat.mul_den_eq_num]`. Conclude with `⟨0, fun h => absurd h hl⟩`. Use `choose m hm using hex`. Establish `h0` using `UpperTheory.HF.log_prime_indep_int S m hS (by`. Establish `: ∑ l ∈ S, (m l : ℝ) * Real.log l = (∑ l ∈ S, (a l : ℝ) * Real.log l - ∑ l ∈ S, (b l : ℝ) * Real.log l) * D`.

Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun l hl => ?_)` and prove the remaining obligations. Establish `h1 : ((m l : ℚ) : ℝ) = (((a l - b l) * D : ℚ) : ℝ)` using `by rw [hm l hl]`. Move the coercions through the operations in `at h1`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, h, sub_self, zero_mul])`. Introduce `l hl`. Establish `h1` using `hm l hl`. Rewrite `h1` using `[h0 l hl]`.

Establish `hDq : (D : ℚ) ≠ 0` using `by exact_mod_cast hD0`. Establish `: a l - b l = 0`. Break down `mul_eq_zero.1 (by simpa using h1.symm : (a l - b l) * (D : ℚ) = 0) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hDq`.

Conclude with `sub_eq_zero.1 this`.
-/
theorem UpperTheory.HF.log_prime_indep :
    ∀ (S : Finset ℕ) (a b : ℕ → ℚ), (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (a l : ℝ) * Real.log l = ∑ l ∈ S, (b l : ℝ) * Real.log l → ∀ l ∈ S, a l = b l := by
  intro S a b hS h
  set D : ℕ := ∏ l ∈ S, (a l - b l).den with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun l _ => (a l - b l).den_nz)
  have hex : ∀ l, ∃ z : ℤ, l ∈ S → (z : ℚ) = (a l - b l) * D := by
    intro l
    by_cases hl : l ∈ S
    · obtain ⟨k, hk⟩ : (a l - b l).den ∣ D := Finset.dvd_prod_of_mem (fun l => (a l - b l).den) hl
      refine ⟨(a l - b l).num * k, fun _ => ?_⟩
      rw [hk]; push_cast
      rw [← mul_assoc, Rat.mul_den_eq_num]
    · exact ⟨0, fun h => absurd h hl⟩
  choose m hm using hex
  have h0 := UpperTheory.HF.log_prime_indep_int S m hS (by
    have : ∑ l ∈ S, (m l : ℝ) * Real.log l
        = (∑ l ∈ S, (a l : ℝ) * Real.log l - ∑ l ∈ S, (b l : ℝ) * Real.log l) * D := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have h1 : ((m l : ℚ) : ℝ) = (((a l - b l) * D : ℚ) : ℝ) := by rw [hm l hl]
      push_cast at h1
      rw [h1]; ring
    rw [this, h, sub_self, zero_mul])
  intro l hl
  have h1 := hm l hl
  rw [h0 l hl] at h1
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
  have : a l - b l = 0 := by
    rcases mul_eq_zero.1 (by simpa using h1.symm : (a l - b l) * (D : ℚ) = 0) with h | h
    · exact h
    · exact absurd h hDq
  exact sub_eq_zero.1 this
