import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {n : ℕ}

/- English proof (translation)
Establish `h : lamS S = ∑ k ∈ S, (Pi.single k 1 : Fin n → ℤ)`. Use function extensionality and compare the values at `x`. Simplify using `[lamS_apply, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[h]`. Simplify using `only [varL, monomial]`.

Rewrite using `[AddMonoidAlgebra.prod_single, Finset.prod_const_one]`.
-/
theorem prod_varL_eq_monomial (S : Finset (Fin n)) :
    ∏ k ∈ S, varL k = monomial (lamS S) := by
  have h : lamS S = ∑ k ∈ S, (Pi.single k 1 : Fin n → ℤ) := by
    funext x
    simp [lamS_apply, Finset.sum_apply, Pi.single_apply]
  rw [h]
  simp only [varL, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]

/- English proof (translation)
Establish `h0 : ∏ k : Fin n, (-varL k + varL i) = 0` using `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Rewrite `h0` using `[Finset.prod_add, Finset.sum_powerset]`. Rewrite using `[← h0, Finset.card_univ, Fintype.card_fin]`. Use `Finset.sum_congr rfl fun r hr => ?_` and prove the remaining obligations. Rewrite using `[esymmL, Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun S hS => ?_` and prove the remaining obligations. Establish `hc` using `(Finset.mem_powersetCard.1 hS).2`. Rewrite using `[Finset.prod_neg, hc, prod_varL_eq_monomial, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin, hc]`.
-/
theorem sum_esymmL_mul_pow (i : Fin n) :
    ∑ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r * varL i ^ (n - r) = 0 := by
  have h0 : ∏ k : Fin n, (-varL k + varL i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Finset.prod_add, Finset.sum_powerset] at h0
  rw [← h0, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [esymmL, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc := (Finset.mem_powersetCard.1 hS).2
  rw [Finset.prod_neg, hc, prod_varL_eq_monomial, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ, Fintype.card_fin, hc]

/- English proof (translation)
The claim follows from `altQuot_eq_of_mul (by simp)`.
-/
theorem altQuot_zero' : altQuot (0 : LaurentRing n) = 0 :=
  altQuot_eq_of_mul (by simp)

/- English proof (translation)
Use `set i₀ : Fin n := ⟨0, hn⟩`. Use `set P : LaurentRing n := monomial (Pi.single i₀ (j - (n : ℤ)) + staircase n) with hP`. Establish `hterm : ∀ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r * schur (Pi.single i₀ (j - (r : ℤ))) = altQuot ((-1) ^ r * esymmL n r * varL i₀ ^ (n - r) * P)`. Introduce `r hr`. Establish `hr' : r ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)`.

Establish `hsym : ∀ σ, permAct σ ((-1) ^ r * esymmL n r) = (-1) ^ r * esymmL n r`. Introduce `σ`. Rewrite using `[map_mul, map_pow, map_neg, map_one, permAct_esymmL]`. Rewrite using `[mul_assoc ((-1) ^ r * esymmL n r), altQuot_mul_of_symm hsym, schur]`. Use `congr 2`.

Rewrite using `[← monomial_single_natCast, hP, ← monomial_add, ← add_assoc, ← Pi.single_add]`. Use `congr 3`. Move the coercions through the operations in `[Nat.cast_sub hr']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl hterm, ← altQuot_sum, ← Finset.sum_mul, sum_esymmL_mul_pow, zero_mul, altQuot_zero']`.
-/
theorem sum_esymmL_mul_schur (hn : 0 < n) (j : ℤ) :
    ∑ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single (⟨0, hn⟩ : Fin n) (j - (r : ℤ))) = 0 := by
  set i₀ : Fin n := ⟨0, hn⟩
  set P : LaurentRing n := monomial (Pi.single i₀ (j - (n : ℤ)) + staircase n) with hP
  have hterm : ∀ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single i₀ (j - (r : ℤ))) =
      altQuot ((-1) ^ r * esymmL n r * varL i₀ ^ (n - r) * P) := by
    intro r hr
    have hr' : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hsym : ∀ σ, permAct σ ((-1) ^ r * esymmL n r) = (-1) ^ r * esymmL n r := by
      intro σ
      rw [map_mul, map_pow, map_neg, map_one, permAct_esymmL]
    rw [mul_assoc ((-1) ^ r * esymmL n r), altQuot_mul_of_symm hsym, schur]
    congr 2
    rw [← monomial_single_natCast, hP, ← monomial_add, ← add_assoc, ← Pi.single_add]
    congr 3
    push_cast [Nat.cast_sub hr']
    ring
  rw [Finset.sum_congr rfl hterm, ← altQuot_sum, ← Finset.sum_mul, sum_esymmL_mul_pow, zero_mul,
    altQuot_zero']

/- English proof (translation)
Use `altQuot_eq_of_mul ?_` and prove the remaining obligations. Rewrite using `[mul_zero]`. Establish `hlt : (-m).toNat < n` using `by omega`. Use `(alternant_eq_zero (i := (⟨0, hn⟩ : Fin n)) (j := ⟨(-m).toNat, hlt⟩) ?_ ?_).symm` and prove the remaining obligations. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Establish `hne : (⟨(-m).toNat, hlt⟩ : Fin n) ≠ ⟨0, hn⟩`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, staircase]`. Establish `: (((-m).toNat : ℕ) : ℤ) = -m` using `by omega`.

Simplify using `only [this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schur_single_eq_zero (hn : 0 < n) {m : ℤ} (h1 : 1 - (n : ℤ) ≤ m) (h2 : m ≤ -1) :
    schur (Pi.single (⟨0, hn⟩ : Fin n) m) = 0 := by
  refine altQuot_eq_of_mul ?_
  rw [mul_zero]
  have hlt : (-m).toNat < n := by omega
  refine (alternant_eq_zero (i := (⟨0, hn⟩ : Fin n)) (j := ⟨(-m).toNat, hlt⟩) ?_ ?_).symm
  · intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  · have hne : (⟨(-m).toNat, hlt⟩ : Fin n) ≠ ⟨0, hn⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, staircase]
    have : (((-m).toNat : ℕ) : ℤ) = -m := by omega
    simp only [this]
    ring

/- English proof (translation)
The claim follows from `altQuot_eq_of_mul (by rw [mul_one, zero_add]; rfl)`.
-/
theorem schur_zero_eq_one : schur (0 : Fin n → ℤ) = 1 :=
  altQuot_eq_of_mul (by rw [mul_one, zero_add]; rfl)

/- English proof (translation)
Use `set f : ℕ → LaurentRing n := fun r => (-1) ^ r * esymmL n r * schur (Pi.single (⟨0, hn⟩ : Fin n) ((j : ℤ) - (r : ℤ))) with hf`. Establish `h1 : ∑ r ∈ Finset.range (j + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r`. Use `Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_` and prove the remaining obligations. Establish `hjr : j < r`. Use `Finset.mem_range.not.1 hr'` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hrn : n < r`. Simplify using `only [hf]`. Rewrite using `[esymmL_eq_zero hrn, mul_zero, zero_mul]`. Simplify using `only [hf]`.

Rewrite using `[schur_single_eq_zero hn (by omega) (by omega), mul_zero]`. Establish `h2 : ∑ r ∈ Finset.range (n + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r`. Use `Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_` and prove the remaining obligations. Establish `hrn : n < r`. Use `Finset.mem_range.not.1 hr'` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [hf]`. Rewrite using `[esymmL_eq_zero hrn, mul_zero, zero_mul]`. Establish `h3 : ∑ r ∈ Finset.range (j + 1), f r = 0`. Rewrite using `[h1, ← h2]`.

Conclude with `sum_esymmL_mul_schur hn (j : ℤ)`. Rewrite using `[← h3]`. Use `Finset.sum_congr rfl fun r hr => ?_` and prove the remaining obligations. Establish `hr' : r ≤ j` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)`. Simplify using `only [hf]`.

Rewrite using `[Nat.cast_sub hr']`.
-/
theorem sum_range_esymmL_mul_schur (hn : 0 < n) {j : ℕ} (hj : 1 ≤ j) :
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single (⟨0, hn⟩ : Fin n) ((j - r : ℕ) : ℤ)) = 0 := by
  set f : ℕ → LaurentRing n := fun r => (-1) ^ r * esymmL n r *
    schur (Pi.single (⟨0, hn⟩ : Fin n) ((j : ℤ) - (r : ℤ))) with hf
  have h1 : ∑ r ∈ Finset.range (j + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    have hjr : j < r := by
      have := Finset.mem_range.not.1 hr'
      omega
    by_cases hrn : n < r
    · simp only [hf]
      rw [esymmL_eq_zero hrn, mul_zero, zero_mul]
    · simp only [hf]
      rw [schur_single_eq_zero hn (by omega) (by omega), mul_zero]
  have h2 : ∑ r ∈ Finset.range (n + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    have hrn : n < r := by
      have := Finset.mem_range.not.1 hr'
      omega
    simp only [hf]
    rw [esymmL_eq_zero hrn, mul_zero, zero_mul]
  have h3 : ∑ r ∈ Finset.range (j + 1), f r = 0 := by
    rw [h1, ← h2]
    exact sum_esymmL_mul_schur hn (j : ℤ)
  rw [← h3]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  simp only [hf]
  rw [Nat.cast_sub hr']

/- English proof (translation)
Rewrite using `[monomialChar_apply]`. Establish `h : ∀ i, ((z i ^ lamS S i : ℂˣ) : ℂ) = if i ∈ S then (z i : ℂ) else 1`. Introduce `i`. Rewrite using `[lamS_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `only [h]`. Rewrite using `[Finset.prod_ite_mem, Finset.univ_inter]`.
-/
theorem monomialChar_lamS (S : Finset (Fin n)) (z : Fin n → ℂˣ) :
    monomialChar (lamS S) z = ∏ i ∈ S, (z i : ℂ) := by
  rw [monomialChar_apply]
  have h : ∀ i, ((z i ^ lamS S i : ℂˣ) : ℂ) = if i ∈ S then (z i : ℂ) else 1 := by
    intro i
    rw [lamS_apply]
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/- English proof (translation)
Introduce `n hn z`. Use `⟨?_, fun j hj => ?_⟩` and prove the remaining obligations. Establish `h0 : (Pi.single (⟨0, hn⟩ : Fin n) ((0 : ℕ) : ℤ) : Fin n → ℤ) = 0`. Simplify using the standard rewrite rules. Rewrite using `[h0, schur_zero_eq_one, map_one]`.

Establish `h` using `congrArg (evalAt z) (sum_range_esymmL_mul_schur hn hj)`. Simplify using `only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero, evalAt_esymmL, monomialChar_lamS] at h`. Conclude with `h`.
-/
theorem schur_row_recursion : L8 := by
  intro n hn z
  refine ⟨?_, fun j hj => ?_⟩
  · have h0 : (Pi.single (⟨0, hn⟩ : Fin n) ((0 : ℕ) : ℤ) : Fin n → ℤ) = 0 := by
      simp
    rw [h0, schur_zero_eq_one, map_one]
  · have h := congrArg (evalAt z) (sum_range_esymmL_mul_schur hn hj)
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero, evalAt_esymmL,
      monomialChar_lamS] at h
    exact h

end GlobalTheory.CompanionTheory.SatakeBound

end
