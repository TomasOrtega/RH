import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffBase

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

open Finset
open scoped ComplexOrder

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Simplify using `only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_mk, Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte, Nat.cast_pow, map_pow]`. Break down `MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h` into its components or cases. Simplify using `only [h, zero_geom_sum]`. Simplify using the standard rewrite rules. Simplify using `only [h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`.

Establish `: (1 : ℝ) ≤ ((2 * a + 1 : ℕ) : ℝ)`. Use `push_cast`. Establish `: (0 : ℝ) ≤ a` using `Nat.cast_nonneg a`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.

Simplify using `only [h, neg_one_geom_sum]`. Establish `: ¬ Even (2 * a + 1)` using `by simp`. Simplify using `[this]`.
-/
theorem one_le_zetaMul_prime_pow_even {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (a : ℕ) : 1 ≤ DirichletCharacter.zetaMul χ (p ^ (2 * a)) := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · simp only [h, zero_geom_sum]
    simp
  · simp only [h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : (1 : ℝ) ≤ ((2 * a + 1 : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    exact_mod_cast this
  · simp only [h, neg_one_geom_sum]
    have : ¬ Even (2 * a + 1) := by simp
    simp [this]

/- English proof (translation)
Rewrite using `[χ.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero 2 hk)]`. Unfold `Finsupp.prod`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => ?_)` and prove the remaining obligations. Establish `hpp : p.Prime` using `Nat.prime_of_mem_primeFactors (by simpa using hp)`.

Rewrite using `[Nat.factorization_pow]`. Simplify using `using one_le_zetaMul_prime_pow_even hχ hpp (k.factorization p)`.
-/
theorem one_le_zetaMul_sq {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (k : ℕ)
    (hk : k ≠ 0) : 1 ≤ DirichletCharacter.zetaMul χ (k ^ 2) := by
  rw [χ.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero 2 hk)]
  unfold Finsupp.prod
  calc (1 : ℂ) = ∏ _p ∈ (k ^ 2).factorization.support, (1 : ℂ) := by simp
    _ ≤ _ := by
      refine Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => ?_)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
      rw [Nat.factorization_pow]
      simpa using one_le_zetaMul_prime_pow_even hχ hpp (k.factorization p)

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Simplify using `only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_mk]`. Use `Finset.sum_congr rfl (fun d hd => ?_)` and prove the remaining obligations. Establish `: d ≠ 0` using `(Nat.pos_of_mem_divisors hd).ne'`. Simplify using `[this]`.
-/
theorem zetaMul_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    DirichletCharacter.zetaMul χ n = ∑ d ∈ n.divisors, χ (d : ZMod q) := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [this]

/- English proof (translation)
Establish `h1 : (1 - u) ≠ 0` using `sub_ne_zero.mpr (Ne.symm hu)`. Proceed by induction on `M with`. Consider the case `zero => simp`. Consider the case `succ M ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega), ih]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem geomIcc (u : ℝ) (hu : u ≠ 1) (M : ℕ) :
    ∑ m ∈ Icc 1 M, u ^ m = (u - u ^ (M + 1)) / (1 - u) := by
  have h1 : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    field_simp
    ring

/- English proof (translation)
Establish `hd0 : (0 : ℝ) < d` using `by exact_mod_cast hd`. Establish `hd1 : (1 : ℝ) ≤ d` using `by exact_mod_cast hd`. Use `set t : ℝ := (d : ℝ) / x with ht`. Establish `ht0 : 0 < t` using `div_pos hd0 hx`. Use `set u : ℝ := Real.exp (-t) with hu`.

Establish `hu0 : 0 < u` using `Real.exp_pos _`. Establish `hu1 : u < 1`. Rewrite using `[hu, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)`. Establish `h1u : 0 < 1 - u` using `by linarith`. Establish `hterm : ∀ m : ℕ, Real.exp (-((d * m : ℕ) : ℝ) / x) = u ^ m`.

Introduce `m`. Rewrite using `[hu, ← Real.exp_nat_mul]`. Use `congr 1`. Rewrite using `[ht]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Use `⟨u ^ (N / d + 1) / (1 - u), by positivity, ?_, ?_⟩` and prove the remaining obligations. Establish `hA : u ^ (N / d + 1) ≤ Real.exp (-(N : ℝ) / x)`. Rewrite using `[← hterm]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Establish `: N < d * (N / d + 1)` using `Nat.lt_mul_div_succ N hd`. Establish `h2 : (N : ℝ) ≤ ((d * (N / d + 1) : ℕ) : ℝ)` using `by exact_mod_cast this.le`. Rewrite using `[neg_div, neg_div]`. Conclude with `neg_le_neg (div_le_div_of_nonneg_right h2 hx.le)`. Establish `hB : 1 / (x + 1) ≤ 1 - u`.

Establish `hle : u ≤ Real.exp (-(1 / x))`. Rewrite using `[hu]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[ht]`. Conclude with `neg_le_neg (div_le_div_of_nonneg_right hd1 hx.le)`.

Establish `h3 : 1 / x + 1 ≤ Real.exp (1 / x)` using `Real.add_one_le_exp _`. Establish `h4 : Real.exp (-(1 / x)) ≤ x / (x + 1)`. Rewrite using `[Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : 1 - x / (x + 1) = 1 / (x + 1)` using `by field_simp; ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_iff₀ h1u]`. Establish `hE : 0 < Real.exp (-(N : ℝ) / x)` using `Real.exp_pos _`. Establish `hx1 : 0 < x + 1` using `by linarith`. Establish `h6 : 1 ≤ (x + 1) * (1 - u)`.

Rewrite `hB` using `[div_le_iff₀ hx1]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul_of_nonneg_left h6 hE.le`. Use `_ = _ := by ring`.

Repeatedly rewrite using `[hterm]`. Rewrite using `[geomIcc u hu1.ne]`. Establish `hg : x / d + gExp t = u / (1 - u)`. Unfold `gExp`. Establish `: (1 : ℝ) / t = x / d` using `by rw [ht]; field_simp`.

Rewrite using `[this]`. Establish `he : Real.exp t = u⁻¹` using `by rw [hu, Real.exp_neg, inv_inv]`. Rewrite using `[he]`. Establish `hu' : u ≠ 0` using `hu0.ne'`. Establish `: u⁻¹ - 1 ≠ 0`.

Establish `: u⁻¹ - 1 = (1 - u) / u` using `by field_simp`. Rewrite using `[this]`. Check the signs of the components of the expression. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem innerSum (x : ℝ) (hx : 0 < x) (d N : ℕ) (hd : 1 ≤ d) :
    ∃ T : ℝ, 0 ≤ T ∧ T ≤ (x + 1) * Real.exp (-(N : ℝ) / x) ∧
      ∑ m ∈ Icc 1 (N / d), Real.exp (-((d * m : ℕ) : ℝ) / x) = x / d + gExp ((d : ℝ) / x) - T := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set t : ℝ := (d : ℝ) / x with ht
  have ht0 : 0 < t := div_pos hd0 hx
  set u : ℝ := Real.exp (-t) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : u < 1 := by
    rw [hu, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1u : 0 < 1 - u := by linarith
  have hterm : ∀ m : ℕ, Real.exp (-((d * m : ℕ) : ℝ) / x) = u ^ m := by
    intro m
    rw [hu, ← Real.exp_nat_mul]
    congr 1
    rw [ht]; push_cast; field_simp
  refine ⟨u ^ (N / d + 1) / (1 - u), by positivity, ?_, ?_⟩
  ·
    have hA : u ^ (N / d + 1) ≤ Real.exp (-(N : ℝ) / x) := by
      rw [← hterm]
      apply Real.exp_le_exp.mpr
      have : N < d * (N / d + 1) := Nat.lt_mul_div_succ N hd
      have h2 : (N : ℝ) ≤ ((d * (N / d + 1) : ℕ) : ℝ) := by exact_mod_cast this.le
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_right h2 hx.le)
    have hB : 1 / (x + 1) ≤ 1 - u := by
      have hle : u ≤ Real.exp (-(1 / x)) := by
        rw [hu]; apply Real.exp_le_exp.mpr
        rw [ht]; exact neg_le_neg (div_le_div_of_nonneg_right hd1 hx.le)
      have h3 : 1 / x + 1 ≤ Real.exp (1 / x) := Real.add_one_le_exp _
      have h4 : Real.exp (-(1 / x)) ≤ x / (x + 1) := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
        calc (x / (x + 1))⁻¹ = 1 / x + 1 := by field_simp; ring
          _ ≤ _ := h3
      have h5 : 1 - x / (x + 1) = 1 / (x + 1) := by field_simp; ring
      linarith
    rw [div_le_iff₀ h1u]
    have hE : 0 < Real.exp (-(N : ℝ) / x) := Real.exp_pos _
    have hx1 : 0 < x + 1 := by linarith
    have h6 : 1 ≤ (x + 1) * (1 - u) := by
      rw [div_le_iff₀ hx1] at hB; linarith
    calc u ^ (N / d + 1) ≤ Real.exp (-(N : ℝ) / x) := hA
      _ = Real.exp (-(N : ℝ) / x) * 1 := by ring
      _ ≤ Real.exp (-(N : ℝ) / x) * ((x + 1) * (1 - u)) := by
        exact mul_le_mul_of_nonneg_left h6 hE.le
      _ = _ := by ring
  · simp_rw [hterm]
    rw [geomIcc u hu1.ne]
    have hg : x / d + gExp t = u / (1 - u) := by
      unfold gExp
      have : (1 : ℝ) / t = x / d := by rw [ht]; field_simp
      rw [this]
      have he : Real.exp t = u⁻¹ := by rw [hu, Real.exp_neg, inv_inv]
      rw [he]
      have hu' : u ≠ 0 := hu0.ne'
      have : u⁻¹ - 1 ≠ 0 := by
        have : u⁻¹ - 1 = (1 - u) / u := by field_simp
        rw [this]; positivity
      field_simp
      ring
    rw [hg]
    ring

/- English proof (translation)
Establish `h1 : ∀ n ∈ Icc 1 N, ∑ d ∈ n.divisors, F d n = ∑ d ∈ Icc 1 N, if d ∣ n then F d n else 0`. Introduce `n hn`. Rewrite using `[← Finset.sum_filter]`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations. Use extensionality with `d`.

Simplify using `only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc] at hn ⊢`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hdn, hn0⟩`. Use `Nat.le_of_dvd (by omega) hdn` as an intermediate fact. Use `Nat.pos_of_dvd_of_pos hdn (by omega)` as an intermediate fact.

Conclude with `⟨⟨by omega, by omega⟩, hdn⟩`. Introduce and unpack `⟨_, hdn⟩`. Conclude with `⟨hdn, by omega⟩`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun d hd => ?_)` and prove the remaining obligations.

Rewrite using `[← Finset.sum_filter]`. Establish `hd1 : 1 ≤ d` using `(Finset.mem_Icc.mp hd).1`. Use `symm`. Use `Finset.sum_nbij (fun m => d * m) ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `m hm`.

Simplify using `only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢`. Use `⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, Dvd.intro _ rfl⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `a _ b _ hab`. Conclude with `Nat.eq_of_mul_eq_mul_left hd1 hab`.

Introduce `n hn`. Simplify using `only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn`. Take `⟨⟨hn1, hnN⟩, m, rfl⟩` from `hn`. Use `⟨m, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Finset.coe_Icc, Set.mem_Icc]`.

Use `⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hn1), ?_⟩` and prove the remaining obligations. Conclude with `(Nat.le_div_iff_mul_le hd1).mpr (by rw [Nat.mul_comm]; exact hnN)`.
-/
theorem regroup (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, F d n = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d (d * m) := by
  have h1 : ∀ n ∈ Icc 1 N, ∑ d ∈ n.divisors, F d n = ∑ d ∈ Icc 1 N, if d ∣ n then F d n else 0 := by
    intro n hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    constructor
    · rintro ⟨hdn, hn0⟩
      have := Nat.le_of_dvd (by omega) hdn
      have := Nat.pos_of_dvd_of_pos hdn (by omega)
      exact ⟨⟨by omega, by omega⟩, hdn⟩
    · rintro ⟨_, hdn⟩
      exact ⟨hdn, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [← Finset.sum_filter]
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  symm
  refine Finset.sum_nbij (fun m => d * m) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, Dvd.intro _ rfl⟩
    calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d hm.2
      _ ≤ N := Nat.mul_div_le N d
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd1 hab
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
    obtain ⟨⟨hn1, hnN⟩, m, rfl⟩ := hn
    refine ⟨m, ?_, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hn1), ?_⟩
    exact (Nat.le_div_iff_mul_le hd1).mpr (by rw [Nat.mul_comm]; exact hnN)

/- English proof (translation)
Use `set E : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / x) with hE`. Establish `hE0 : ∀ n, 0 < E n` using `fun n => Real.exp_pos _`. Establish `hlow : (K : ℝ) / Real.exp 1 ≤ ∑ n ∈ Icc 1 N, r n * E n`. Establish `hsub : (Icc 1 K).image (fun k => k ^ 2) ⊆ Icc 1 N`. Introduce `n hn`.

Simplify using `only [Finset.mem_image, Finset.mem_Icc] at hn ⊢`. Take `⟨k, ⟨hk1, hkK⟩, rfl⟩` from `hn`. Conclude with `⟨Nat.one_le_pow _ _ hk1, le_trans (Nat.pow_le_pow_left hkK 2) hKN⟩`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[div_eq_mul_inv]`.

Use `_ ≤ ∑ k ∈ Icc 1 K, r (k ^ 2) * E (k ^ 2) := by`. Use `Finset.sum_le_sum (fun k hk => ?_)` and prove the remaining obligations. Establish `hk'` using `Finset.mem_Icc.mp hk`. Establish `h1 : 1 ≤ r (k ^ 2)` using `hr1 k (by omega)`. Establish `h2 : (Real.exp 1)⁻¹ ≤ E (k ^ 2)`.

Rewrite using `[← Real.exp_neg, hE]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hkK : (k : ℝ) ≤ K` using `by exact_mod_cast hk'.2`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `: ((k ^ 2 : ℕ) : ℝ) ≤ x`.

Use `push_cast`. Conclude with `le_trans (pow_le_pow_left₀ hk0 hkK 2) hKx`. Rewrite using `[neg_div]`. Conclude with `neg_le_neg ((div_le_one hx).mpr this)`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = ∑ n ∈ (Icc 1 K).image (fun k => k ^ 2), r n * E n := by`. Rewrite using `[Finset.sum_image]`. Introduce `a _ b _ hab`. Conclude with `Nat.pow_left_injective (n := 2) (by omega) hab`. Use `_ ≤ ∑ n ∈ Icc 1 N, r n * E n := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg (hr0 n) (hE0 n).le)`.

Establish `hre : ∑ n ∈ Icc 1 N, r n * E n = ∑ d ∈ Icc 1 N, c d * ∑ m ∈ Icc 1 (N / d), E (d * m)`. Use `regroup N (fun d n => c d * E n)` as an intermediate fact. Simplify using `only [← Finset.sum_mul, ← Finset.mul_sum] at this`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl (fun n _ => by rw [hr n])`.

Establish `hup : ∑ d ∈ Icc 1 N, c d * ∑ m ∈ Icc 1 (N / d), E (d * m) ≤ ∑ d ∈ Icc 1 N, (x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) + (x + 1) * Real.exp (-(N : ℝ) / x))`. Use `Finset.sum_le_sum (fun d hd => ?_)` and prove the remaining obligations. Take `⟨T, hT0, hT1, hT⟩` from `innerSum x hx d N (Finset.mem_Icc.mp hd).1`. Rewrite using `[hE]`. Simplify using `only`.

Rewrite using `[hT]`. Establish `h1 : -(c d * T) ≤ T`. Use `abs_le.mp (hc d)` as an intermediate fact. Use polynomial arithmetic with `[this.1, this.2]`. Establish `h2 : c d * (x / d + gExp ((d : ℝ) / x) - T) = x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) + -(c d * T)` using `by ring`.

Rewrite using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin : ∑ d ∈ Icc 1 N, (x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) + (x + 1) * Real.exp (-(N : ℝ) / x)) = x * (∑ d ∈ Icc 1 N, c d / (d : ℝ)) + (∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x)) + (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x)`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem smoothLowerReal (c r : ℕ → ℝ) (hr : ∀ n, r n = ∑ d ∈ n.divisors, c d)
    (hc : ∀ d, |c d| ≤ 1) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ k, k ≠ 0 → 1 ≤ r (k ^ 2))
    (K N : ℕ) (x : ℝ) (hx : 0 < x) (hKx : (K : ℝ) ^ 2 ≤ x) (hKN : K ^ 2 ≤ N) :
    (K : ℝ) / Real.exp 1 ≤
      x * (∑ d ∈ Icc 1 N, c d / (d : ℝ)) + (∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x)) +
      (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x) := by
  set E : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / x) with hE
  have hE0 : ∀ n, 0 < E n := fun n => Real.exp_pos _

  have hlow : (K : ℝ) / Real.exp 1 ≤ ∑ n ∈ Icc 1 N, r n * E n := by
    have hsub : (Icc 1 K).image (fun k => k ^ 2) ⊆ Icc 1 N := by
      intro n hn
      simp only [Finset.mem_image, Finset.mem_Icc] at hn ⊢
      obtain ⟨k, ⟨hk1, hkK⟩, rfl⟩ := hn
      exact ⟨Nat.one_le_pow _ _ hk1, le_trans (Nat.pow_le_pow_left hkK 2) hKN⟩
    calc (K : ℝ) / Real.exp 1 = ∑ _k ∈ Icc 1 K, (Real.exp 1)⁻¹ := by
          simp [div_eq_mul_inv]
      _ ≤ ∑ k ∈ Icc 1 K, r (k ^ 2) * E (k ^ 2) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hk' := Finset.mem_Icc.mp hk
          have h1 : 1 ≤ r (k ^ 2) := hr1 k (by omega)
          have h2 : (Real.exp 1)⁻¹ ≤ E (k ^ 2) := by
            rw [← Real.exp_neg, hE]
            apply Real.exp_le_exp.mpr
            have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk'.2
            have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            have : ((k ^ 2 : ℕ) : ℝ) ≤ x := by
              push_cast
              exact le_trans (pow_le_pow_left₀ hk0 hkK 2) hKx
            rw [neg_div]
            exact neg_le_neg ((div_le_one hx).mpr this)
          calc (Real.exp 1)⁻¹ = 1 * (Real.exp 1)⁻¹ := by ring
            _ ≤ r (k ^ 2) * E (k ^ 2) := mul_le_mul h1 h2 (by positivity) (by linarith)
      _ = ∑ n ∈ (Icc 1 K).image (fun k => k ^ 2), r n * E n := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          exact Nat.pow_left_injective (n := 2) (by omega) hab
      _ ≤ ∑ n ∈ Icc 1 N, r n * E n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => mul_nonneg (hr0 n) (hE0 n).le)

  have hre : ∑ n ∈ Icc 1 N, r n * E n = ∑ d ∈ Icc 1 N, c d * ∑ m ∈ Icc 1 (N / d), E (d * m) := by
    have := regroup N (fun d n => c d * E n)
    simp only [← Finset.sum_mul, ← Finset.mul_sum] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun n _ => by rw [hr n])
  have hup : ∑ d ∈ Icc 1 N, c d * ∑ m ∈ Icc 1 (N / d), E (d * m) ≤
      ∑ d ∈ Icc 1 N, (x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) +
        (x + 1) * Real.exp (-(N : ℝ) / x)) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    obtain ⟨T, hT0, hT1, hT⟩ := innerSum x hx d N (Finset.mem_Icc.mp hd).1
    rw [hE]
    simp only
    rw [hT]
    have h1 : -(c d * T) ≤ T := by
      have := abs_le.mp (hc d)
      nlinarith [this.1, this.2]
    have h2 : c d * (x / d + gExp ((d : ℝ) / x) - T) =
        x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) + -(c d * T) := by ring
    rw [h2]
    linarith
  have hfin : ∑ d ∈ Icc 1 N, (x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) +
        (x + 1) * Real.exp (-(N : ℝ) / x)) =
      x * (∑ d ∈ Icc 1 N, c d / (d : ℝ)) + (∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x)) +
      (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
    ring
  linarith

/- English proof (translation)
Use `set c : ℕ → ℝ := fun d => (χ (d : ZMod q)).re with hcdef`. Establish `hχc : ∀ d : ℕ, χ (d : ZMod q) = ((c d : ℝ) : ℂ)`. Introduce `d`. Apply the tactic sequence `rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ2 (d : ZMod q) with h | h | h <;>`. Simplify using `[hcdef, h]`.

Establish `hc : ∀ d, |c d| ≤ 1`. Introduce `d`. Apply the tactic sequence `rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ2 (d : ZMod q) with h | h | h <;>`. Simplify using `[hcdef, h]`. Establish `hz : ∀ n, DirichletCharacter.zetaMul χ n = ((∑ d ∈ n.divisors, c d : ℝ) : ℂ)`.

Introduce `n`. Rewrite using `[zetaMul_eq_sum]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl (fun d _ => hχc d)`. Establish `key` using `smoothLowerReal c (fun n => ∑ d ∈ n.divisors, c d) (fun _ => rfl) hc (fun n => by`.

Use `DirichletCharacter.zetaMul_nonneg hχ2 n` as an intermediate fact. Rewrite `this` using `[hz]`. Conclude with `this)` after adjusting the coercions. Use the proof step `(fun k hk => by`. Use `one_le_zetaMul_sq hχ2 k hk` as an intermediate fact.

Rewrite `this` using `[hz]`. Conclude with `this) K N x hx hKx hKN` after adjusting the coercions. Establish `e1 : (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) / (d : ℂ)).re = ∑ d ∈ Icc 1 N, c d / (d : ℝ)`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations.

Rewrite using `[hχc d, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]`. Establish `e2 : (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)).re = ∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x)`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[hχc d, ← Complex.ofReal_mul, Complex.ofReal_re]`.

Rewrite using `[e1, e2]`. Conclude with `key`.
-/
theorem smoothLower (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (K N : ℕ) (x : ℝ) (hx : 0 < x) (hKx : (K : ℝ) ^ 2 ≤ x) (hKN : K ^ 2 ≤ N) :
    (K : ℝ) / Real.exp 1 ≤
      x * (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) / (d : ℂ)).re +
      (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)).re +
      (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x) := by
  set c : ℕ → ℝ := fun d => (χ (d : ZMod q)).re with hcdef
  have hχc : ∀ d : ℕ, χ (d : ZMod q) = ((c d : ℝ) : ℂ) := by
    intro d
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ2 (d : ZMod q) with h | h | h <;>
      simp [hcdef, h]
  have hc : ∀ d, |c d| ≤ 1 := by
    intro d
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ2 (d : ZMod q) with h | h | h <;>
      simp [hcdef, h]
  have hz : ∀ n, DirichletCharacter.zetaMul χ n = ((∑ d ∈ n.divisors, c d : ℝ) : ℂ) := by
    intro n
    rw [zetaMul_eq_sum]
    push_cast
    exact Finset.sum_congr rfl (fun d _ => hχc d)
  have key := smoothLowerReal c (fun n => ∑ d ∈ n.divisors, c d) (fun _ => rfl) hc
    (fun n => by
      have := DirichletCharacter.zetaMul_nonneg hχ2 n
      rw [hz] at this
      exact_mod_cast this)
    (fun k hk => by
      have := one_le_zetaMul_sq hχ2 k hk
      rw [hz] at this
      exact_mod_cast this) K N x hx hKx hKN
  have e1 : (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) / (d : ℂ)).re = ∑ d ∈ Icc 1 N, c d / (d : ℝ) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hχc d, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  have e2 : (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)).re =
      ∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hχc d, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [e1, e2]
  exact key

end Formalism.HermitianLattices.Ext.SupplyAP
