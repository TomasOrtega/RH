import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl Polynomial

/- English proof (translation)
Establish `hmul : ∀ i, (p * (X - C a)).coeff i = (p * X).coeff i - a * p.coeff i`. Introduce `i`. Rewrite using `[mul_sub, coeff_sub, coeff_mul_C, mul_comm a]`. Establish `h1 : ∑ i ∈ Finset.range (p.natDegree + 1 + 1), (p * X).coeff i * d i = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * d (i + 1)`. Rewrite using `[Finset.sum_range_succ']`.

Simplify using `[coeff_mul_X]`. Establish `h2 : ∑ i ∈ Finset.range (p.natDegree + 1 + 1), a * p.coeff i * d i = ∑ i ∈ Finset.range (p.natDegree + 1), a * p.coeff i * d i`. Rewrite using `[Finset.sum_range_succ, coeff_eq_zero_of_natDegree_lt (by omega)]`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[hmul, sub_mul, Finset.sum_sub_distrib, h1, h2, mul_sub, Finset.sum_sub_distrib]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem shift_sum (p : ℤ[X]) (a : ℤ) (d : ℕ → ℤ) :
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (d (i + 1) - a * d i) =
      ∑ i ∈ Finset.range (p.natDegree + 1 + 1), (p * (X - C a)).coeff i * d i := by
  have hmul : ∀ i, (p * (X - C a)).coeff i = (p * X).coeff i - a * p.coeff i := by
    intro i
    rw [mul_sub, coeff_sub, coeff_mul_C, mul_comm a]
  have h1 : ∑ i ∈ Finset.range (p.natDegree + 1 + 1), (p * X).coeff i * d i =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * d (i + 1) := by
    rw [Finset.sum_range_succ']
    simp [coeff_mul_X]
  have h2 : ∑ i ∈ Finset.range (p.natDegree + 1 + 1), a * p.coeff i * d i =
      ∑ i ∈ Finset.range (p.natDegree + 1), a * p.coeff i * d i := by
    rw [Finset.sum_range_succ, coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  simp_rw [hmul, sub_mul, Finset.sum_sub_distrib, h1, h2, mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Establish `hmem : E ∈ Finset.range M` using `Finset.mem_range.2 h`. Unfold `polE`. Rewrite using `[natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]`. Simplify using `only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]`. Rewrite using `[Finset.card_erase_of_mem hmem, Finset.card_range]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem natDegree_polE (κ : ℤ) (M E : ℕ) (h : E < M) : (polE κ M E).natDegree + 1 = M := by
  have hmem : E ∈ Finset.range M := Finset.mem_range.2 h
  unfold polE
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem hmem, Finset.card_range]
  omega

/- English proof (translation)
Introduce `L F _ _ _ _ _ γ κ M E hE α 𝔡 hD P`. Take `⟨_, hmul, hone, _, hinv, hadd, hpow⟩` from `cAct L F`. Establish `hprod : ∀ (s : Finset ℕ) (f : ℕ → Fˣ), ordP P (∏ i ∈ s, f i) = ∑ i ∈ s, ordP P (f i)`. Introduce `s f`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations.

Simplify using `using hpow P 1 0`. Introduce `j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, hadd, ih]`. Establish `key : ∀ i : ℕ, ordP P (actU (γ⁻¹ ^ i) α) = 𝔡 (actP (γ ^ (i + 1)) P) - (κ : ℤ) ^ E * 𝔡 (actP (γ ^ i) P)`. Introduce `i`.

Establish `hP : actP (γ⁻¹ ^ i) (actP (γ ^ i) P) = P`. Rewrite using `[← hmul, inv_pow, inv_mul_cancel, hone]`. Establish `h0` using `hinv (γ⁻¹ ^ i) (actP (γ ^ i) P) α`. Rewrite `h0` using `[hP]`. Rewrite using `[h0, hD, ← hmul, pow_succ']`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hpol : polE (κ : ℤ) M E * (X - C ((κ : ℤ) ^ E)) = pol (κ : ℤ) M`. Rewrite using `[mul_comm]`. Conclude with `Finset.mul_prod_erase (Finset.range M) (fun j => X - C ((κ : ℤ) ^ j)) (Finset.mem_range.2 hE)`.

Establish `hs` using `shift_sum (polE (κ : ℤ) M E) ((κ : ℤ) ^ E) (fun i => 𝔡 (actP (γ ^ i) P))`. Rewrite `hs` using `[hpol, natDegree_polE κ M E hE]`. Unfold `polAct`. Rewrite using `[hprod]`. Simplify using `only [hpow, key]`.

Rewrite `*` using `[natDegree_polE κ M E hE]`. Conclude with `hs`.
-/
theorem UpperTheory.V.ZK.Cl.cBetaDiv :
    UpperTheory.V.ZK.Cl.CBetaDiv := by
  intro L F _ _ _ _ _ γ κ M E hE α 𝔡 hD P
  obtain ⟨_, hmul, hone, _, hinv, hadd, hpow⟩ := cAct L F
  have hprod : ∀ (s : Finset ℕ) (f : ℕ → Fˣ), ordP P (∏ i ∈ s, f i) = ∑ i ∈ s, ordP P (f i) := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · simpa using hpow P 1 0
    · intro j s hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj, hadd, ih]
  have key : ∀ i : ℕ, ordP P (actU (γ⁻¹ ^ i) α) =
      𝔡 (actP (γ ^ (i + 1)) P) - (κ : ℤ) ^ E * 𝔡 (actP (γ ^ i) P) := by
    intro i
    have hP : actP (γ⁻¹ ^ i) (actP (γ ^ i) P) = P := by
      rw [← hmul, inv_pow, inv_mul_cancel, hone]
    have h0 := hinv (γ⁻¹ ^ i) (actP (γ ^ i) P) α
    rw [hP] at h0
    rw [h0, hD, ← hmul, pow_succ']
    push_cast
    rfl
  have hpol : polE (κ : ℤ) M E * (X - C ((κ : ℤ) ^ E)) = pol (κ : ℤ) M := by
    rw [mul_comm]
    exact Finset.mul_prod_erase (Finset.range M) (fun j => X - C ((κ : ℤ) ^ j)) (Finset.mem_range.2 hE)
  have hs := shift_sum (polE (κ : ℤ) M E) ((κ : ℤ) ^ E) (fun i => 𝔡 (actP (γ ^ i) P))
  rw [hpol, natDegree_polE κ M E hE] at hs
  unfold polAct
  rw [hprod]
  simp only [hpow, key]
  rw [natDegree_polE κ M E hE] at *
  exact hs
