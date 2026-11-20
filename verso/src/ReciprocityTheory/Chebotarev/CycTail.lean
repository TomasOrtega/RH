import ReciprocityTheory.Chebotarev.NZIdeal

open NumberField IsDedekindDomain

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

noncomputable def primeBelow (q : Prm E) : ℕ := Ideal.absNorm (q.asIdeal.under ℤ)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem primeBelow_prime (q : Prm E) : (primeBelow q).Prime := by
  have : NeZero q.asIdeal := ⟨q.ne_bot⟩
  exact Nat.absNorm_under_prime q.asIdeal

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nrm_eq_primeBelow_pow (q : Prm E) : ∃ f : ℕ, Nrm q = primeBelow q ^ f :=
  have : q.asIdeal.LiesOver (Ideal.span {((primeBelow q : ℕ) : ℤ)}) := Int.liesOver_span_absNorm q.asIdeal
  ⟨_, Ideal.absNorm_eq_pow_inertiaDeg' q.asIdeal (primeBelow_prime q)⟩

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem two_le_nrm (q : Prm E) : 2 ≤ Nrm q := by
  have h0 : Nrm q ≠ 0 := by
    unfold Nrm; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot
  have h1 : Nrm q ≠ 1 := by
    unfold Nrm; rw [Ne, Ideal.absNorm_eq_one_iff]; exact q.isPrime.ne_top
  omega

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem primeBelow_sq_le (q : Prm E) (h : ¬ (Nrm q).Prime) : primeBelow q ^ 2 ≤ Nrm q := by
  obtain ⟨f, hf⟩ := nrm_eq_primeBelow_pow q
  have hp := primeBelow_prime q
  have h1 : Nrm q ≠ 1 := by have := two_le_nrm q; omega
  rw [hf] at h h1 ⊢
  have hf0 : f ≠ 0 := by rintro rfl; simp at h1
  have hf1 : f ≠ 1 := by rintro rfl; simp [hp] at h
  exact Nat.pow_le_pow_right hp.pos (by omega)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem mem_primesOverFinset_primeBelow (q : Prm E) :
    q.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((primeBelow q : ℕ) : ℤ)}) (𝓞 E) := by
  have hp := primeBelow_prime q
  have : (Ideal.span {((primeBelow q : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  rw [IsDedekindDomain.mem_primesOverFinset_iff (by simp [hp.ne_zero])]
  exact ⟨q.isPrime, Int.liesOver_span_absNorm q.asIdeal⟩

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem card_primesOverFinset_le (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 E)).card ≤ Module.finrank ℚ E := by
  have : (Ideal.span {(p:ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E (by simp [hp.ne_zero])

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem card_filter_primeBelow_le (u : Finset (Prm E)) (p : ℕ) (hp : p.Prime) :
    (u.filter fun x => primeBelow x = p).card ≤ Module.finrank ℚ E := by
  classical
  refine le_trans ?_ (card_primesOverFinset_le (E := E) p hp)
  refine Finset.card_le_card_of_injOn (fun x => x.asIdeal) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter] at hx
    have := mem_primesOverFinset_primeBelow x
    rw [hx.2] at this
    exact this
  · intro x _ y _ hxy
    exact HeightOneSpectrum.ext hxy

/- English proof (translation)
Check the signs of the components of the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nonprime_term_le (q : Prm E) :
    (if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) ≤ 1 / ((primeBelow q : ℕ) : ℝ) ^ 2 := by
  split_ifs with h
  · positivity
  · have hq := primeBelow_sq_le q h
    have hp := (primeBelow_prime q).pos
    have hq' : ((primeBelow q : ℝ)) ^ 2 ≤ (Nrm q : ℝ) := by exact_mod_cast hq
    have hpos : (0 : ℝ) < (primeBelow q : ℝ) ^ 2 := by positivity
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos hq'

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.

Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem summable_nonprime_norm :
    Summable (fun q : Prm E => if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) := by
  classical
  let G : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hG : Summable G := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hG0 : ∀ n, 0 ≤ G n := fun n => by positivity
  refine summable_of_sum_le (c := Module.finrank ℚ E * ∑' n, G n) (fun q => by
    dsimp only; split_ifs <;> positivity) (fun u => ?_)
  calc ∑ x ∈ u, (if (Nrm x).Prime then (0 : ℝ) else ((Nrm x : ℕ) : ℝ)⁻¹)
        ≤ ∑ x ∈ u, G (primeBelow x) := Finset.sum_le_sum fun x _ => nonprime_term_le x
    _ = ∑ b ∈ u.image (fun x => primeBelow x),
          (u.filter fun x => primeBelow x = b).card • G b := Finset.sum_comp _ _
    _ ≤ ∑ b ∈ u.image (fun x => primeBelow x), (Module.finrank ℚ E : ℝ) * G b := by
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hb
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hG0 _)
        exact_mod_cast card_filter_primeBelow_le u _ (primeBelow_prime x)
    _ = (Module.finrank ℚ E : ℝ) * ∑ b ∈ u.image (fun x => primeBelow x), G b := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ E : ℝ) * ∑' n, G n :=
        mul_le_mul_of_nonneg_left (hG.sum_le_tsum _ fun n _ => hG0 n) (by positivity)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_norm_mem (T : Finset ℕ) : {q : Prm E | Nrm q ∈ T}.Finite := by
  have h : {I : Ideal (𝓞 E) | Ideal.absNorm I ∈ T}.Finite := by
    have : {I : Ideal (𝓞 E) | Ideal.absNorm I ∈ T} = ⋃ n ∈ T, {I : Ideal (𝓞 E) | Ideal.absNorm I = n} := by
      ext; simp
    rw [this]
    exact Set.Finite.biUnion T.finite_toSet fun n _ => Ideal.finite_setOfPred_absNorm_eq n
  exact h.preimage (f := fun q : Prm E => q.asIdeal) (fun x _ y _ hxy => HeightOneSpectrum.ext hxy)

end ReciprocityTheory.Cheb
