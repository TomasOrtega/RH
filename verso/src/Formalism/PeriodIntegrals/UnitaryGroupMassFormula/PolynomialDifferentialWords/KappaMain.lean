import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaCoeff

open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

/- English proof (translation)
Introduce `K _ _ k d A B h`. Establish `hmono : ∀ g : Fin k →₀ ℕ, A (mono K k d g) = B (mono K k d g)`. Introduce `g`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `m`.

Establish `h1` using `congrArg (coeff (Finsupp.sumElim m g)) h`. Rewrite `h1` using `[coeff_kappa, coeff_kappa]`. Conclude with `mul_left_cancel₀ (invFact_ne_zero g) h1`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`.

Rewrite using `[eq_sum_mono F, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, hmono g]`.
-/
theorem symbolMapInjective : KappaInj := by
  intro K _ _ k d A B h
  have hmono : ∀ g : Fin k →₀ ℕ, A (mono K k d g) = B (mono K k d g) := by
    intro g
    apply Subtype.ext
    ext m
    have h1 := congrArg (coeff (Finsupp.sumElim m g)) h
    rw [coeff_kappa, coeff_kappa] at h1
    exact mul_left_cancel₀ (invFact_ne_zero g) h1
  apply LinearMap.ext
  intro F
  rw [eq_sum_mono F, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, map_smul, hmono g]

/- English proof (translation)
Introduce `K _ _ k d A`. Use `show kappa K k d A ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d`. Establish `key : ∀ m g : Fin k →₀ ℕ, coeff (Finsupp.sumElim m g) (kappa K k d A) ≠ 0 → m.degree = d ∧ g.degree = d`. Introduce `m g h`. Rewrite `h` using `[coeff_kappa]`.

Establish `h2 : coeff m (A (mono K k d g) : MvPolynomial (Fin k) K) ≠ 0` using `right_ne_zero_of_mul h`. Use `⟨degree_of_coeff_ne _ h2, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hg`. Establish `h0 : mono K k d g = 0`. Unfold `mono`.

Rewrite using `[dif_neg hg]`. Rewrite `h2` using `[h0, map_zero]`. Simplify using `at h2`. Apply the tactic sequence `refine Submodule.mem_inf.2 ⟨?_, ?_⟩ <;> rw [mem_weightedHomogeneousSubmodule] <;> intro n hn <;>`. Take `⟨m, g, rfl⟩` from `exists_sumElim n`.

Rewrite using `[weight_wx]`. Conclude with `(key m g hn).1`. Rewrite using `[weight_wxi]`. Conclude with `(key m g hn).2`.
-/
theorem symbolMapBihomogeneous : KappaBihom := by
  intro K _ _ k d A
  show kappa K k d A ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  have key : ∀ m g : Fin k →₀ ℕ, coeff (Finsupp.sumElim m g) (kappa K k d A) ≠ 0 →
      m.degree = d ∧ g.degree = d := by
    intro m g h
    rw [coeff_kappa] at h
    have h2 : coeff m (A (mono K k d g) : MvPolynomial (Fin k) K) ≠ 0 := right_ne_zero_of_mul h
    refine ⟨degree_of_coeff_ne _ h2, ?_⟩
    by_contra hg
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dif_neg hg]
    rw [h0, map_zero] at h2
    simp at h2
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩ <;> rw [mem_weightedHomogeneousSubmodule] <;> intro n hn <;>
    obtain ⟨m, g, rfl⟩ := exists_sumElim n
  · rw [weight_wx]
    exact (key m g hn).1
  · rw [weight_wxi]
    exact (key m g hn).2

/- English proof (translation)
Introduce `K _ _ k d a b A`. Rewrite using `[kappa_apply, kappa_apply, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Ed_val, Derivation.map_smul, mul_smul_comm]`. Use `congr 1`.

Simplify using `only [Derivation.leibniz, pderiv_inl_xi, smul_zero, zero_add, add_zero, smul_eq_mul]`. Rewrite using `[pderiv_rename Sum.inl_injective, map_mul, rename_X]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem symbolMapMulLeft : KappaLeft := by
  intro K _ _ k d a b A
  rw [kappa_apply, kappa_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Module.End.mul_apply, Ed_val, Derivation.map_smul, mul_smul_comm]
  congr 1
  simp only [Derivation.leibniz, pderiv_inl_xi, smul_zero, zero_add, add_zero, smul_eq_mul]
  rw [pderiv_rename Sum.inl_injective, map_mul, rename_X]
  ring

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on'`. Use `next u c =>`. Rewrite using `[pderiv_monomial, coeff_monomial, coeff_monomial]`. Distinguish the cases in `h : u = n + Finsupp.single i 1`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h, zero_mul] split_ifs with h2`. Establish `hu : u i = 0`. Assume the negation of the conclusion as `hne`. Apply `h` to reduce the goal to its premises.

Rewrite using `[← h2, tsub_add_cancel_of_le]`. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Simplify using `[hu]`. Both sides reduce to the same expression.

Use `next p q hp hq =>`. Rewrite using `[map_add, coeff_add, coeff_add, hp, hq, add_mul]`.
-/
private theorem coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth {σ : Type} {K : Type} [Field K] (i : σ) (P : MvPolynomial σ K)
    (n : σ →₀ ℕ) : coeff n (pderiv i P) = coeff (n + Finsupp.single i 1) P * ((n i : K) + 1) := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = n + Finsupp.single i 1
    · subst h
      simp
    · rw [if_neg h, zero_mul]
      split_ifs with h2
      · have hu : u i = 0 := by
          by_contra hne
          apply h
          rw [← h2, tsub_add_cancel_of_le]
          rw [Finsupp.single_le_iff]
          omega
        simp [hu]
      · rfl
  next p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]

/- English proof (translation)
Introduce `K _ _ k d a b A`. Apply `pol_ext` to reduce the goal to its premises. Introduce `m g`. Rewrite using `[coeff_kappa, Module.End.mul_apply, Ed_mono, map_smul, Submodule.coe_smul, coeff_smul, coeff_X_mul']`. Distinguish the cases in `hb : g b = 0`.

Rewrite using `[if_neg (by simp [hb])]`. Simplify using `[hb]`. Rewrite using `[if_pos (by simp [hb]), sumElim_sub_single_inr, coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, sumElim_add_single_inr, coeff_kappa]`. Simplify using `only [Finsupp.sumElim_apply, Sum.elim_inr]`. Establish `h1` using `invFact_add_single (K := K) (g - single b 1) a`.

Establish `h2` using `invFact_add_single (K := K) (g - single b 1) b`. Establish `hle : single b 1 ≤ g`. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite `h2` using `[tsub_add_cancel_of_le hle]`.

Establish `h3 : ((g - single b 1 : Fin k →₀ ℕ) b : K) + 1 = (g b : K)`. Establish `h4 : (g - single b 1 : Fin k →₀ ℕ) b + 1 = g b`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Conclude with `h4` after adjusting the coercions.

Rewrite `h2` using `[h3]`. Take the linear combination `(coeff m (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K)) * h2 - (coeff m (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K)) * h1`.
-/
theorem symbolMapMulRight : KappaRight := by
  intro K _ _ k d a b A
  apply pol_ext
  intro m g
  rw [coeff_kappa, Module.End.mul_apply, Ed_mono, map_smul, Submodule.coe_smul, coeff_smul, coeff_X_mul']
  by_cases hb : g b = 0
  · rw [if_neg (by simp [hb])]
    simp [hb]
  · rw [if_pos (by simp [hb]), sumElim_sub_single_inr, coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, sumElim_add_single_inr, coeff_kappa]
    simp only [Finsupp.sumElim_apply, Sum.elim_inr]
    have h1 := invFact_add_single (K := K) (g - single b 1) a
    have h2 := invFact_add_single (K := K) (g - single b 1) b
    have hle : single b 1 ≤ g := by
      rw [Finsupp.single_le_iff]
      omega
    rw [tsub_add_cancel_of_le hle] at h2
    have h3 : ((g - single b 1 : Fin k →₀ ℕ) b : K) + 1 = (g b : K) := by
      have h4 : (g - single b 1 : Fin k →₀ ℕ) b + 1 = g b := by
        simp
        omega
      exact_mod_cast h4
    rw [h3] at h2
    linear_combination (coeff m (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K)) * h2 -
      (coeff m (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K)) * h1

/- English proof (translation)
Establish `hprod : ∀ f : Fin k → ℕ, ∏ i, (X (Sum.inl i) * X (Sum.inr i) : Pol K k) ^ f i = monomial (Finsupp.sumElim (Finsupp.equivFunOnFinite.symm f) (Finsupp.equivFunOnFinite.symm f)) 1`. Introduce `f`. Rewrite using `[monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]`. Simplify using `[mul_pow, Finset.prod_mul_distrib]`. Rewrite using `[tt, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]`.

Simplify using `only [hprod, ← map_natCast (C : K →+* Pol K k), coeff_C_mul, coeff_monomial, sumElim_inj, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `h : m = g ∧ g.degree = d`. Take `⟨hmg, hd⟩` from `h`. Rewrite using `[if_pos ⟨hmg, hd⟩, Finset.sum_eq_single (⇑g)]`. Simplify using `[hmg]`.

Introduce `f _ hf`. Rewrite using `[if_neg]`. Introduce and unpack `⟨_, h2⟩`. Apply `hf` to reduce the goal to its premises. Rewrite using `[← h2]`.

Simplify using the standard rewrite rules. Introduce `hnot`. It suffices to derive a contradiction. Apply `hnot` to reduce the goal to its premises. Rewrite using `[Finset.mem_piAntidiag]`.

Use `⟨?_, fun i _ => Finset.mem_univ i⟩` and prove the remaining obligations. Rewrite using `[← hd, Finsupp.degree_eq_sum]`. Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun f hf => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Introduce and unpack `⟨h1, h2⟩`. Apply `h` to reduce the goal to its premises. Use `⟨h1.symm.trans h2, ?_⟩` and prove the remaining obligations. Rewrite using `[← h2, Finsupp.degree_eq_sum]`. Establish `h3` using `(Finset.mem_piAntidiag.1 hf).1`.

Simplify using `using h3`.
-/
private theorem coeff_sumElim_tt_pow (K : Type) [Field K] (k d : ℕ) (m g : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (tt K k ^ d) =
      if m = g ∧ g.degree = d then ((Nat.multinomial Finset.univ ⇑g : ℕ) : K) else 0 := by
  classical
  have hprod : ∀ f : Fin k → ℕ, ∏ i, (X (Sum.inl i) * X (Sum.inr i) : Pol K k) ^ f i =
      monomial (Finsupp.sumElim (Finsupp.equivFunOnFinite.symm f) (Finsupp.equivFunOnFinite.symm f)) 1 := by
    intro f
    rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
    simp [mul_pow, Finset.prod_mul_distrib]
  rw [tt, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp only [hprod, ← map_natCast (C : K →+* Pol K k), coeff_C_mul, coeff_monomial, sumElim_inj, mul_ite,
    mul_one, mul_zero]
  by_cases h : m = g ∧ g.degree = d
  · obtain ⟨hmg, hd⟩ := h
    rw [if_pos ⟨hmg, hd⟩, Finset.sum_eq_single (⇑g)]
    · simp [hmg]
    · intro f _ hf
      rw [if_neg]
      rintro ⟨_, h2⟩
      apply hf
      rw [← h2]
      simp
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.degree_eq_sum]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply h
    refine ⟨h1.symm.trans h2, ?_⟩
    rw [← h2, Finsupp.degree_eq_sum]
    have h3 := (Finset.mem_piAntidiag.1 hf).1
    simpa using h3

/- English proof (translation)
Introduce `K _ _ k d`. Apply `pol_ext` to reduce the goal to its premises. Introduce `m g`. Rewrite using `[coeff_kappa, Module.End.one_apply, mono_val, coeff_smul, smul_eq_mul, coeff_sumElim_tt_pow]`. Distinguish the cases in `h : m = g ∧ g.degree = d`.

Take `⟨hmg, hd⟩` from `h`. Rewrite using `[if_pos hd, if_pos ⟨hmg, hd⟩, coeff_monomial, if_pos hmg.symm, mul_one]`. Establish `hspec` using `Nat.multinomial_spec (Finset.univ : Finset (Fin k)) ⇑g`. Establish `hsum : ∑ i, g i = d` using `by rw [← hd, Finsupp.degree_eq_sum]`. Rewrite `hspec` using `[hsum]`.

Establish `hcast : ((d.factorial : ℕ) : K) = (∏ i, ((g i).factorial : K)) * (Nat.multinomial Finset.univ ⇑g : K)`. Conclude with `hspec.symm` after adjusting the coercions. Establish `hM : (Nat.multinomial Finset.univ ⇑g : K) ≠ 0`. Introduce `h0`. Rewrite `hcast` using `[h0, mul_zero]`.

Conclude with `(Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)) hcast`. Unfold `invFact`. Rewrite using `[prodFact_fintype, hcast, mul_inv, mul_assoc, inv_mul_cancel₀ hM, mul_one]`. Rewrite using `[if_neg h, mul_zero] split_ifs with hd`. Rewrite using `[coeff_monomial, if_neg (fun hgm => h ⟨hgm.symm, hd⟩), mul_zero]`.

Rewrite using `[coeff_zero, mul_zero]`.
-/
theorem symbolMapOne : KappaId := by
  intro K _ _ k d
  apply pol_ext
  intro m g
  rw [coeff_kappa, Module.End.one_apply, mono_val, coeff_smul, smul_eq_mul, coeff_sumElim_tt_pow]
  by_cases h : m = g ∧ g.degree = d
  · obtain ⟨hmg, hd⟩ := h
    rw [if_pos hd, if_pos ⟨hmg, hd⟩, coeff_monomial, if_pos hmg.symm, mul_one]
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin k)) ⇑g
    have hsum : ∑ i, g i = d := by rw [← hd, Finsupp.degree_eq_sum]
    rw [hsum] at hspec
    have hcast : ((d.factorial : ℕ) : K) =
        (∏ i, ((g i).factorial : K)) * (Nat.multinomial Finset.univ ⇑g : K) := by
      exact_mod_cast hspec.symm
    have hM : (Nat.multinomial Finset.univ ⇑g : K) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcast
      exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)) hcast
    unfold invFact
    rw [prodFact_fintype, hcast, mul_inv, mul_assoc, inv_mul_cancel₀ hM, mul_one]
  · rw [if_neg h, mul_zero]
    split_ifs with hd
    · rw [coeff_monomial, if_neg (fun hgm => h ⟨hgm.symm, hd⟩), mul_zero]
    · rw [coeff_zero, mul_zero]

end PI.OpWords
