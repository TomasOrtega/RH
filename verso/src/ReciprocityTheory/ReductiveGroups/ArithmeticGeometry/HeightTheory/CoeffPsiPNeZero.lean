import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution

namespace ReciprocityTheory.ChartRestriction.G.T0.WH

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]

def wt (s : σ →₀ ℕ) : ℕ := ∑ v, if p v then s v else 0

/- English proof (translation)
Simplify using `only [wt, Finsupp.coe_add, Pi.add_apply]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem wt_add (s t : σ →₀ ℕ) : wt p (s + t) = wt p s + wt p t := by
  simp only [wt, Finsupp.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [wt]`. Rewrite using `[Finset.sum_eq_single v]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Finsupp.single_apply, Ne.symm hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ v) h`.
-/
theorem wt_single (v : σ) (e : ℕ) : wt p (Finsupp.single v e) = if p v then e else 0 := by
  simp only [wt]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Finsupp.single_apply, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ v) h

noncomputable def psiP : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun v => if p v then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

/- English proof (translation)
Establish `key : ∀ v, (if p v then Polynomial.C (X v : MvPolynomial σ K) * Polynomial.X else Polynomial.C (X v)) ^ (s v) = Polynomial.C ((X v : MvPolynomial σ K) ^ s v) * Polynomial.X ^ (if p v then s v else 0)`. Introduce `v`. Apply the tactic sequence `split_ifs <;> simp [mul_pow]`. Rewrite using `[psiP, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finset.prod_congr rfl (fun v _ => key v), Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul, wt]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem psiP_monomial (s : σ →₀ ℕ) (a : K) :
    psiP p (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ wt p s := by
  have key : ∀ v, (if p v then Polynomial.C (X v : MvPolynomial σ K) * Polynomial.X
      else Polynomial.C (X v)) ^ (s v)
      = Polynomial.C ((X v : MvPolynomial σ K) ^ s v) * Polynomial.X ^ (if p v then s v else 0) := by
    intro v
    split_ifs <;> simp [mul_pow]
  rw [psiP, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finset.prod_congr rfl (fun v _ => key v), Finset.prod_mul_distrib, ← map_prod,
    Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul, wt]
  ring

/- English proof (translation)
Establish `h : ∀ s ∈ f.support, psiP p (monomial s (coeff s f)) = Polynomial.C (monomial s (coeff s f)) * Polynomial.X ^ n` using `fun s hs => by`. Rewrite using `[psiP_monomial, hf s hs]`. Use `conv_lhs => rw [f.as_sum]`. Rewrite using `[map_sum, Finset.sum_congr rfl h, ← Finset.sum_mul, ← map_sum, ← f.as_sum]`.
-/
theorem psiP_eq_of_isWeightedHomogeneous (n : ℕ) (f : MvPolynomial σ K) (hf : ∀ s ∈ f.support, wt p s = n) :
    psiP p f = Polynomial.C f * Polynomial.X ^ n := by
  have h : ∀ s ∈ f.support, psiP p (monomial s (coeff s f))
      = Polynomial.C (monomial s (coeff s f)) * Polynomial.X ^ n := fun s hs => by
    rw [psiP_monomial, hf s hs]
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Finset.sum_congr rfl h, ← Finset.sum_mul, ← map_sum, ← f.as_sum]

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Rewrite using `[map_sum]`. Simplify using `only [psiP_monomial]`.
-/
private theorem psiP_eq_sum_monomial (f : MvPolynomial σ K) :
    psiP p f = ∑ s ∈ f.support, Polynomial.C (monomial s (coeff s f)) * Polynomial.X ^ wt p s := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  simp only [psiP_monomial]

/- English proof (translation)
Rewrite using `[psiP_eq_sum_monomial, Polynomial.finset_sum_coeff, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_C_mul_X_pow]`. Distinguish the cases in `h : wt p s = k`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h]`.
-/
private theorem coeff_psiP (f : MvPolynomial σ K) (k : ℕ) :
    (psiP p f).coeff k = ∑ s ∈ f.support.filter (fun s => wt p s = k), monomial s (coeff s f) := by
  rw [psiP_eq_sum_monomial, Polynomial.finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : wt p s = k
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg (MvPolynomial.coeff s) h`. Rewrite `h'` using `[coeff_psiP, MvPolynomial.coeff_sum, Finset.sum_eq_single s]`. Rewrite `h'` using `[coeff_monomial, if_pos rfl, coeff_zero]`. Conclude with `(mem_support_iff.mp hs) h'`.

Introduce `t _ hts`. Rewrite using `[coeff_monomial, if_neg hts]`. Introduce `hn`. Conclude with `(hn (Finset.mem_filter.mpr ⟨hs, rfl⟩)).elim`.
-/
theorem coeff_psiP_ne_zero (f : MvPolynomial σ K) (s : σ →₀ ℕ) (hs : s ∈ f.support) :
    (psiP p f).coeff (wt p s) ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.coeff s) h
  rw [coeff_psiP, MvPolynomial.coeff_sum, Finset.sum_eq_single s] at h'
  · classical
    rw [coeff_monomial, if_pos rfl, coeff_zero] at h'
    exact (mem_support_iff.mp hs) h'
  · classical
    intro t _ hts
    rw [coeff_monomial, if_neg hts]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨hs, rfl⟩)).elim

/- English proof (translation)
Introduce `s hs`. Assume the negation of the conclusion as `hne`. Apply `coeff_psiP_ne_zero p f s hs` to reduce the goal to its premises. Rewrite using `[hf, Polynomial.coeff_C_mul_X_pow, if_neg hne]`.
-/
theorem hom_of_psiP (n : ℕ) (f : MvPolynomial σ K) (hf : psiP p f = Polynomial.C f * Polynomial.X ^ n) :
    ∀ s ∈ f.support, wt p s = n := by
  intro s hs
  by_contra hne
  apply coeff_psiP_ne_zero p f s hs
  rw [hf, Polynomial.coeff_C_mul_X_pow, if_neg hne]

/- English proof (translation)
Take `⟨B, rfl⟩` from `hA`. Establish `hA0 : A ≠ 0` using `left_ne_zero_of_mul hH0`. Establish `hB0 : B ≠ 0` using `right_ne_zero_of_mul hH0`. Establish `hne : ∀ F : MvPolynomial σ K, F ≠ 0 → psiP p F ≠ 0`. Introduce `F hF h0`.

Take `⟨s, hs⟩` from `MvPolynomial.ne_zero_iff.mp hF`. Conclude with `coeff_psiP_ne_zero p F s (mem_support_iff.mpr hs) (by rw [h0, Polynomial.coeff_zero])`. Establish `hprod : psiP p A * psiP p B = Polynomial.C (A * B) * Polynomial.X ^ n`. Rewrite using `[← map_mul]`. Conclude with `psiP_eq_of_isWeightedHomogeneous p n _ hH`.

Establish `hd` using `congrArg Polynomial.natDegree hprod`. Establish `ht` using `congrArg Polynomial.natTrailingDegree hprod`. Rewrite `hd` using `[Polynomial.natDegree_mul (hne A hA0) (hne B hB0), Polynomial.natDegree_C_mul_X_pow _ _ hH0]`. Rewrite `ht` using `[Polynomial.natTrailingDegree_mul (hne A hA0) (hne B hB0), Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hH0]`. Establish `h1` using `Polynomial.natTrailingDegree_le_natDegree (p := psiP p A)`.

Establish `h2` using `Polynomial.natTrailingDegree_le_natDegree (p := psiP p B)`. Use `⟨(psiP p A).natDegree, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hc` using `coeff_psiP_ne_zero p A s hs`. Establish `h3` using `Polynomial.le_natDegree_of_ne_zero hc`. Establish `h4` using `Polynomial.natTrailingDegree_le_of_ne_zero hc`.

Use linear arithmetic over natural numbers and integers.
-/
theorem hom_of_dvd (n : ℕ) (H A : MvPolynomial σ K) (hH0 : H ≠ 0)
    (hH : ∀ s ∈ H.support, wt p s = n) (hA : A ∣ H) : ∃ m, ∀ s ∈ A.support, wt p s = m := by
  obtain ⟨B, rfl⟩ := hA
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hH0
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hH0
  have hne : ∀ F : MvPolynomial σ K, F ≠ 0 → psiP p F ≠ 0 := by
    intro F hF h0
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hF
    exact coeff_psiP_ne_zero p F s (mem_support_iff.mpr hs) (by rw [h0, Polynomial.coeff_zero])
  have hprod : psiP p A * psiP p B = Polynomial.C (A * B) * Polynomial.X ^ n := by
    rw [← map_mul]
    exact psiP_eq_of_isWeightedHomogeneous p n _ hH
  have hd := congrArg Polynomial.natDegree hprod
  have ht := congrArg Polynomial.natTrailingDegree hprod
  rw [Polynomial.natDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.natDegree_C_mul_X_pow _ _ hH0] at hd
  rw [Polynomial.natTrailingDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hH0] at ht
  have h1 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p A)
  have h2 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p B)
  refine ⟨(psiP p A).natDegree, fun s hs => ?_⟩
  have hc := coeff_psiP_ne_zero p A s hs
  have h3 := Polynomial.le_natDegree_of_ne_zero hc
  have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
  omega

end ReciprocityTheory.ChartRestriction.G.T0.WH
