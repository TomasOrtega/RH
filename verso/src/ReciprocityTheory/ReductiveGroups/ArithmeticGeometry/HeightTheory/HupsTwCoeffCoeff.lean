import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UpMkApplyInl

namespace ReciprocityTheory.ChartRestriction.G.T0

open Polynomial in

noncomputable def hupsTw {σ R : Type*} [CommRing R] (w : σ → ℕ) :
    MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  MvPolynomial.aeval fun v => Polynomial.C (MvPolynomial.X v) * Polynomial.X ^ (w v)

def hupsWt {σ : Type*} (w : σ → ℕ) (s : σ →₀ ℕ) : ℕ := s.sum fun v k => k * w v

/- English proof (translation)
Rewrite using `[hupsTw, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]`. Simplify using `only [mul_pow, Finsupp.prod_mul, hupsWt, Finsupp.prod, Finsupp.sum, ← pow_mul, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`. Simplify using `only [mul_comm (w _) _]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hupsTw_monomial {σ R : Type*} [CommRing R] (w : σ → ℕ) (s : σ →₀ ℕ) (a : R) :
    hupsTw w (MvPolynomial.monomial s a) =
      Polynomial.C (MvPolynomial.monomial s a) * Polynomial.X ^ hupsWt w s := by
  rw [hupsTw, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, hupsWt, Finsupp.prod, Finsupp.sum, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  simp only [mul_comm (w _) _]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/- English proof (translation)
Use `conv_lhs => rw [p.as_sum]`. Rewrite using `[map_sum]`. Simplify using `only [hupsTw_monomial]`.
-/
theorem hupsTw_eq {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R) :
    hupsTw w p = ∑ s ∈ p.support,
      Polynomial.C (MvPolynomial.monomial s (p.coeff s)) * Polynomial.X ^ hupsWt w s := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [hupsTw_monomial]

/- English proof (translation)
Rewrite using `[hupsTw_eq, Polynomial.finset_sum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [apply_ite (MvPolynomial.coeff s), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]`. Rewrite using `[Finset.sum_eq_single s]`.

Distinguish the cases in `h : hupsWt w s = j`. Rewrite using `[if_pos h.symm, if_pos h, if_pos rfl]`. Simplify using `[h, Ne.symm h]`. Introduce `t _ hts`. Simplify using `[hts, MvPolynomial.coeff_monomial]`.

Introduce `hs`. Rewrite `hs` using `[MvPolynomial.mem_support_iff, not_not]`. Simplify using `[hs]`.
-/
theorem hupsTw_coeff_coeff {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R)
    (j : ℕ) (s : σ →₀ ℕ) :
    ((hupsTw w p).coeff j).coeff s = if hupsWt w s = j then p.coeff s else 0 := by
  classical
  rw [hupsTw_eq, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [MvPolynomial.coeff_sum]
  simp only [apply_ite (MvPolynomial.coeff s), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
  rw [Finset.sum_eq_single s]
  · by_cases h : hupsWt w s = j
    · rw [if_pos h.symm, if_pos h, if_pos rfl]
    · simp [h, Ne.symm h]
  · intro t _ hts
    simp [hts, MvPolynomial.coeff_monomial]
  · intro hs
    rw [MvPolynomial.mem_support_iff, not_not] at hs
    simp [hs]

/- English proof (translation)
Introduce `h`. Establish `e` using `hupsTw_coeff_coeff w p (hupsWt w s) s`. Rewrite `e` using `[h, MvPolynomial.coeff_zero, if_pos rfl]`. Conclude with `(MvPolynomial.mem_support_iff.mp hs) e.symm`.
-/
theorem hupsTw_ne_zero {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R}
    {s : σ →₀ ℕ} (hs : s ∈ p.support) : (hupsTw w p).coeff (hupsWt w s) ≠ 0 := by
  intro h
  have e := hupsTw_coeff_coeff w p (hupsWt w s) s
  rw [h, MvPolynomial.coeff_zero, if_pos rfl] at e
  exact (MvPolynomial.mem_support_iff.mp hs) e.symm

/- English proof (translation)
Use extensionality with `j s`. Rewrite using `[hupsTw_coeff_coeff, Polynomial.coeff_C_mul_X_pow]`. Distinguish the cases in `hs : s ∈ p.support`. Rewrite using `[hp s hs]`. Distinguish the cases in `hj : j = a`.

Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj, Ne.symm hj]`. Apply the tactic sequence `rw [MvPolynomial.mem_support_iff, not_not] at hs split_ifs <;> simp [hs]`.
-/
theorem hupsTw_hom {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R} {a : ℕ}
    (hp : ∀ s ∈ p.support, hupsWt w s = a) :
    hupsTw w p = Polynomial.C p * Polynomial.X ^ a := by
  ext j s
  rw [hupsTw_coeff_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hs : s ∈ p.support
  · rw [hp s hs]
    by_cases hj : j = a
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  · rw [MvPolynomial.mem_support_iff, not_not] at hs
    split_ifs <;> simp [hs]

/- English proof (translation)
Establish `h1 : hupsTw w (F * P) = Polynomial.C (F * P) * Polynomial.X ^ n` using `hupsTw_hom w hFP`. Establish `h2 : hupsTw w F = Polynomial.C F * Polynomial.X ^ a` using `hupsTw_hom w hFa`. Rewrite `h1` using `[map_mul, h2, map_mul]`. Establish `hCF : (Polynomial.C F : Polynomial (MvPolynomial σ R)) ≠ 0` using `Polynomial.C_ne_zero.mpr hF`. Establish `h3 : Polynomial.X ^ a * hupsTw w P = Polynomial.C P * Polynomial.X ^ n`.

Apply `mul_left_cancel₀ hCF` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← mul_assoc]`. Conclude with `h1`. Establish `h4` using `congrArg (fun q => q.coeff (hupsWt w s0 + a)) h3`. Simplify using `only [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C_mul_X_pow] at h4`.

Assume the negation of the conclusion as `hne`. Rewrite `h4` using `[if_neg hne]`. Conclude with `hupsTw_ne_zero w hs0 h4`.
-/
theorem hups_hom_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} (hF : F ≠ 0) {a n : ℕ} (hFa : ∀ s ∈ F.support, hupsWt w s = a)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s = n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + a = n := by
  have h1 : hupsTw w (F * P) = Polynomial.C (F * P) * Polynomial.X ^ n := hupsTw_hom w hFP
  have h2 : hupsTw w F = Polynomial.C F * Polynomial.X ^ a := hupsTw_hom w hFa
  rw [map_mul, h2, map_mul] at h1
  have hCF : (Polynomial.C F : Polynomial (MvPolynomial σ R)) ≠ 0 := Polynomial.C_ne_zero.mpr hF
  have h3 : Polynomial.X ^ a * hupsTw w P = Polynomial.C P * Polynomial.X ^ n := by
    apply mul_left_cancel₀ hCF
    rw [← mul_assoc, ← mul_assoc]
    exact h1
  have h4 := congrArg (fun q => q.coeff (hupsWt w s0 + a)) h3
  simp only [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C_mul_X_pow] at h4
  by_contra hne
  rw [if_neg hne] at h4
  exact hupsTw_ne_zero w hs0 h4

/- English proof (translation)
Establish `hTF : (hupsTw w F).coeff u ≠ 0`. Rewrite using `[← hFu]`. Conclude with `hupsTw_ne_zero w hsF`. Establish `hTP : (hupsTw w P).coeff (hupsWt w s0) ≠ 0` using `hupsTw_ne_zero w hs0`. Establish `hF0 : hupsTw w F ≠ 0` using `fun h => hTF (by rw [h, Polynomial.coeff_zero])`.

Establish `hP0 : hupsTw w P ≠ 0` using `fun h => hTP (by rw [h, Polynomial.coeff_zero])`. Establish `hdeg : (hupsTw w (F * P)).natDegree ≤ n`. Rewrite using `[Polynomial.natDegree_le_iff_coeff_eq_zero]`. Introduce `j hj`. Use extensionality with `s`.

Rewrite using `[hupsTw_coeff_coeff, MvPolynomial.coeff_zero]`. Use `split_ifs with h`. Assume the negation of the conclusion as `hc`. Use `hFP s (MvPolynomial.mem_support_iff.mpr hc)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Both sides reduce to the same expression. Rewrite `hdeg` using `[map_mul, Polynomial.natDegree_mul hF0 hP0]`. Establish `h1` using `Polynomial.le_natDegree_of_ne_zero hTF`. Establish `h2` using `Polynomial.le_natDegree_of_ne_zero hTP`. Use linear arithmetic over natural numbers and integers.
-/
theorem hups_deg_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} {u n : ℕ} {sF : σ →₀ ℕ} (hsF : sF ∈ F.support)
    (hFu : hupsWt w sF = u)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s ≤ n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + u ≤ n := by
  have hTF : (hupsTw w F).coeff u ≠ 0 := by
    rw [← hFu]
    exact hupsTw_ne_zero w hsF
  have hTP : (hupsTw w P).coeff (hupsWt w s0) ≠ 0 := hupsTw_ne_zero w hs0
  have hF0 : hupsTw w F ≠ 0 := fun h => hTF (by rw [h, Polynomial.coeff_zero])
  have hP0 : hupsTw w P ≠ 0 := fun h => hTP (by rw [h, Polynomial.coeff_zero])
  have hdeg : (hupsTw w (F * P)).natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    ext s
    rw [hupsTw_coeff_coeff, MvPolynomial.coeff_zero]
    split_ifs with h
    · by_contra hc
      have := hFP s (MvPolynomial.mem_support_iff.mpr hc)
      omega
    · rfl
  rw [map_mul, Polynomial.natDegree_mul hF0 hP0] at hdeg
  have h1 := Polynomial.le_natDegree_of_ne_zero hTF
  have h2 := Polynomial.le_natDegree_of_ne_zero hTP
  omega

end ReciprocityTheory.ChartRestriction.G.T0
