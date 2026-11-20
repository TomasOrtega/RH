import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Classical

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩

def padExp (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) : (Σ k, ι k) →₀ ℕ :=
  ∑ k, Finsupp.single ⟨k, p k⟩ (T - blkDeg m k)

/- English proof (translation)
Take `⟨k', i'⟩` from `q`. Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single i']`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `e`. Conclude with `hb (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `e`. Conclude with `h (Sigma.mk.inj_iff.1 e).1`.
-/
theorem sum_single_blk (q : Σ k, ι k) (a : ℕ) (k : K) :
    ∑ i, (Finsupp.single q a : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = if q.1 = k then a else 0 := by
  classical
  obtain ⟨k', i'⟩ := q
  by_cases h : k' = k
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i']
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hb (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (Sigma.mk.inj_iff.1 e).1

/- English proof (translation)
Simplify using `only [padExp, Finsupp.coe_finsetSum, Finset.sum_apply]`. Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[Finsupp.single_apply]`. Distinguish the cases in `h : i = p k`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg, if_neg h]`. Introduce `e`. Conclude with `h (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm`. Introduce `b _ hb`.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `e`. Conclude with `hb (Sigma.mk.inj_iff.1 e).1`. Simplify using the standard rewrite rules.
-/
theorem padExp_apply (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) (k : K) (i : ι k) :
    padExp p T m ⟨k, i⟩ = if i = p k then T - blkDeg m k else 0 := by
  classical
  simp only [padExp, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finsupp.single_apply]
    by_cases h : i = p k
    · subst h; simp
    · rw [if_neg, if_neg h]
      intro e
      exact h (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact hb (Sigma.mk.inj_iff.1 e).1
  · simp

/- English proof (translation)
Unfold `blkDeg`. Simplify using `only [padExp_apply]`. Rewrite using `[Finset.sum_eq_single (p k)]`. Simplify using `[blkDeg]`. Introduce `b _ hb`.

Rewrite using `[if_neg hb]`. Simplify using the standard rewrite rules.
-/
theorem blkDeg_padExp (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    blkDeg (padExp p T m) k = T - blkDeg m k := by
  classical
  unfold blkDeg
  simp only [padExp_apply]
  rw [Finset.sum_eq_single (p k)]
  · simp [blkDeg]
  · intro b _ hb; rw [if_neg hb]
  · simp

/- English proof (translation)
Use `le_trans ?_ (le_totalDegree hm)` and prove the remaining obligations. Rewrite using `[Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]`. Conclude with `Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`.
-/
theorem blkDeg_le_totalDegree {Q : MvPolynomial (Σ k, ι k) ℂ} {m : (Σ k, ι k) →₀ ℕ} (hm : m ∈ Q.support)
    (k : K) : blkDeg m k ≤ Q.totalDegree := by
  classical
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  exact Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

/- English proof (translation)
Use `set Q' : MvPolynomial (Σ k, ι k) ℂ := rename (Fintype.equivFin (Σ k, ι k)).symm Q with hQ'`. Establish `hren : ∀ v : (Σ k, ι k) → ℂ, eval (ReciprocityTheory.AnForm.R.renPt v) Q = eval v Q'` using `fun v => by`. Rewrite using `[hQ', eval_rename]`. Use `set T := Q'.totalDegree + 1 with hT`. Establish `hlt : ∀ m ∈ Q'.support, ∀ k, blkDeg m k < T` using `fun m hm k => Nat.lt_succ_of_le (blkDeg_le_totalDegree hm k)`.

Use `⟨∑ m ∈ Q'.support, monomial (m + padExp p T m) (coeff m Q'), T, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n hn k`. Take `⟨m, hm, hn'⟩` from `Finset.mem_biUnion.1 (MvPolynomial.support_sum hn)`. Establish `hn''` using `support_monomial_subset hn'`. Rewrite `hn''` using `[Finset.mem_singleton]`.

Substitute `hn''` using the available equality. Establish `e1 : ∑ i, (m + padExp p T m) ⟨k, i⟩ = blkDeg (m + padExp p T m) k` using `rfl`. Rewrite using `[e1]`. Unfold `blkDeg`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]`.

Use `blkDeg_padExp p T m k` as an intermediate fact. Unfold `blkDeg at this`. Rewrite using `[this]`. Establish `h2` using `(hlt m hm k).le`. Unfold `blkDeg at h2`.

Use linear arithmetic over natural numbers and integers. Introduce `z hz`. Rewrite using `[map_sum]`. Use `conv_rhs => rw [hren, Q'.as_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Rewrite using `[eval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`. Rewrite using `[Fintype.prod_sigma, Fintype.prod_sigma, Fintype.prod_sigma]`. Establish `hpad : ∀ k, ∏ i, z ⟨k, i⟩ ^ padExp p T m ⟨k, i⟩ = z ⟨k, p k⟩ ^ (T - blkDeg m k)` using `fun k => by`. Rewrite using `[Finset.prod_eq_single (p k)]`.

Rewrite using `[padExp_apply, if_pos rfl]`. Introduce `b _ hb`. Rewrite using `[padExp_apply, if_neg hb, pow_zero]`. Simplify using the standard rewrite rules. Simplify using `only [hpad, ReciprocityTheory.AnForm.R.affCoord, div_pow]`.

Establish `hden : ∀ k, ∏ i, z ⟨k, p k⟩ ^ m ⟨k, i⟩ = z ⟨k, p k⟩ ^ blkDeg m k` using `fun k => by`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Both sides reduce to the same expression. Rewrite using `[show (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩ / z ⟨k, p k⟩ ^ m ⟨k, i⟩) = (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩) / ∏ k, z ⟨k, p k⟩ ^ blkDeg m k by`. Rewrite using `[← Finset.prod_div_distrib]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_div_distrib, hden]]`. Establish `hsub : ∀ k, z ⟨k, p k⟩ ^ (T - blkDeg m k) = z ⟨k, p k⟩ ^ T / z ⟨k, p k⟩ ^ blkDeg m k` using `fun k => pow_sub₀ _ (hz k) (hlt m hm k).le`. Simplify using `only [hsub, Finset.prod_div_distrib]`. Establish `h0 : (∏ k, z ⟨k, p k⟩ ^ blkDeg m k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)`.

Clear the denominators using the available nonvanishing facts. Introduce and unpack `z ⟨k, hk⟩`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Rewrite using `[eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`.

Use `mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, p k⟩) ?_)` and prove the remaining obligations. Rewrite using `[hk, Finsupp.coe_add, Pi.add_apply, padExp_apply, if_pos rfl]`. Conclude with `zero_pow (by have := hlt m hm k; omega)`.
-/
theorem exists_homogenize (p : (k : K) → ι k) (Q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :
    ∃ (G : MvPolynomial (Σ k, ι k) ℂ) (T : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G (fun _ => T) ∧
      (∀ z : (Σ k, ι k) → ℂ, (∀ k, z ⟨k, p k⟩ ≠ 0) →
        eval z G = (∏ k, z ⟨k, p k⟩ ^ T) * eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord p z)) Q) ∧
      ∀ z : (Σ k, ι k) → ℂ, (∃ k, z ⟨k, p k⟩ = 0) → eval z G = 0 := by
  classical
  set Q' : MvPolynomial (Σ k, ι k) ℂ := rename (Fintype.equivFin (Σ k, ι k)).symm Q with hQ'
  have hren : ∀ v : (Σ k, ι k) → ℂ, eval (ReciprocityTheory.AnForm.R.renPt v) Q = eval v Q' := fun v => by
    rw [hQ', eval_rename]
  set T := Q'.totalDegree + 1 with hT
  have hlt : ∀ m ∈ Q'.support, ∀ k, blkDeg m k < T := fun m hm k =>
    Nat.lt_succ_of_le (blkDeg_le_totalDegree hm k)
  refine ⟨∑ m ∈ Q'.support, monomial (m + padExp p T m) (coeff m Q'), T, ?_, ?_, ?_⟩
  · intro n hn k
    obtain ⟨m, hm, hn'⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hn)
    have hn'' := support_monomial_subset hn'
    rw [Finset.mem_singleton] at hn''
    subst hn''
    have e1 : ∑ i, (m + padExp p T m) ⟨k, i⟩ = blkDeg (m + padExp p T m) k := rfl
    rw [e1]
    unfold blkDeg
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    have := blkDeg_padExp p T m k
    unfold blkDeg at this
    rw [this]
    have h2 := (hlt m hm k).le
    unfold blkDeg at h2
    omega
  · intro z hz
    rw [map_sum]
    conv_rhs => rw [hren, Q'.as_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [Fintype.prod_sigma, Fintype.prod_sigma, Fintype.prod_sigma]
    have hpad : ∀ k, ∏ i, z ⟨k, i⟩ ^ padExp p T m ⟨k, i⟩ = z ⟨k, p k⟩ ^ (T - blkDeg m k) := fun k => by
      rw [Finset.prod_eq_single (p k)]
      · rw [padExp_apply, if_pos rfl]
      · intro b _ hb; rw [padExp_apply, if_neg hb, pow_zero]
      · simp
    simp only [hpad, ReciprocityTheory.AnForm.R.affCoord, div_pow]
    have hden : ∀ k, ∏ i, z ⟨k, p k⟩ ^ m ⟨k, i⟩ = z ⟨k, p k⟩ ^ blkDeg m k := fun k => by
      rw [Finset.prod_pow_eq_pow_sum]; rfl
    rw [show (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩ / z ⟨k, p k⟩ ^ m ⟨k, i⟩) =
        (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩) / ∏ k, z ⟨k, p k⟩ ^ blkDeg m k by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Finset.prod_div_distrib, hden]]
    have hsub : ∀ k, z ⟨k, p k⟩ ^ (T - blkDeg m k) = z ⟨k, p k⟩ ^ T / z ⟨k, p k⟩ ^ blkDeg m k := fun k =>
      pow_sub₀ _ (hz k) (hlt m hm k).le
    simp only [hsub, Finset.prod_div_distrib]
    have h0 : (∏ k, z ⟨k, p k⟩ ^ blkDeg m k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
    field_simp
  · rintro z ⟨k, hk⟩
    rw [map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, p k⟩) ?_)
    rw [hk, Finsupp.coe_add, Pi.add_apply, padExp_apply, if_pos rfl]
    exact zero_pow (by have := hlt m hm k; omega)

end

end PositivityTheory.Xgp.c_bm_exists_boundary
