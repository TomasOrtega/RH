import Formalism.SharpRestriction.GrowthBounds.RootWeights.PadicGeMulNat

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => intro f j`. Simplify using the standard rewrite rules. Consider the case `succ l ih`. Introduce `f j`.

Establish `e : f * (X ^ P + C (p : ℤ) * h) ^ (l + 1) = X ^ P * (f * (X ^ P + C (p : ℤ) * h) ^ l) + C (p : ℤ) * ((f * h) * (X ^ P + C (p : ℤ) * h) ^ l)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, coeff_add, coeff_X_pow_mul', coeff_C_mul]`. Use `dvd_add ?_ ?_` and prove the remaining obligations. Use `split_ifs with hj`.

Take `⟨q, rfl⟩ : ∃ q, j = q + P` from `⟨j - P, by omega⟩`. Rewrite using `[Nat.add_sub_cancel, Nat.add_div_right _ hP]`. Conclude with `dvd_trans (pow_dvd_pow _ (by omega)) (ih f q)`. Conclude with `dvd_zero _`. Use `dvd_trans (pow_dvd_pow _ (show l + 1 - j / P ≤ l - j / P + 1 by omega)) ?_` and prove the remaining obligations.

Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left _ (ih (f * h) j)`.
-/
theorem coeff_binomial_power_divisibility (p P : ℕ) (hP : 0 < P) (h : ℤ[X]) (l : ℕ) : ∀ (f : ℤ[X]) (j : ℕ),
    (p : ℤ) ^ (l - j / P) ∣ (f * (X ^ P + C (p : ℤ) * h) ^ l).coeff j := by
  induction l with
  | zero => intro f j; simp
  | succ l ih =>
    intro f j
    have e : f * (X ^ P + C (p : ℤ) * h) ^ (l + 1) =
        X ^ P * (f * (X ^ P + C (p : ℤ) * h) ^ l) + C (p : ℤ) * ((f * h) * (X ^ P + C (p : ℤ) * h) ^ l) := by
      ring
    rw [e, coeff_add, coeff_X_pow_mul', coeff_C_mul]
    refine dvd_add ?_ ?_
    · split_ifs with hj
      · obtain ⟨q, rfl⟩ : ∃ q, j = q + P := ⟨j - P, by omega⟩
        rw [Nat.add_sub_cancel, Nat.add_div_right _ hP]
        exact dvd_trans (pow_dvd_pow _ (by omega)) (ih f q)
      · exact dvd_zero _
    · refine dvd_trans (pow_dvd_pow _ (show l + 1 - j / P ≤ l - j / P + 1 by omega)) ?_
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih (f * h) j)

def binomialExpansionCoeff (P rho M l : ℕ) : ℤ := (((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l : ℤ[X])).coeff M

/- English proof (translation)
Establish `hP : 0 < p ^ t` using `pow_pos hp.pos t`. Choose the witnesses or unpack the hypotheses as in `⟨h, hh⟩ : ∃ h : ℤ[X], (1 + X) ^ (p ^ t) - 1 = X ^ (p ^ t) + C (p : ℤ) * h := by`. Establish `hd : C (p : ℤ) ∣ ((1 + X) ^ (p ^ t) - 1 - X ^ (p ^ t) : ℤ[X])`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`.

Simplify using `only [coeff_sub, coeff_one_add_X_pow, coeff_one, coeff_X_pow]`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Simplify using `[hP.ne']`. Rewrite using `[if_neg (ne_of_lt hP)]`. Conclude with `dvd_zero _`.

Distinguish the cases in `hiP : i = p ^ t`. Substitute `hiP` using the available equality. Simplify using `[hP.ne']`. Rewrite using `[if_neg (by simp [hp.ne_zero])]`. Conclude with `dvd_zero _`.

Distinguish the cases in `hlt : i < p ^ t`. Establish `hdv` using `hp.dvd_choose_pow hi.ne' hiP`. Simplify using `only [if_neg hi.ne', if_neg hiP, sub_zero]`. Conclude with `hdv` after adjusting the coercions. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega)]`.

Simplify using `[hi.ne', hiP]`. Take `⟨h, hh⟩` from `hd`. Conclude with `⟨h, by rw [← hh]; ring⟩`. Unfold `binomialExpansionCoeff`. Rewrite using `[hh]`.

Conclude with `coeff_binomial_power_divisibility p (p ^ t) hP h l _ M`.
-/
theorem binomial_expansion_coeff_padic_dvd (p t : ℕ) (hp : p.Prime) (rho M l : ℕ) :
    (p : ℤ) ^ (l - M / p ^ t) ∣ binomialExpansionCoeff (p ^ t) rho M l := by
  have hP : 0 < p ^ t := pow_pos hp.pos t

  obtain ⟨h, hh⟩ : ∃ h : ℤ[X], (1 + X) ^ (p ^ t) - 1 = X ^ (p ^ t) + C (p : ℤ) * h := by
    have hd : C (p : ℤ) ∣ ((1 + X) ^ (p ^ t) - 1 - X ^ (p ^ t) : ℤ[X]) := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      simp only [coeff_sub, coeff_one_add_X_pow, coeff_one, coeff_X_pow]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [hP.ne']
        rw [if_neg (ne_of_lt hP)]
        exact dvd_zero _
      · by_cases hiP : i = p ^ t
        · subst hiP
          simp [hP.ne']
          rw [if_neg (by simp [hp.ne_zero])]
          exact dvd_zero _
        · by_cases hlt : i < p ^ t
          · have hdv := hp.dvd_choose_pow hi.ne' hiP
            simp only [if_neg hi.ne', if_neg hiP, sub_zero]
            exact_mod_cast hdv
          · rw [Nat.choose_eq_zero_of_lt (by omega)]
            simp [hi.ne', hiP]
    obtain ⟨h, hh⟩ := hd
    exact ⟨h, by rw [← hh]; ring⟩
  unfold binomialExpansionCoeff
  rw [hh]
  exact coeff_binomial_power_divisibility p (p ^ t) hP h l _ M

/- English proof (translation)
Unfold `binomialExpansionCoeff`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : X ∣ ((1 + X) ^ P - 1 : ℤ[X]) := by`. Rewrite using `[X_dvd_iff]`. Simplify using `[coeff_one_add_X_pow]`. Rewrite using `[hq, mul_pow, show (1 + X : ℤ[X]) ^ rho * (X ^ l * q ^ l) = X ^ l * ((1 + X) ^ rho * q ^ l) by ring, coeff_X_pow_mul', if_neg (by omega)]`.
-/
theorem binomial_expansion_coeff_zero_of_gt (P rho M l : ℕ) (h : M < l) : binomialExpansionCoeff P rho M l = 0 := by
  unfold binomialExpansionCoeff
  obtain ⟨q, hq⟩ : X ∣ ((1 + X) ^ P - 1 : ℤ[X]) := by
    rw [X_dvd_iff]
    simp [coeff_one_add_X_pow]
  rw [hq, mul_pow, show (1 + X : ℤ[X]) ^ rho * (X ^ l * q ^ l) = X ^ l * ((1 + X) ^ rho * q ^ l) by ring,
    coeff_X_pow_mul', if_neg (by omega)]

/- English proof (translation)
Unfold `binomialExpansionCoeff`. Apply `coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises. Use `lt_of_le_of_lt ?_ h` and prove the remaining obligations. Establish `h1 : ((1 + X : ℤ[X])).natDegree ≤ 1` using `(natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)`. Establish `h2 : ((1 + X : ℤ[X]) ^ P - 1).natDegree ≤ P`.

Use `(natDegree_sub_le _ _).trans (max_le ?_ (by simp))` and prove the remaining obligations. Conclude with `natDegree_pow_le.trans ((Nat.mul_le_mul_left P h1).trans (by simp))`. Use `natDegree_mul_le.trans (add_le_add ?_ ?_)` and prove the remaining obligations. Conclude with `natDegree_pow_le.trans ((Nat.mul_le_mul_left rho h1).trans (by simp))`. Conclude with `natDegree_pow_le.trans ((Nat.mul_le_mul_left l h2).trans (le_of_eq (mul_comm _ _)))`.
-/
theorem binomial_expansion_coeff_zero_of_deg (P rho M l : ℕ) (h : rho + P * l < M) : binomialExpansionCoeff P rho M l = 0 := by
  unfold binomialExpansionCoeff
  apply coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt ?_ h
  have h1 : ((1 + X : ℤ[X])).natDegree ≤ 1 := (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
  have h2 : ((1 + X : ℤ[X]) ^ P - 1).natDegree ≤ P := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    exact natDegree_pow_le.trans ((Nat.mul_le_mul_left P h1).trans (by simp))
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · exact natDegree_pow_le.trans ((Nat.mul_le_mul_left rho h1).trans (by simp))
  · exact natDegree_pow_le.trans ((Nat.mul_le_mul_left l h2).trans (le_of_eq (mul_comm _ _)))

/- English proof (translation)
Establish `hpoly : ((1 + X : ℤ[X])) ^ (rho + P * e) = ∑ l ∈ range (e + 1), C ((e.choose l : ℕ) : ℤ) * ((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l)`. Rewrite using `[pow_add, pow_mul, show ((1 + X : ℤ[X]) ^ P) = ((1 + X) ^ P - 1) + 1 by ring, add_pow ((1 + X : ℤ[X]) ^ P - 1) 1 e, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[one_pow, mul_one, C_eq_natCast, add_sub_cancel_right]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc` using `congrArg (fun q : ℤ[X] => q.coeff M) hpoly`. Simplify using `only [coeff_one_add_X_pow, finset_sum_coeff, coeff_C_mul] at hc`. Rewrite using `[hc]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)` and prove the remaining obligations.

Simplify using `only [Finset.mem_range] at hl hn`. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega)]`. Simplify using the standard rewrite rules. Use `_ = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by`. Use `(Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)).symm` and prove the remaining obligations.

Simplify using `only [Finset.mem_range] at hl hn`. Rewrite using `[binomial_expansion_coeff_zero_of_gt P rho M l (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem choose_shift_binomial_expansion (P rho M e : ℕ) :
    (((rho + P * e).choose M : ℕ) : ℤ) = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by

  have hpoly : ((1 + X : ℤ[X])) ^ (rho + P * e) =
      ∑ l ∈ range (e + 1), C ((e.choose l : ℕ) : ℤ) * ((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l) := by
    rw [pow_add, pow_mul, show ((1 + X : ℤ[X]) ^ P) = ((1 + X) ^ P - 1) + 1 by ring,
      add_pow ((1 + X : ℤ[X]) ^ P - 1) 1 e, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [one_pow, mul_one, C_eq_natCast, add_sub_cancel_right]
    ring
  have hc := congrArg (fun q : ℤ[X] => q.coeff M) hpoly
  simp only [coeff_one_add_X_pow, finset_sum_coeff, coeff_C_mul] at hc
  rw [hc]
  calc ∑ l ∈ range (e + 1), ((e.choose l : ℕ) : ℤ) * ((1 + X : ℤ[X]) ^ rho * ((1 + X) ^ P - 1) ^ l).coeff M
      = ∑ l ∈ range (e + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) :=
        Finset.sum_congr rfl (fun l _ => by rw [mul_comm]; rfl)
    _ = ∑ l ∈ range (e + M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)
        simp only [Finset.mem_range] at hl hn
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    _ = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)).symm
        simp only [Finset.mem_range] at hl hn
        rw [binomial_expansion_coeff_zero_of_gt P rho M l (by omega)]
        simp

/- English proof (translation)
Introduce `p hp _ t σ _ rho M _ c`. Establish `hP : 0 < p ^ t` using `pow_pos hp.pos t`. Set `a : σ → ℕ → ℤ` to `fun k l => binomialExpansionCoeff (p ^ t) (rho k) (M k) l`. Set `good : (σ → ℕ) → Prop` to `fun l => (∀ k, M k ≤ rho k + p ^ t * l k) ∧ ∑ k, (l k - M k / p ^ t) < c`. Set `B : Finset (σ → ℕ)` to `Fintype.piFinset (fun k => range (M k + 1))`.

Use `⟨B.filter good, fun l => ∏ k, a k (l k), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl`. Establish `hl'` using `(Finset.mem_filter.1 hl).2.2`. Establish `h1 : ∑ k, l k ≤ ∑ k, (l k - M k / p ^ t) + ∑ k, M k / p ^ t`. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_le_sum (fun k _ => le_tsub_add)`. Establish `h2 : (∑ k, M k / p ^ t) ≤ (∑ k, M k) / p ^ t`. Rewrite using `[Nat.le_div_iff_mul_le hP, Finset.sum_mul]`. Conclude with `Finset.sum_le_sum (fun k _ => Nat.div_mul_le_self _ _)`. Establish `h3 : ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) ≤ ((∑ k, M k : ℕ) : ℝ) / ((p ^ t : ℕ) : ℝ)` using `Nat.cast_div_le`.

Establish `h4 : ∑ k, l k ≤ c + (∑ k, M k) / p ^ t` using `by omega`. Establish `h5 : ((∑ k, l k : ℕ) : ℝ) ≤ (c : ℝ) + ((((∑ k, M k) / p ^ t : ℕ)) : ℝ)` using `by exact_mod_cast h4`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `l hl k`. Conclude with `(Finset.mem_filter.1 hl).2.1 k`.

Introduce `e'`. Establish `hexp : ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) = ∑ l ∈ B, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ))`. Combine the equalities or inequalities in the displayed calculation. Establish `hT : ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ) = ∑ l ∈ B.filter good, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ))` using `Finset.sum_congr rfl (fun l _ => Finset.prod_mul_distrib.symm)`. Establish `hsplit` using `Finset.sum_filter_add_sum_filter_not B good (fun l => ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)))`.

Use `show (p : ℤ) ^ c ∣ ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) - ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ)`. Rewrite using `[hexp, hT, ← hsplit, add_sub_cancel_left]`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `l hl`. Establish `hng` using `(Finset.mem_filter.1 hl).2`.

Rewrite using `[Finset.prod_mul_distrib]`. Apply `Dvd.dvd.mul_right` to reduce the goal to its premises. Distinguish the cases in `hdeg : ∀ k, M k ≤ rho k + p ^ t * l k`. Establish `hc : c ≤ ∑ k, (l k - M k / p ^ t)`. Assume the negation of the conclusion as `hh`.

Conclude with `hng ⟨hdeg, by omega⟩`. Use `dvd_trans (pow_dvd_pow _ hc) ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Conclude with `Finset.prod_dvd_prod_of_dvd _ _ (fun k _ => binomial_expansion_coeff_padic_dvd p t hp (rho k) (M k) (l k))`. Use `push_neg at hdeg`.

Take `⟨k, hk⟩` from `hdeg`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ k) (binomial_expansion_coeff_zero_of_deg (p ^ t) (rho k) (M k) (l k) hk)]`. Conclude with `dvd_zero _`.
-/
theorem derivative_digit_expansion (D : Formalism.BasicNotions.D7) : DerivativeDigitExpansion D := by
  intro p hp _ t σ _ rho M _ c
  classical
  have hP : 0 < p ^ t := pow_pos hp.pos t
  let a : σ → ℕ → ℤ := fun k l => binomialExpansionCoeff (p ^ t) (rho k) (M k) l

  let good : (σ → ℕ) → Prop := fun l => (∀ k, M k ≤ rho k + p ^ t * l k) ∧ ∑ k, (l k - M k / p ^ t) < c
  let B : Finset (σ → ℕ) := Fintype.piFinset (fun k => range (M k + 1))
  refine ⟨B.filter good, fun l => ∏ k, a k (l k), ?_, ?_, ?_⟩
  · intro l hl
    have hl' := (Finset.mem_filter.1 hl).2.2
    have h1 : ∑ k, l k ≤ ∑ k, (l k - M k / p ^ t) + ∑ k, M k / p ^ t := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun k _ => le_tsub_add)
    have h2 : (∑ k, M k / p ^ t) ≤ (∑ k, M k) / p ^ t := by
      rw [Nat.le_div_iff_mul_le hP, Finset.sum_mul]
      exact Finset.sum_le_sum (fun k _ => Nat.div_mul_le_self _ _)
    have h3 : ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) ≤ ((∑ k, M k : ℕ) : ℝ) / ((p ^ t : ℕ) : ℝ) := Nat.cast_div_le
    have h4 : ∑ k, l k ≤ c + (∑ k, M k) / p ^ t := by omega
    have h5 : ((∑ k, l k : ℕ) : ℝ) ≤ (c : ℝ) + ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) := by exact_mod_cast h4
    linarith
  · intro l hl k
    exact (Finset.mem_filter.1 hl).2.1 k
  · intro e'
    have hexp : ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) =
        ∑ l ∈ B, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)) := by
      calc ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ)
          = ∏ k, ∑ j ∈ range (M k + 1), a k j * (((e' k).choose j : ℕ) : ℤ) :=
            Finset.prod_congr rfl (fun k _ => choose_shift_binomial_expansion (p ^ t) (rho k) (M k) (e' k))
        _ = _ := Finset.prod_univ_sum _ _
    have hT : ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ) =
        ∑ l ∈ B.filter good, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun l _ => Finset.prod_mul_distrib.symm)
    have hsplit := Finset.sum_filter_add_sum_filter_not B good
      (fun l => ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)))
    show (p : ℤ) ^ c ∣ ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) -
      ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ)
    rw [hexp, hT, ← hsplit, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro l hl
    have hng := (Finset.mem_filter.1 hl).2
    rw [Finset.prod_mul_distrib]
    apply Dvd.dvd.mul_right
    by_cases hdeg : ∀ k, M k ≤ rho k + p ^ t * l k
    · have hc : c ≤ ∑ k, (l k - M k / p ^ t) := by
        by_contra hh
        exact hng ⟨hdeg, by omega⟩
      refine dvd_trans (pow_dvd_pow _ hc) ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun k _ => binomial_expansion_coeff_padic_dvd p t hp (rho k) (M k) (l k))
    · push_neg at hdeg
      obtain ⟨k, hk⟩ := hdeg
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (binomial_expansion_coeff_zero_of_deg (p ^ t) (rho k) (M k) (l k) hk)]
      exact dvd_zero _

/- English proof (translation)
Proceed by induction on `rho with`. Consider the case `zero => simp [dUnit]`. Consider the case `succ r ih => show (∏ y ∈ Finset.Icc 1 (r + 1), (1 + (P : ℚ) * n / y)) = _`. Rewrite using `[Finset.prod_Icc_succ_top (by omega)]`. Establish `ih' : (∏ y ∈ Finset.Icc 1 r, (1 + (P : ℚ) * n / y)) = (((r + P * n).choose r : ℕ) : ℚ)` using `ih`.

Rewrite using `[ih', show r + 1 + P * n = r + P * n + 1 by ring]`. Establish `hc : (((r + P * n + 1 : ℕ) : ℚ)) * (((r + P * n).choose r : ℕ) : ℚ) = (((r + P * n + 1).choose (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1)`. Conclude with `Nat.add_one_mul_choose_eq (r + P * n) r` after adjusting the coercions. Establish `hr : ((r : ℚ) + 1) ≠ 0` using `by positivity`. Move the coercions through the operations in `at hc ⊢`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hc`.
-/
theorem unit_product_eq_choose (P n rho : ℕ) : dUnit P n rho = (((rho + P * n).choose rho : ℕ) : ℚ) := by
  induction rho with
  | zero => simp [dUnit]
  | succ r ih =>
    show (∏ y ∈ Finset.Icc 1 (r + 1), (1 + (P : ℚ) * n / y)) = _
    rw [Finset.prod_Icc_succ_top (by omega)]
    have ih' : (∏ y ∈ Finset.Icc 1 r, (1 + (P : ℚ) * n / y)) = (((r + P * n).choose r : ℕ) : ℚ) := ih
    rw [ih', show r + 1 + P * n = r + P * n + 1 by ring]

    have hc : (((r + P * n + 1 : ℕ) : ℚ)) * (((r + P * n).choose r : ℕ) : ℚ) =
        (((r + P * n + 1).choose (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (r + P * n) r
    have hr : ((r : ℚ) + 1) ≠ 0 := by positivity
    push_cast at hc ⊢
    field_simp
    linear_combination hc

/- English proof (translation)
Introduce `t rho hrho`. Use `⟨fun l => binomialExpansionCoeff (p ^ (t + 1)) rho rho l, fun n => ?_, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[unit_product_eq_choose]`. Conclude with `choose_shift_binomial_expansion (p ^ (t + 1)) rho rho n` after adjusting the coercions. Establish `h` using `binomial_expansion_coeff_padic_dvd p (t + 1) hp rho rho l`.

Rewrite `h` using `[Nat.div_eq_of_lt hrho, Nat.sub_zero]`. Conclude with `h`.
-/
theorem hdU_proved {p : ℕ} (hp : p.Prime) : HdU p := by
  intro t rho hrho
  refine ⟨fun l => binomialExpansionCoeff (p ^ (t + 1)) rho rho l, fun n => ?_, fun l => ?_⟩
  · rw [unit_product_eq_choose]
    exact_mod_cast choose_shift_binomial_expansion (p ^ (t + 1)) rho rho n
  · have h := binomial_expansion_coeff_padic_dvd p (t + 1) hp rho rho l
    rw [Nat.div_eq_of_lt hrho, Nat.sub_zero] at h
    exact h

end Formalism.MainNotions.G.GLWeightTheory
