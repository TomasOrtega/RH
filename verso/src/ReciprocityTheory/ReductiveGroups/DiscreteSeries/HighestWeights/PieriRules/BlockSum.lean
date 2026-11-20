import Mathlib

namespace ReciprocityTheory.ChartRestriction.DS.HW

open Polynomial Finset

/- English proof (translation)
Establish `h` using `congrArg (fun p : Polynomial ℝ => p.coeff (S.card - 1)) (Lagrange.eq_interpolate hu hF)`. Rewrite using `[h, Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_C_mul, div_eq_mul_inv, ← Finset.prod_inv_distrib]`. Use `congr 1`.

Unfold `Lagrange.basis`. Simplify using `only [Lagrange.basisDivisor]`. Rewrite using `[Finset.prod_mul_distrib, ← map_prod Polynomial.C, Polynomial.coeff_C_mul]`. Establish `hc : S.card - 1 = (S.erase s).card` using `(Finset.card_erase_of_mem hs).symm`. Establish `hm : (∏ b ∈ S.erase s, (X - C (u b))).Monic` using `Polynomial.monic_prod_of_monic _ _ (fun b _ => Polynomial.monic_X_sub_C _)`.

Establish `hd : (∏ b ∈ S.erase s, (X - C (u b))).natDegree = (S.erase s).card` using `Polynomial.natDegree_finset_prod_X_sub_C_eq_card _ _`. Rewrite using `[hc, ← hd, hm.coeff_natDegree, mul_one]`.
-/
private theorem coeff_card_sub_one_eq_sum_eval_div_prod_sub {α : Type*} [DecidableEq α] (S : Finset α) (u : α → ℝ)
    (hu : Set.InjOn u S) (F : Polynomial ℝ) (hF : F.degree < S.card) :
    F.coeff (S.card - 1) = ∑ s ∈ S, F.eval (u s) / ∏ b ∈ S.erase s, (u s - u b) := by
  have h := congrArg (fun p : Polynomial ℝ => p.coeff (S.card - 1)) (Lagrange.eq_interpolate hu hF)
  rw [h, Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Polynomial.coeff_C_mul, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1

  unfold Lagrange.basis
  simp only [Lagrange.basisDivisor]
  rw [Finset.prod_mul_distrib, ← map_prod Polynomial.C, Polynomial.coeff_C_mul]
  have hc : S.card - 1 = (S.erase s).card := (Finset.card_erase_of_mem hs).symm
  have hm : (∏ b ∈ S.erase s, (X - C (u b))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun b _ => Polynomial.monic_X_sub_C _)
  have hd : (∏ b ∈ S.erase s, (X - C (u b))).natDegree = (S.erase s).card :=
    Polynomial.natDegree_finset_prod_X_sub_C_eq_card _ _
  rw [hc, ← hd, hm.coeff_natDegree, mul_one]

/- English proof (translation)
Break down `S.eq_empty_or_nonempty with rfl | hne` into its components or cases. Simplify using the standard rewrite rules. Establish `hpos : 0 < S.card` using `hne.card_pos`. Use `set F : Polynomial ℝ := ∏ b ∈ S, (X - C (u b - c)) - ∏ b ∈ S, (X - C (u b)) with hFdef`. Establish `hm1 : (∏ b ∈ S, (X - C (u b - c))).Monic` using `Polynomial.monic_prod_of_monic _ _ (fun b _ => Polynomial.monic_X_sub_C _)`.

Establish `hm2 : (∏ b ∈ S, (X - C (u b))).Monic` using `Polynomial.monic_prod_of_monic _ _ (fun b _ => Polynomial.monic_X_sub_C _)`. Establish `hd1 : (∏ b ∈ S, (X - C (u b - c))).natDegree = S.card` using `Polynomial.natDegree_finset_prod_X_sub_C_eq_card _ _`. Establish `hd2 : (∏ b ∈ S, (X - C (u b))).natDegree = S.card` using `Polynomial.natDegree_finset_prod_X_sub_C_eq_card _ _`. Establish `hdeg : F.degree < S.card`. Establish `h` using `Polynomial.degree_sub_lt (by rw [Polynomial.degree_eq_natDegree hm1.ne_zero, Polynomial.degree_eq_natDegree hm2.ne_zero, hd1, hd2]) hm1.ne_zero (hm1.leadingCoeff.trans hm2.leadingCoeff.symm)`.

Rewrite `h` using `[Polynomial.degree_eq_natDegree hm1.ne_zero, hd1]`. Then use the resulting hypothesis. Establish `hcoef : F.coeff (S.card - 1) = S.card * c`. Rewrite using `[hFdef, Polynomial.coeff_sub, Polynomial.prod_X_sub_C_coeff_card_pred S _ hpos, Polynomial.prod_X_sub_C_coeff_card_pred S _ hpos, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hev : ∀ s ∈ S, F.eval (u s) = c * ∏ b ∈ S.erase s, (u s - u b + c)`.

Introduce `s hs`. Establish `hsh : ∀ b, u s - (u b - c) = u s - u b + c` using `fun b => by ring`. Simplify using `only [hFdef, Polynomial.eval_sub, Polynomial.eval_prod, Polynomial.eval_X, Polynomial.eval_C]`. Rewrite using `[Finset.prod_eq_zero (f := fun b => u s - u b) hs (sub_self _), sub_zero, ← Finset.mul_prod_erase S (fun b => u s - (u b - c)) hs]`. Simplify using `only [hsh, sub_self, zero_add]`.

Establish `key` using `coeff_card_sub_one_eq_sum_eval_div_prod_sub S u hu F hdeg`. Establish `hsum : ∑ s ∈ S, F.eval (u s) / ∏ b ∈ S.erase s, (u s - u b) = c * ∑ s ∈ S, ∏ b ∈ S.erase s, (u s - u b + c) / (u s - u b)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[hev s hs, Finset.prod_div_distrib, mul_div_assoc]`.

Rewrite `key` using `[hcoef, hsum]`. Conclude with `mul_left_cancel₀ hc (by rw [← key]; ring)`.
-/
private theorem sum_prod_sub_add_div_sub_eq_card {α : Type*} [DecidableEq α] (S : Finset α) (u : α → ℝ)
    (hu : Set.InjOn u S) (c : ℝ) (hc : c ≠ 0) :
    ∑ s ∈ S, ∏ b ∈ S.erase s, (u s - u b + c) / (u s - u b) = #S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hpos : 0 < S.card := hne.card_pos
  set F : Polynomial ℝ := ∏ b ∈ S, (X - C (u b - c)) - ∏ b ∈ S, (X - C (u b)) with hFdef
  have hm1 : (∏ b ∈ S, (X - C (u b - c))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun b _ => Polynomial.monic_X_sub_C _)
  have hm2 : (∏ b ∈ S, (X - C (u b))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun b _ => Polynomial.monic_X_sub_C _)
  have hd1 : (∏ b ∈ S, (X - C (u b - c))).natDegree = S.card :=
    Polynomial.natDegree_finset_prod_X_sub_C_eq_card _ _
  have hd2 : (∏ b ∈ S, (X - C (u b))).natDegree = S.card :=
    Polynomial.natDegree_finset_prod_X_sub_C_eq_card _ _
  have hdeg : F.degree < S.card := by
    have h := Polynomial.degree_sub_lt
      (by rw [Polynomial.degree_eq_natDegree hm1.ne_zero, Polynomial.degree_eq_natDegree hm2.ne_zero, hd1, hd2])
      hm1.ne_zero (hm1.leadingCoeff.trans hm2.leadingCoeff.symm)
    rwa [Polynomial.degree_eq_natDegree hm1.ne_zero, hd1] at h
  have hcoef : F.coeff (S.card - 1) = S.card * c := by
    rw [hFdef, Polynomial.coeff_sub, Polynomial.prod_X_sub_C_coeff_card_pred S _ hpos,
      Polynomial.prod_X_sub_C_coeff_card_pred S _ hpos, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
    ring
  have hev : ∀ s ∈ S, F.eval (u s) = c * ∏ b ∈ S.erase s, (u s - u b + c) := by
    intro s hs
    have hsh : ∀ b, u s - (u b - c) = u s - u b + c := fun b => by ring
    simp only [hFdef, Polynomial.eval_sub, Polynomial.eval_prod, Polynomial.eval_X, Polynomial.eval_C]
    rw [Finset.prod_eq_zero (f := fun b => u s - u b) hs (sub_self _), sub_zero,
      ← Finset.mul_prod_erase S (fun b => u s - (u b - c)) hs]
    simp only [hsh, sub_self, zero_add]
  have key := coeff_card_sub_one_eq_sum_eval_div_prod_sub S u hu F hdeg
  have hsum : ∑ s ∈ S, F.eval (u s) / ∏ b ∈ S.erase s, (u s - u b) =
      c * ∑ s ∈ S, ∏ b ∈ S.erase s, (u s - u b + c) / (u s - u b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hev s hs, Finset.prod_div_distrib, mul_div_assoc]
  rw [hcoef, hsum] at key
  exact mul_left_cancel₀ hc (by rw [← key]; ring)

/- English proof (translation)
Conclude with `sum_prod_sub_add_div_sub_eq_card S u hu 1 one_ne_zero`.
-/
theorem pieri_sum_finset {α : Type*} [DecidableEq α] (S : Finset α) (u : α → ℝ) (hu : Set.InjOn u S) :
    ∑ s ∈ S, ∏ b ∈ S.erase s, (u s - u b + 1) / (u s - u b) = #S := by
  exact sum_prod_sub_add_div_sub_eq_card S u hu 1 one_ne_zero

/- English proof (translation)
Establish `h` using `sum_prod_sub_add_div_sub_eq_card S u hu (-1) (by norm_num)`. Simplify using `only [← sub_eq_add_neg] at h`. Conclude with `h`.
-/
theorem pieri_sum_finset_neg {α : Type*} [DecidableEq α] (S : Finset α) (u : α → ℝ) (hu : Set.InjOn u S) :
    ∑ s ∈ S, ∏ b ∈ S.erase s, (u s - u b - 1) / (u s - u b) = #S := by
  have h := sum_prod_sub_add_div_sub_eq_card S u hu (-1) (by norm_num)
  simp only [← sub_eq_add_neg] at h
  exact h

/- English proof (translation)
Use extensionality with `b`. Simplify using `[hs]`.
-/
lemma block_filter_eq_erase {n : ℕ} (ε : Fin n → Bool) (β : Bool) {s : Fin n} (hs : ε s = β) :
    univ.filter (fun b => b ≠ s ∧ ε b = ε s) = (univ.filter (fun b => ε b = β)).erase s := by
  ext b
  simp [hs]

/- English proof (translation)
Rewrite using `[Finset.sum_congr rfl (fun s hs => by rw [block_filter_eq_erase ε β (Finset.mem_filter.mp hs).2])]`. Conclude with `pieri_sum_finset _ u (fun a ha b hb h => hu a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 h)`.
-/
theorem blockSum_plus {n : ℕ} (ε : Fin n → Bool) (β : Bool) (u : Fin n → ℝ)
    (hu : ∀ a b, ε a = β → ε b = β → u a = u b → a = b) :
    ∑ s ∈ univ.filter (fun s => ε s = β), ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
      (u s - u b + 1) / (u s - u b) = ((univ.filter (fun s => ε s = β)).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun s hs => by rw [block_filter_eq_erase ε β (Finset.mem_filter.mp hs).2])]
  exact pieri_sum_finset _ u (fun a ha b hb h =>
    hu a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 h)

/- English proof (translation)
Rewrite using `[Finset.sum_congr rfl (fun s hs => by rw [block_filter_eq_erase ε β (Finset.mem_filter.mp hs).2])]`. Conclude with `pieri_sum_finset_neg _ u (fun a ha b hb h => hu a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 h)`.
-/
theorem blockSum_minus {n : ℕ} (ε : Fin n → Bool) (β : Bool) (u : Fin n → ℝ)
    (hu : ∀ a b, ε a = β → ε b = β → u a = u b → a = b) :
    ∑ s ∈ univ.filter (fun s => ε s = β), ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
      (u s - u b - 1) / (u s - u b) = ((univ.filter (fun s => ε s = β)).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun s hs => by rw [block_filter_eq_erase ε β (Finset.mem_filter.mp hs).2])]
  exact pieri_sum_finset_neg _ u (fun a ha b hb h =>
    hu a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 h)

end ReciprocityTheory.ChartRestriction.DS.HW
