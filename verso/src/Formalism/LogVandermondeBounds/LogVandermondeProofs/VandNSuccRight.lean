import Formalism.LogVandermondeBounds.VandPlace

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

/- English proof (translation)
Introduce `i j hij hjN`. Proceed by induction on `j with`. Consider the case `zero => omega`. Consider the case `succ j ih`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'` into its components or cases.

Conclude with `lt_trans (h j (by omega)) (ih h' (by omega))`. Substitute `h'` using the available equality. Conclude with `h i hjN`.
-/
lemma anti_of_step (f : ℕ → ℝ) (N : ℕ) (h : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i j, i < j → j < N → f j < f i := by
  intro i j hij hjN
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (h j (by omega)) (ih h' (by omega))
    · subst h'; exact h i hjN

/- English proof (translation)
Introduce `i j hij hjN`. Proceed by induction on `j with`. Consider the case `zero => omega`. Consider the case `succ j ih`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'` into its components or cases.

Establish `h1` using `h j (by omega)`. Establish `h2` using `ih h' (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Substitute `h'` using the available equality. Conclude with `h i hjN`.
-/
lemma gap_of_step (f : ℕ → ℝ) (N : ℕ) (h : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i) :
    ∀ i j, i < j → j < N → 1 ≤ f j - f i := by
  intro i j hij hjN
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · have h1 := h j (by omega)
      have h2 := ih h' (by omega)
      linarith
    · subst h'; exact h i hjN

/- English proof (translation)
Unfold `vandN`. Apply `prod_pos` to reduce the goal to its premises. Introduce `i hi`. Apply `prod_pos` to reduce the goal to its premises. Introduce `j hj`.

Rewrite `hi` using `[mem_range]`. Rewrite `hj` using `[mem_Ico]`. Conclude with `sub_pos.2 (h i j (by omega) (by omega))`.
-/
lemma vandN_pos (x : ℕ → ℝ) (N : ℕ) (h : ∀ i j, i < j → j < N → x j < x i) : 0 < vandN x N := by
  unfold vandN
  apply prod_pos
  intro i hi
  apply prod_pos
  intro j hj
  rw [mem_range] at hi
  rw [mem_Ico] at hj
  exact sub_pos.2 (h i j (by omega) (by omega))

/- English proof (translation)
Unfold `vandN`. Apply `prod_congr rfl` to reduce the goal to its premises. Introduce `i hi`. Apply `prod_congr rfl` to reduce the goal to its premises. Introduce `j hj`.

Rewrite `hi` using `[mem_range]`. Rewrite `hj` using `[mem_Ico]`. Rewrite using `[h i hi, h j (by omega)]`.
-/
lemma vandN_congr (x y : ℕ → ℝ) (N : ℕ) (h : ∀ i, i < N → x i = y i) : vandN x N = vandN y N := by
  unfold vandN
  apply prod_congr rfl
  intro i hi
  apply prod_congr rfl
  intro j hj
  rw [mem_range] at hi
  rw [mem_Ico] at hj
  rw [h i hi, h j (by omega)]

/- English proof (translation)
Unfold `vandN`. Rewrite using `[prod_range_succ, Ico_self, prod_empty, mul_one, ← prod_mul_distrib]`. Apply `prod_congr rfl` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[mem_range]`.

Rewrite using `[prod_Ico_succ_top (by omega : i + 1 ≤ N)]`.
-/
lemma vandN_succ_right (x : ℕ → ℝ) (N : ℕ) :
    vandN x (N + 1) = vandN x N * ∏ i ∈ range N, (x i - x N) := by
  unfold vandN
  rw [prod_range_succ, Ico_self, prod_empty, mul_one, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [prod_Ico_succ_top (by omega : i + 1 ≤ N)]

/- English proof (translation)
Unfold `vandN`. Rewrite using `[prod_range_succ', mul_comm, zero_add]`. Use `congr 1`. Apply `prod_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[← prod_Ico_add' (fun j => x (i + 1) - x j) (i + 1) N 1]`.
-/
lemma vandN_succ_left (x : ℕ → ℝ) (N : ℕ) :
    vandN x (N + 1) = (∏ j ∈ Ico 1 (N + 1), (x 0 - x j)) * vandN (fun i => x (i + 1)) N := by
  unfold vandN
  rw [prod_range_succ', mul_comm, zero_add]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [← prod_Ico_add' (fun j => x (i + 1) - x j) (i + 1) N 1]

/- English proof (translation)
Establish `hr : ∀ i, i < k - 1 → rowPar k v b i = v i` using `fun i hi => by simp [rowPar, hi]`. Establish `hr2 : ∀ i, rowPar k v b (k - 1 + i) = - b i` using `fun i => by simp [rowPar]`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`.

Introduce `_`. Simplify using `only [range_zero, prod_empty, mul_one, add_zero]`. Conclude with `le_of_eq (vandN_congr _ _ _ (fun i hi => (hr i hi).symm))`. Consider the case `succ m ih`. Introduce `hm`.

Establish `ih'` using `ih (by omega)`. Establish `hbm : 0 < b m` using `hbpos m (by omega)`. Rewrite using `[show k - 1 + (m + 1) = (k - 1 + m) + 1 by omega, vandN_succ_right, prod_range_succ]`. Establish `hA : b m ^ (k - 1) ≤ ∏ i ∈ range (k - 1), (rowPar k v b i - rowPar k v b (k - 1 + m))`. Combine the equalities or inequalities in the displayed calculation.

Apply `prod_le_prod (fun i _ => hbm.le)` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[mem_range]`. Rewrite using `[hr i hi, hr2 m]`. Combine the linear relations using `[hv i hi]`.

Establish `hB : (1 : ℝ) ≤ ∏ i ∈ range m, (rowPar k v b (k - 1 + i) - rowPar k v b (k - 1 + m))`. Combine the equalities or inequalities in the displayed calculation. Apply `prod_le_prod (fun i _ => zero_le_one)` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[mem_range]`.

Rewrite using `[hr2 i, hr2 m]`. Combine the linear relations using `[hgap i m hi (by omega)]`. Establish `hF : b m ^ (k - 1) ≤ ∏ i ∈ range (k - 1 + m), (rowPar k v b i - rowPar k v b (k - 1 + m))`. Rewrite using `[prod_range_add]`. Establish `hA0 : 0 ≤ ∏ i ∈ range (k - 1), (rowPar k v b i - rowPar k v b (k - 1 + m))` using `le_trans (pow_nonneg hbm.le _) hA`.

Combine the equalities or inequalities in the displayed calculation. Establish `hL0 : 0 ≤ vandN v (k - 1) * ∏ j ∈ range m, b j ^ (k - 1)` using `mul_nonneg hV.le (prod_nonneg fun j hj => pow_nonneg (hbpos j (by rw [mem_range] at hj; omega)).le _)`. Rewrite using `[← mul_assoc]`. Conclude with `mul_le_mul ih' hF (pow_nonneg hbm.le _) (le_trans hL0 ih')`.
-/
private lemma vandN_mul_prod_pow_le_vandN_rowPar (k M : ℕ) (v b : ℕ → ℝ)
    (hv : ∀ i, i < k - 1 → 0 ≤ v i) (hbpos : ∀ j, j < M → 0 < b j)
    (hgap : ∀ i j, i < j → j < M → 1 ≤ b j - b i) (hV : 0 < vandN v (k - 1)) :
    ∀ m, m ≤ M → vandN v (k - 1) * ∏ j ∈ range m, b j ^ (k - 1)
      ≤ vandN (rowPar k v b) (k - 1 + m) := by
  have hr : ∀ i, i < k - 1 → rowPar k v b i = v i := fun i hi => by simp [rowPar, hi]
  have hr2 : ∀ i, rowPar k v b (k - 1 + i) = - b i := fun i => by simp [rowPar]
  intro m
  induction m with
  | zero =>
    intro _
    simp only [range_zero, prod_empty, mul_one, add_zero]
    exact le_of_eq (vandN_congr _ _ _ (fun i hi => (hr i hi).symm))
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hbm : 0 < b m := hbpos m (by omega)
    rw [show k - 1 + (m + 1) = (k - 1 + m) + 1 by omega, vandN_succ_right, prod_range_succ]
    have hA : b m ^ (k - 1) ≤ ∏ i ∈ range (k - 1), (rowPar k v b i - rowPar k v b (k - 1 + m)) := by
      calc b m ^ (k - 1) = ∏ _i ∈ range (k - 1), b m := by simp
        _ ≤ _ := by
          apply prod_le_prod (fun i _ => hbm.le)
          intro i hi
          rw [mem_range] at hi
          rw [hr i hi, hr2 m]
          linarith [hv i hi]
    have hB : (1 : ℝ) ≤ ∏ i ∈ range m, (rowPar k v b (k - 1 + i) - rowPar k v b (k - 1 + m)) := by
      calc (1 : ℝ) = ∏ _i ∈ range m, (1 : ℝ) := by simp
        _ ≤ _ := by
          apply prod_le_prod (fun i _ => zero_le_one)
          intro i hi
          rw [mem_range] at hi
          rw [hr2 i, hr2 m]
          linarith [hgap i m hi (by omega)]
    have hF : b m ^ (k - 1) ≤ ∏ i ∈ range (k - 1 + m), (rowPar k v b i - rowPar k v b (k - 1 + m)) := by
      rw [prod_range_add]
      have hA0 : 0 ≤ ∏ i ∈ range (k - 1), (rowPar k v b i - rowPar k v b (k - 1 + m)) :=
        le_trans (pow_nonneg hbm.le _) hA
      calc b m ^ (k - 1) = b m ^ (k - 1) * 1 := by ring
        _ ≤ _ := mul_le_mul hA hB zero_le_one hA0
    have hL0 : 0 ≤ vandN v (k - 1) * ∏ j ∈ range m, b j ^ (k - 1) :=
      mul_nonneg hV.le (prod_nonneg fun j hj => pow_nonneg (hbpos j (by rw [mem_range] at hj; omega)).le _)
    rw [← mul_assoc]
    exact mul_le_mul ih' hF (pow_nonneg hbm.le _) (le_trans hL0 ih')

/- English proof (translation)
Establish `hvsplit : vandN v (p + 1) = (∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1))) * ∏ i ∈ range p, (v i - v (i + 1))`. Unfold `vandN`. Rewrite using `[prod_range_succ, Ico_self, prod_empty, mul_one, ← prod_mul_distrib]`. Use `prod_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Rewrite `hi` using `[mem_range]`.

Rewrite using `[prod_eq_prod_Ico_succ_bot (by omega : i + 1 < p + 1), ← prod_Ico_add' (fun j => v i - v j) (i + 1) p 1, mul_comm]`. Establish `hD0 : 0 ≤ D` using `le_trans (by linarith [hu 0 1 (by omega) (by omega)]) (hD 0 1 (by omega) (by omega))`. Rewrite using `[hvsplit, show p + 2 = (p + 1) + 1 from rfl, vandN_succ_left, vandN_succ_right]`. Use `beta_reduce`. Establish `hP0 : ∏ j ∈ Ico 1 (p + 1 + 1), (u 0 - u j) ≤ D ^ (p + 1)`.

Combine the equalities or inequalities in the displayed calculation. Apply `prod_le_prod` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[mem_Ico]`. Combine the linear relations using `[hu 0 j (by omega) (by omega)]`.

Introduce `j hj`. Rewrite `hj` using `[mem_Ico]`. Conclude with `hD 0 j (by omega) (by omega)`. Use `_ = D ^ (p + 1) := by simp`. Establish `hC0 : 0 ≤ ∏ i ∈ range p, (u (i + 1) - u (p + 1))`.

Apply `prod_nonneg` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[mem_range]`. Combine the linear relations using `[hu (i + 1) (p + 1) (by omega) (by omega)]`. Establish `hC : ∏ i ∈ range p, (u (i + 1) - u (p + 1)) ≤ D ^ p`.

Combine the equalities or inequalities in the displayed calculation. Apply `prod_le_prod` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[mem_range]`. Combine the linear relations using `[hu (i + 1) (p + 1) (by omega) (by omega)]`.

Introduce `i hi`. Rewrite `hi` using `[mem_range]`. Conclude with `hD (i + 1) (p + 1) (by omega) (by omega)`. Use `_ = D ^ p := by simp`. Establish `hV0 : 0 ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (u (i + 1) - u (j + 1))`.

Apply `prod_nonneg` to reduce the goal to its premises. Introduce `i hi`. Apply `prod_nonneg` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hi` using `[mem_range]`.

Rewrite `hj` using `[mem_Ico]`. Combine the linear relations using `[hu (i + 1) (j + 1) (by omega) (by omega)]`. Establish `hW0 : 0 ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1))`. Apply `prod_nonneg` to reduce the goal to its premises. Introduce `i hi`.

Apply `prod_nonneg` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hi` using `[mem_range]`. Rewrite `hj` using `[mem_Ico]`. Combine the linear relations using `[(hint i (by omega)).2, (hint (j + 1) (by omega)).1, hu (i + 1) (j + 1) (by omega) (by omega)]`.

Establish `hVW : ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (u (i + 1) - u (j + 1)) ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1))`. Apply `prod_le_prod` to reduce the goal to its premises. Introduce `i hi`. Apply `prod_nonneg` to reduce the goal to its premises. Introduce `j hj`.

Rewrite `hi` using `[mem_range]`. Rewrite `hj` using `[mem_Ico]`. Combine the linear relations using `[hu (i + 1) (j + 1) (by omega) (by omega)]`. Introduce `i hi`. Apply `prod_le_prod` to reduce the goal to its premises.

Introduce `j hj`. Rewrite `hi` using `[mem_range]`. Rewrite `hj` using `[mem_Ico]`. Combine the linear relations using `[hu (i + 1) (j + 1) (by omega) (by omega)]`. Introduce `j hj`.

Rewrite `hi` using `[mem_range]`. Rewrite `hj` using `[mem_Ico]`. Combine the linear relations using `[(hint i (by omega)).2, (hint (j + 1) (by omega)).1]`. Establish `hAdj : (1 : ℝ) ≤ ∏ i ∈ range p, (v i - v (i + 1))`. Combine the equalities or inequalities in the displayed calculation.

Apply `prod_le_prod (fun i _ => zero_le_one)` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[mem_range]`. Conclude with `hst i (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma vandN_le_pow_mul_pow_mul_vandN_of_interlace (p : ℕ) (u v : ℕ → ℝ) (D : ℝ)
    (hu : ∀ i j, i < j → j < p + 2 → u j < u i)
    (hint : ∀ i, i < p + 1 → v i < u i ∧ u (i + 1) < v i)
    (hst : ∀ i, i + 1 < p + 1 → 1 ≤ v i - v (i + 1))
    (hD : ∀ i j, i < j → j ≤ p + 1 → u i - u j ≤ D) :
    vandN u (p + 2) ≤ D ^ (p + 1) * D ^ p * vandN v (p + 1) := by
  have hvsplit : vandN v (p + 1) = (∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1)))
      * ∏ i ∈ range p, (v i - v (i + 1)) := by
    unfold vandN
    rw [prod_range_succ, Ico_self, prod_empty, mul_one, ← prod_mul_distrib]
    refine prod_congr rfl (fun i hi => ?_)
    rw [mem_range] at hi
    rw [prod_eq_prod_Ico_succ_bot (by omega : i + 1 < p + 1),
      ← prod_Ico_add' (fun j => v i - v j) (i + 1) p 1, mul_comm]
  have hD0 : 0 ≤ D := le_trans (by linarith [hu 0 1 (by omega) (by omega)]) (hD 0 1 (by omega) (by omega))
  rw [hvsplit, show p + 2 = (p + 1) + 1 from rfl, vandN_succ_left, vandN_succ_right]
  beta_reduce
  have hP0 : ∏ j ∈ Ico 1 (p + 1 + 1), (u 0 - u j) ≤ D ^ (p + 1) := by
    calc _ ≤ ∏ _j ∈ Ico 1 (p + 1 + 1), D := by
          apply prod_le_prod
          · intro j hj
            rw [mem_Ico] at hj
            linarith [hu 0 j (by omega) (by omega)]
          · intro j hj
            rw [mem_Ico] at hj
            exact hD 0 j (by omega) (by omega)
      _ = D ^ (p + 1) := by simp
  have hC0 : 0 ≤ ∏ i ∈ range p, (u (i + 1) - u (p + 1)) := by
    apply prod_nonneg
    intro i hi
    rw [mem_range] at hi
    linarith [hu (i + 1) (p + 1) (by omega) (by omega)]
  have hC : ∏ i ∈ range p, (u (i + 1) - u (p + 1)) ≤ D ^ p := by
    calc _ ≤ ∏ _i ∈ range p, D := by
          apply prod_le_prod
          · intro i hi
            rw [mem_range] at hi
            linarith [hu (i + 1) (p + 1) (by omega) (by omega)]
          · intro i hi
            rw [mem_range] at hi
            exact hD (i + 1) (p + 1) (by omega) (by omega)
      _ = D ^ p := by simp
  have hV0 : 0 ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (u (i + 1) - u (j + 1)) := by
    apply prod_nonneg
    intro i hi
    apply prod_nonneg
    intro j hj
    rw [mem_range] at hi
    rw [mem_Ico] at hj
    linarith [hu (i + 1) (j + 1) (by omega) (by omega)]
  have hW0 : 0 ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1)) := by
    apply prod_nonneg
    intro i hi
    apply prod_nonneg
    intro j hj
    rw [mem_range] at hi
    rw [mem_Ico] at hj
    linarith [(hint i (by omega)).2, (hint (j + 1) (by omega)).1, hu (i + 1) (j + 1) (by omega) (by omega)]
  have hVW : ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (u (i + 1) - u (j + 1))
      ≤ ∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1)) := by
    apply prod_le_prod
    · intro i hi
      apply prod_nonneg
      intro j hj
      rw [mem_range] at hi
      rw [mem_Ico] at hj
      linarith [hu (i + 1) (j + 1) (by omega) (by omega)]
    · intro i hi
      apply prod_le_prod
      · intro j hj
        rw [mem_range] at hi
        rw [mem_Ico] at hj
        linarith [hu (i + 1) (j + 1) (by omega) (by omega)]
      · intro j hj
        rw [mem_range] at hi
        rw [mem_Ico] at hj
        linarith [(hint i (by omega)).2, (hint (j + 1) (by omega)).1]
  have hAdj : (1 : ℝ) ≤ ∏ i ∈ range p, (v i - v (i + 1)) := by
    calc (1 : ℝ) = ∏ _i ∈ range p, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply prod_le_prod (fun i _ => zero_le_one)
        intro i hi
        rw [mem_range] at hi
        exact hst i (by omega)
  calc (∏ j ∈ Ico 1 (p + 1 + 1), (u 0 - u j)) *
        ((∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (u (i + 1) - u (j + 1))) *
          ∏ i ∈ range p, (u (i + 1) - u (p + 1)))
      ≤ D ^ (p + 1) * ((∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1))) * D ^ p) :=
        mul_le_mul hP0 (mul_le_mul hVW hC hC0 hW0) (mul_nonneg hV0 hC0) (pow_nonneg hD0 _)
    _ = D ^ (p + 1) * D ^ p * ((∏ i ∈ range p, ∏ j ∈ Ico (i + 1) p, (v i - v (j + 1))) * 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAdj hW0)
        (mul_nonneg (pow_nonneg hD0 _) (pow_nonneg hD0 _))

/- English proof (translation)
Introduce `ε x hε hx k m Δ u v b w hk hm hΔ hP`. Take `⟨hv, hvstep, hint, hb0u, hcase, hw, hbstep, hkb, hwB⟩` from `hP`. Take `⟨p, rfl⟩ : ∃ p, k = p + 2` from `⟨k - 2, by omega⟩`. Take `⟨q, rfl⟩ : ∃ q, m = q + 1` from `⟨m - 1, by omega⟩`. Establish `e1 : p + 2 - 1 = p + 1` using `by omega`.

Establish `e2 : p + 2 - 2 = p` using `by omega`. Establish `e3 : q + 1 - 1 = q` using `by omega`. Simplify using `only [e1, e2, e3] at hv hvstep hint hb0u hcase hwB ⊢`. Move the coercions through the operations in `at hv hcase hkb ⊢`. Establish `hx0 : 0 < x` using `by linarith`.

Establish `hB1 : 1 ≤ Real.exp (x ^ ε)` using `Real.one_le_exp (Real.rpow_nonneg hx0.le _)`. Establish `haB : Real.exp (x ^ ε) ≤ x * Real.exp (x ^ ε)` using `le_mul_of_one_le_left (by linarith) hx`. Establish `ha1 : 1 ≤ x * Real.exp (x ^ ε)` using `le_trans hB1 haB`. Establish `hbgap : ∀ i j, i < j → j < q + 1 → 1 ≤ b j - b i` using `gap_of_step b (q + 1) (fun i hi => (hbstep i hi).2)`. Establish `hK0 : 0 < ((p : ℝ) + 2) * (4 * Δ)` using `by positivity`.

Establish `hb0 : 0 < b 0` using `(div_pos_iff_of_pos_right hx0).1 (lt_of_lt_of_le hK0 hkb)`. Establish `hbpos : ∀ j, j < q + 1 → 0 < b j`. Introduce `j hj`. Break down `Nat.eq_zero_or_pos j with h | h` into its components or cases. Substitute `h` using the available equality.

Conclude with `hb0`. Combine the linear relations using `[hbgap 0 j h hj]`. Establish `hu : ∀ i j, i < j → j < p + 2 → u j < u i` using `anti_of_step u (p + 2) (fun i hi => by`. Use `hint i (by omega)` as an intermediate fact. Combine the linear relations using `[this.1, this.2])`.

Establish `hvdec : ∀ i j, i < j → j < p + 1 → v j < v i` using `anti_of_step v (p + 1) (fun i hi => by`. Use `hvstep i hi` as an intermediate fact. Use the proof step `linarith)`. Establish `hVv : 0 < vandN v (p + 1)` using `vandN_pos v _ hvdec`. Establish `hVu : 0 < vandN u (p + 2)` using `vandN_pos u _ hu`.

Establish `hbq : b 0 ≤ b q`. Break down `Nat.eq_zero_or_pos q with h | h` into its components or cases. Rewrite using `[h]`. Combine the linear relations using `[hbgap 0 q h (by omega)]`. Establish `hD8 : u 0 - u (p + 1) ≤ 8 * (x * Real.exp (x ^ ε))`.

Break down `hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hwq` using `(hw q (by omega)).1`. Establish `hdiv : b 0 / x ≤ b 0` using `div_le_self hb0.le hx`. Establish `hv0` using `(hv 0 (by omega)).2`.

Establish `hvp` using `(hv p (by omega)).1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDpair : ∀ i j, i < j → j ≤ p + 1 → u i - u j ≤ 8 * (x * Real.exp (x ^ ε))`. Introduce `i j hij hj`. Establish `h1 : u i ≤ u 0`.

Break down `Nat.eq_zero_or_pos i with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `(hu 0 i h (by omega)).le`. Establish `h2 : u (p + 1) ≤ u j`. Break down `Nat.lt_or_ge j (p + 1) with h | h` into its components or cases.

Conclude with `(hu j (p + 1) h (by omega)).le`. Rewrite using `[show j = p + 1 by omega]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `huv` using `vandN_le_pow_mul_pow_mul_vandN_of_interlace p u v _ hu hint (fun i hi => by linarith [hvstep i hi]) hDpair`. Establish `hrow` using `vandN_mul_prod_pow_le_vandN_rowPar (p + 2) (q + 1) v b (by simpa only [e1] using fun i hi => (hv i hi).1) hbpos hbgap (by simpa only [e1] using hVv) (q + 1) le_rfl`.

Simplify using `only [e1] at hrow`. Establish `hP : 0 < ∏ j ∈ range (q + 1), b j ^ (p + 1)` using `prod_pos fun j hj => pow_pos (hbpos j (mem_range.1 hj)) _`. Establish `hrow0 : 0 < vandN (rowPar (p + 2) v b) (p + 1 + (q + 1))` using `lt_of_lt_of_le (mul_pos hVv hP) hrow`. Use `⟨hVu, hrow0, ?_⟩` and prove the remaining obligations. Establish `h8 : 0 < 8 * (x * Real.exp (x ^ ε))` using `by linarith`.

Establish `hlr : Real.log (vandN v (p + 1)) + (p + 1) * ∑ j ∈ range (q + 1), Real.log (b j) ≤ Real.log (vandN (rowPar (p + 2) v b) (p + 1 + (q + 1)))`. Use `Real.log_le_log (mul_pos hVv hP) hrow` as an intermediate fact. Rewrite `this` using `[Real.log_mul hVv.ne' hP.ne', Real.log_prod (fun j hj => (pow_pos (hbpos j (mem_range.1 hj)) _).ne')]`. Simplify using `only [Real.log_pow] at this`. Rewrite `this` using `[← mul_sum]`.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlu : Real.log (vandN u (p + 2)) ≤ (p + 1) * Real.log (8 * (x * Real.exp (x ^ ε))) + p * Real.log (8 * (x * Real.exp (x ^ ε))) + Real.log (vandN v (p + 1))`. Use `Real.log_le_log hVu huv` as an intermediate fact. Rewrite `this` using `[Real.log_mul (by positivity) hVv.ne', Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]`.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl8 : 0 ≤ Real.log (8 * (x * Real.exp (x ^ ε)))` using `Real.log_nonneg (by linarith)`. Establish `hlk : 0 ≤ Real.log ((p : ℝ) + 2)` using `Real.log_nonneg (by linarith [(p.cast_nonneg : (0 : ℝ) ≤ p)])`. Establish `hpk : 0 ≤ ((p : ℝ) + 2) * (1 + Real.log ((p : ℝ) + 2))` using `mul_nonneg (by positivity) (by linarith)`.

Use polynomial arithmetic with `[hl8, hlk, hpk, (p.cast_nonneg : (0 : ℝ) ≤ p)]`.
-/
theorem VandPlace_holds : VandPlace := by
  intro ε x hε hx k m Δ u v b w hk hm hΔ hP
  obtain ⟨hv, hvstep, hint, hb0u, hcase, hw, hbstep, hkb, hwB⟩ := hP
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  have e1 : p + 2 - 1 = p + 1 := by omega
  have e2 : p + 2 - 2 = p := by omega
  have e3 : q + 1 - 1 = q := by omega
  simp only [e1, e2, e3] at hv hvstep hint hb0u hcase hwB ⊢
  push_cast at hv hcase hkb ⊢
  have hx0 : 0 < x := by linarith
  have hB1 : 1 ≤ Real.exp (x ^ ε) := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have haB : Real.exp (x ^ ε) ≤ x * Real.exp (x ^ ε) := le_mul_of_one_le_left (by linarith) hx
  have ha1 : 1 ≤ x * Real.exp (x ^ ε) := le_trans hB1 haB
  have hbgap : ∀ i j, i < j → j < q + 1 → 1 ≤ b j - b i := gap_of_step b (q + 1) (fun i hi => (hbstep i hi).2)
  have hK0 : 0 < ((p : ℝ) + 2) * (4 * Δ) := by positivity
  have hb0 : 0 < b 0 := (div_pos_iff_of_pos_right hx0).1 (lt_of_lt_of_le hK0 hkb)
  have hbpos : ∀ j, j < q + 1 → 0 < b j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact hb0
    · linarith [hbgap 0 j h hj]
  have hu : ∀ i j, i < j → j < p + 2 → u j < u i :=
    anti_of_step u (p + 2) (fun i hi => by
      have := hint i (by omega)
      linarith [this.1, this.2])
  have hvdec : ∀ i j, i < j → j < p + 1 → v j < v i :=
    anti_of_step v (p + 1) (fun i hi => by
      have := hvstep i hi
      linarith)
  have hVv : 0 < vandN v (p + 1) := vandN_pos v _ hvdec
  have hVu : 0 < vandN u (p + 2) := vandN_pos u _ hu
  have hbq : b 0 ≤ b q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h]
    · linarith [hbgap 0 q h (by omega)]
  have hD8 : u 0 - u (p + 1) ≤ 8 * (x * Real.exp (x ^ ε)) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · linarith
    · have hwq := (hw q (by omega)).1
      have hdiv : b 0 / x ≤ b 0 := div_le_self hb0.le hx
      have hv0 := (hv 0 (by omega)).2
      have hvp := (hv p (by omega)).1
      linarith
  have hDpair : ∀ i j, i < j → j ≤ p + 1 → u i - u j ≤ 8 * (x * Real.exp (x ^ ε)) := by
    intro i j hij hj
    have h1 : u i ≤ u 0 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h]
      · exact (hu 0 i h (by omega)).le
    have h2 : u (p + 1) ≤ u j := by
      rcases Nat.lt_or_ge j (p + 1) with h | h
      · exact (hu j (p + 1) h (by omega)).le
      · rw [show j = p + 1 by omega]
    linarith
  have huv := vandN_le_pow_mul_pow_mul_vandN_of_interlace p u v _ hu hint (fun i hi => by linarith [hvstep i hi]) hDpair
  have hrow := vandN_mul_prod_pow_le_vandN_rowPar (p + 2) (q + 1) v b (by simpa only [e1] using fun i hi => (hv i hi).1) hbpos hbgap
    (by simpa only [e1] using hVv) (q + 1) le_rfl
  simp only [e1] at hrow
  have hP : 0 < ∏ j ∈ range (q + 1), b j ^ (p + 1) :=
    prod_pos fun j hj => pow_pos (hbpos j (mem_range.1 hj)) _
  have hrow0 : 0 < vandN (rowPar (p + 2) v b) (p + 1 + (q + 1)) := lt_of_lt_of_le (mul_pos hVv hP) hrow
  refine ⟨hVu, hrow0, ?_⟩
  have h8 : 0 < 8 * (x * Real.exp (x ^ ε)) := by linarith
  have hlr : Real.log (vandN v (p + 1)) + (p + 1) * ∑ j ∈ range (q + 1), Real.log (b j)
      ≤ Real.log (vandN (rowPar (p + 2) v b) (p + 1 + (q + 1))) := by
    have := Real.log_le_log (mul_pos hVv hP) hrow
    rw [Real.log_mul hVv.ne' hP.ne', Real.log_prod (fun j hj => (pow_pos (hbpos j (mem_range.1 hj)) _).ne')] at this
    simp only [Real.log_pow] at this
    rw [← mul_sum] at this
    push_cast at this
    linarith
  have hlu : Real.log (vandN u (p + 2))
      ≤ (p + 1) * Real.log (8 * (x * Real.exp (x ^ ε))) + p * Real.log (8 * (x * Real.exp (x ^ ε)))
        + Real.log (vandN v (p + 1)) := by
    have := Real.log_le_log hVu huv
    rw [Real.log_mul (by positivity) hVv.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hl8 : 0 ≤ Real.log (8 * (x * Real.exp (x ^ ε))) := Real.log_nonneg (by linarith)
  have hlk : 0 ≤ Real.log ((p : ℝ) + 2) := Real.log_nonneg (by linarith [(p.cast_nonneg : (0 : ℝ) ≤ p)])
  have hpk : 0 ≤ ((p : ℝ) + 2) * (1 + Real.log ((p : ℝ) + 2)) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [hl8, hlk, hpk, (p.cast_nonneg : (0 : ℝ) ≤ p)]

end Formalism.LogVandermondeBounds.StandardLattice
