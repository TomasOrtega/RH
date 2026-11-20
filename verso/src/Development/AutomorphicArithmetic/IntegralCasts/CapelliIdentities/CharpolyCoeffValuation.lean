import Mathlib

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, map_prod]`.
-/
private theorem UpperTheory.valuation_perm_term {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (σ : Equiv.Perm ι) :
    v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = ∏ i, v (M (σ i) i) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, map_prod]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `v.map_sum_le fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[UpperTheory.valuation_perm_term]`. Conclude with `Finset.prod_le_one' fun i _ => h1 _ _`.
-/
private theorem UpperTheory.valuation_det_le_one_of_entries_le_one' {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le fun σ _ => ?_
  rw [UpperTheory.valuation_perm_term]
  exact Finset.prod_le_one' fun i _ => h1 _ _

/- English proof (translation)
Establish `hlt : ∀ (σ : Equiv.Perm ι) (j : ι), v (M (σ j) j) < 1 → v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1`. Introduce `σ j hj`. Rewrite using `[UpperTheory.valuation_perm_term, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun i _ => h1 _ _)) hj`. Establish `hσ : ∀ σ : Equiv.Perm ι, σ ≠ 1 → v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1`.

Introduce `σ hσ`. Establish `: ∃ j, j < σ j`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hσ` to reduce the goal to its premises.

Use extensionality with `i`. Proceed by induction on `i using WellFoundedLT.induction with`. Consider the case `_ i ih`. Break down `(hcon i).lt_or_eq with h | h` into its components or cases. Conclude with `σ.injective (ih _ h)`.

Conclude with `h`. Take `⟨j, hj⟩` from `this`. Conclude with `hlt σ j (h2 _ _ hj)`. Prove the components needed by the constructor for the conclusion. Introduce `h i`.

Assume the negation of the conclusion as `hne`. Establish `hi : v (M i i) < 1` using `lt_of_le_of_ne (h1 _ _) hne`. Use `absurd h (ne_of_lt ?_)` and prove the remaining obligations. Rewrite using `[Matrix.det_apply]`. Use `v.map_sum_lt one_ne_zero fun σ _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h' : σ = 1`. Conclude with `hlt σ i (by simpa [h'] using hi)`. Conclude with `hσ σ h'`. Introduce `h`. Establish `h0 : v (Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, M ((1 : Equiv.Perm ι) i) i) = 1`.

Rewrite using `[UpperTheory.valuation_perm_term]`. Conclude with `Finset.prod_eq_one fun i _ => h i`. Rewrite using `[Matrix.det_apply, v.map_sum_eq_of_lt (Finset.mem_univ 1), h0]`. Introduce `σ hσ'`. Rewrite using `[h0]`.

Conclude with `hσ σ (by simpa using hσ')`.
-/
private theorem UpperTheory.val_det_eq_one_iff {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) (h2 : ∀ i j, j < i → v (M i j) < 1) :
    v M.det = 1 ↔ ∀ i, v (M i i) = 1 := by
  have hlt : ∀ (σ : Equiv.Perm ι) (j : ι), v (M (σ j) j) < 1 →
      v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ j hj
    rw [UpperTheory.valuation_perm_term, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun i _ => h1 _ _)) hj
  have hσ : ∀ σ : Equiv.Perm ι, σ ≠ 1 → v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ hσ
    have : ∃ j, j < σ j := by
      by_contra hcon
      push Not at hcon
      apply hσ
      ext i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rcases (hcon i).lt_or_eq with h | h
        · exact σ.injective (ih _ h)
        · exact h
    obtain ⟨j, hj⟩ := this
    exact hlt σ j (h2 _ _ hj)
  constructor
  · intro h i
    by_contra hne
    have hi : v (M i i) < 1 := lt_of_le_of_ne (h1 _ _) hne
    refine absurd h (ne_of_lt ?_)
    rw [Matrix.det_apply]
    refine v.map_sum_lt one_ne_zero fun σ _ => ?_
    by_cases h' : σ = 1
    · exact hlt σ i (by simpa [h'] using hi)
    · exact hσ σ h'
  · intro h
    have h0 : v (Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, M ((1 : Equiv.Perm ι) i) i) = 1 := by
      rw [UpperTheory.valuation_perm_term]
      exact Finset.prod_eq_one fun i _ => h i
    rw [Matrix.det_apply, v.map_sum_eq_of_lt (Finset.mem_univ 1), h0]
    intro σ hσ'
    rw [h0]
    exact hσ σ (by simpa using hσ')

/- English proof (translation)
Establish `hc' : (S \ T).card = (T \ S).card` using `Finset.card_sdiff_comm hc`. Establish `hS : (S \ T).Nonempty`. Rewrite using `[Finset.sdiff_nonempty]`. Introduce `hsub`. Conclude with `hne (Finset.eq_of_subset_of_card_le hsub hc.ge)`.

Establish `hT' : (T \ S).Nonempty`. Rewrite using `[← Finset.card_pos, ← hc', Finset.card_pos]`. Conclude with `hS`. Take `⟨c, hcm, hcmax⟩` from `Finset.exists_max_image (S \ T) id hS`. Establish `key : ∏ i ∈ S \ T, f i < ∏ i ∈ T \ S, f i`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.prod_inter_mul_prod_diff S T, ← Finset.prod_inter_mul_prod_diff T S, Finset.inter_comm T S]`. Conclude with `mul_lt_mul_of_pos_left key (Finset.prod_pos fun i _ => h0 i)`.
-/
private theorem UpperTheory.prod_lt_of_strictMono {Γ ι : Type} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrder ι] (f : ι → Γ) (hf : StrictMono f) (h0 : ∀ i, 0 < f i) (S T : Finset ι)
    (hc : S.card = T.card) (hne : S ≠ T) (hT : ∀ i j, i ∉ T → j ∈ T → i < j) :
    ∏ i ∈ S, f i < ∏ i ∈ T, f i := by
  have hc' : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm hc
  have hS : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hc.ge)
  have hT' : (T \ S).Nonempty := by
    rw [← Finset.card_pos, ← hc', Finset.card_pos]
    exact hS
  obtain ⟨c, hcm, hcmax⟩ := Finset.exists_max_image (S \ T) id hS
  have key : ∏ i ∈ S \ T, f i < ∏ i ∈ T \ S, f i := by
    calc ∏ i ∈ S \ T, f i ≤ ∏ _i ∈ S \ T, f c :=
          Finset.prod_le_prod' fun i hi => hf.monotone (hcmax i hi)
      _ = ∏ _i ∈ T \ S, f c := by simp [hc']
      _ < _ := Finset.prod_lt_prod_of_nonempty (fun _ _ => h0 c)
          (fun i hi => hf (hT _ _ (Finset.mem_sdiff.1 hcm).2 (Finset.mem_sdiff.1 hi).1)) hT'
  rw [← Finset.prod_inter_mul_prod_diff S T, ← Finset.prod_inter_mul_prod_diff T S,
    Finset.inter_comm T S]
  exact mul_lt_mul_of_pos_left key (Finset.prod_pos fun i _ => h0 i)

/- English proof (translation)
Introduce `K Γ _ _ v n M d h1 h2 hdet hmono hd k hk`. Establish `hdiag` using `(UpperTheory.val_det_eq_one_iff v M h1 h2).1 hdet`. Establish `hminor : ∀ S : Finset (Fin n), v ((Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det = (∏ i ∈ S, v (d i)) * v (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det`. Introduce `S`. Establish `: (Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n) = Matrix.of fun i j : S => d i * (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)) i j`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.det_mul_column, map_mul, map_prod, Finset.prod_coe_sort S fun i => v (d i)]`. Use `set T := Finset.univ.filter (fun i : Fin n => k ≤ i.val) with hT`. Establish `hcard : T.card = n - k`.

Establish `h` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => k ≤ i.val)`. Establish `h' : (Finset.univ.filter fun i : Fin n => ¬ k ≤ i.val).card = k`. Simplify using `only [not_le]`. Rewrite using `[Fin.card_filter_val_lt, min_eq_right hk]`. Rewrite `h` using `[h', Finset.card_univ, Fintype.card_fin, ← hT]`.

Use linear arithmetic over natural numbers and integers. Establish `hTval : v ((Matrix.diagonal d * M).submatrix (Subtype.val : T → Fin n) (Subtype.val : T → Fin n)).det = ∏ i ∈ T, v (d i)`. Rewrite using `[hminor, (UpperTheory.val_det_eq_one_iff v (M.submatrix (Subtype.val : T → Fin n) (Subtype.val : T → Fin n)) (fun i j => h1 _ _) (fun i j h => h2 _ _ h)).2 fun i => hdiag _, mul_one]`. Establish `hc` using `Matrix.charpoly_coeff_eq_sum_minors (Matrix.diagonal d * M) (n - k) (by simp)`. Rewrite `hc` using `[Fintype.card_fin, Nat.sub_sub_self hk]`.

Establish `hmem : T ∈ Finset.powersetCard (n - k) (Finset.univ : Finset (Fin n))`. Simplify using `[hcard]`. Rewrite using `[hc, map_mul, map_pow, v.map_neg, map_one, one_pow, one_mul, v.map_sum_eq_of_lt hmem, hTval]`. Introduce `S hS`. Rewrite using `[hTval, hminor]`.

Simplify using `only [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_singleton] at hS`. Use `lt_of_le_of_lt (mul_le_of_le_one_right' (UpperTheory.valuation_det_le_one_of_entries_le_one' v _ fun i j => h1 _ _)) ?_` and prove the remaining obligations. Use `UpperTheory.prod_lt_of_strictMono (fun i => v (d i)) hmono (fun i => zero_lt_iff.2 ((v.ne_zero_iff).2 (hd i))) S T (hS.1.2.trans hcard.symm) hS.2 ?_` and prove the remaining obligations. Introduce `i j hi hj`. Simplify using `only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi hj`.

Conclude with `Fin.lt_def.2 (lt_of_lt_of_le hi hj)`.
-/
theorem UpperTheory.charpoly_coeff_valuation :
    ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ)
        (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
        (∀ i j, v (M i j) ≤ 1) → (∀ i j, j < i → v (M i j) < 1) → v M.det = 1 →
        StrictMono (fun i => v (d i)) → (∀ i, d i ≠ 0) →
        ∀ k ≤ n, v ((Matrix.diagonal d * M).charpoly.coeff k) =
          ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), v (d i) := by
  intro K Γ _ _ v n M d h1 h2 hdet hmono hd k hk
  have hdiag := (UpperTheory.val_det_eq_one_iff v M h1 h2).1 hdet
  have hminor : ∀ S : Finset (Fin n),
      v ((Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det
        = (∏ i ∈ S, v (d i)) *
          v (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det := by
    intro S
    have : (Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)
        = Matrix.of fun i j : S => d i *
          (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)) i j := by
      ext i j
      simp
    rw [this, Matrix.det_mul_column, map_mul, map_prod, Finset.prod_coe_sort S fun i => v (d i)]
  set T := Finset.univ.filter (fun i : Fin n => k ≤ i.val) with hT
  have hcard : T.card = n - k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => k ≤ i.val)
    have h' : (Finset.univ.filter fun i : Fin n => ¬ k ≤ i.val).card = k := by
      simp only [not_le]
      rw [Fin.card_filter_val_lt, min_eq_right hk]
    rw [h', Finset.card_univ, Fintype.card_fin, ← hT] at h
    omega
  have hTval : v ((Matrix.diagonal d * M).submatrix (Subtype.val : T → Fin n)
      (Subtype.val : T → Fin n)).det = ∏ i ∈ T, v (d i) := by
    rw [hminor, (UpperTheory.val_det_eq_one_iff v
      (M.submatrix (Subtype.val : T → Fin n) (Subtype.val : T → Fin n)) (fun i j => h1 _ _)
      (fun i j h => h2 _ _ h)).2 fun i => hdiag _, mul_one]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (Matrix.diagonal d * M) (n - k) (by simp)
  rw [Fintype.card_fin, Nat.sub_sub_self hk] at hc
  have hmem : T ∈ Finset.powersetCard (n - k) (Finset.univ : Finset (Fin n)) := by
    simp [hcard]
  rw [hc, map_mul, map_pow, v.map_neg, map_one, one_pow, one_mul, v.map_sum_eq_of_lt hmem, hTval]
  intro S hS
  rw [hTval, hminor]
  simp only [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_singleton] at hS
  refine lt_of_le_of_lt
    (mul_le_of_le_one_right' (UpperTheory.valuation_det_le_one_of_entries_le_one' v _ fun i j => h1 _ _)) ?_
  refine UpperTheory.prod_lt_of_strictMono (fun i => v (d i)) hmono
    (fun i => zero_lt_iff.2 ((v.ne_zero_iff).2 (hd i))) S T (hS.1.2.trans hcard.symm) hS.2 ?_
  intro i j hi hj
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi hj
  exact Fin.lt_def.2 (lt_of_lt_of_le hi hj)
