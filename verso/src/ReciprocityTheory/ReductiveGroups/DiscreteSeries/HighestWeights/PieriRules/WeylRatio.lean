import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Establish `h1 : (univ.filter fun x => b < x ∧ ε x = ε b).card + 1 ≤ (univ.filter fun x => a < x ∧ ε x = ε a).card`. Apply `Nat.succ_le_of_lt` to reduce the goal to its premises. Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`. Conclude with `⟨b, by simp [hab, he], by simp⟩`.

Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`. Conclude with `⟨hab.trans hx.1, hx.2.trans he.symm⟩`. Establish `h2 : (univ.filter fun x => x < a ∧ ε x = ε a).card + 1 ≤ (univ.filter fun x => x < b ∧ ε x = ε b).card`. Apply `Nat.succ_le_of_lt` to reduce the goal to its premises.

Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`. Conclude with `⟨a, by simp [hab, he], by simp⟩`. Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`.

Conclude with `⟨hx.1.trans hab, hx.2.trans he⟩`. Establish `h1' : ((univ.filter fun x => b < x ∧ ε x = ε b).card : ℝ) + 1 ≤ ((univ.filter fun x => a < x ∧ ε x = ε a).card : ℝ)` using `by exact_mod_cast h1`. Establish `h2' : ((univ.filter fun x => x < a ∧ ε x = ε a).card : ℝ) + 1 ≤ ((univ.filter fun x => x < b ∧ ε x = ε b).card : ℝ)` using `by exact_mod_cast h2`. Simplify using `only [rhoC]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weylRatio_rhoC_sub_ge_one {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) : 1 ≤ rhoC ε a - rhoC ε b := by
  have h1 : (univ.filter fun x => b < x ∧ ε x = ε b).card + 1 ≤
      (univ.filter fun x => a < x ∧ ε x = ε a).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨b, by simp [hab, he], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hab.trans hx.1, hx.2.trans he.symm⟩
  have h2 : (univ.filter fun x => x < a ∧ ε x = ε a).card + 1 ≤
      (univ.filter fun x => x < b ∧ ε x = ε b).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, by simp [hab, he], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.1.trans hab, hx.2.trans he⟩
  have h1' : ((univ.filter fun x => b < x ∧ ε x = ε b).card : ℝ) + 1 ≤
      ((univ.filter fun x => a < x ∧ ε x = ε a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((univ.filter fun x => x < a ∧ ε x = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun x => x < b ∧ ε x = ε b).card : ℝ) := by exact_mod_cast h2
  simp only [rhoC]
  linarith

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase univ _ (Finset.mem_univ s)]`. Establish `h1 : ∏ b ∈ univ.filter (fun b => s < b ∧ ε s = ε b), (if b = s then h s else if s = s then h b else 1) = ∏ b ∈ univ.filter (fun b => s < b ∧ ε s = ε b), h b` using `Finset.prod_congr rfl fun b hb => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Simplify using `[ne_of_gt hb.1]`. Establish `h2 : ∏ a ∈ univ.erase s, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b), (if b = s then h a else if a = s then h b else 1) = ∏ a ∈ univ.filter (fun a => a < s ∧ ε a = ε s), h a`.

Rewrite using `[Finset.prod_filter, ← Finset.mul_prod_erase univ (fun a => if a < s ∧ ε a = ε s then h a else 1) (Finset.mem_univ s)]`. Simplify using `only [lt_self_iff_false, false_and, ↓reduceIte, one_mul]`. Use `Finset.prod_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `has : a ≠ s` using `Finset.ne_of_mem_erase ha`. Simplify using `only [has, ↓reduceIte]`.

Rewrite using `[Finset.prod_ite_eq']`. Simplify using `[Finset.mem_filter]`. Rewrite using `[h1, h2, ← Finset.prod_union]`. Use `congr 1`. Use extensionality with `b`.

Simplify using `only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨h1, h2⟩ | ⟨h1, h2⟩)`. Conclude with `⟨ne_of_gt h1, h2.symm⟩`. Conclude with `⟨ne_of_lt h1, h2⟩`.

Introduce and unpack `⟨h1, h2⟩`. Break down `lt_or_gt_of_ne h1 with h | h` into its components or cases. Conclude with `Or.inr ⟨h, h2⟩`. Conclude with `Or.inl ⟨h, h2.symm⟩`. Conclude with `Finset.disjoint_filter.mpr fun b _ h1 h2 => lt_asymm h1.1 h2.1`.
-/
theorem weylRatio_prodW {n : ℕ} (ε : Fin n → Bool) (s : Fin n) (h : Fin n → ℝ) :
    ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b),
        (if b = s then h a else if a = s then h b else 1) =
      ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), h b := by
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ s)]
  have h1 : ∏ b ∈ univ.filter (fun b => s < b ∧ ε s = ε b),
      (if b = s then h s else if s = s then h b else 1) =
        ∏ b ∈ univ.filter (fun b => s < b ∧ ε s = ε b), h b :=
    Finset.prod_congr rfl fun b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp [ne_of_gt hb.1]
  have h2 : ∏ a ∈ univ.erase s, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b),
      (if b = s then h a else if a = s then h b else 1) =
        ∏ a ∈ univ.filter (fun a => a < s ∧ ε a = ε s), h a := by
    rw [Finset.prod_filter,
      ← Finset.mul_prod_erase univ (fun a => if a < s ∧ ε a = ε s then h a else 1) (Finset.mem_univ s)]
    simp only [lt_self_iff_false, false_and, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun a ha => ?_
    have has : a ≠ s := Finset.ne_of_mem_erase ha
    simp only [has, ↓reduceIte]
    rw [Finset.prod_ite_eq']
    simp [Finset.mem_filter]
  rw [h1, h2, ← Finset.prod_union]
  · congr 1
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨ne_of_gt h1, h2.symm⟩
      · exact ⟨ne_of_lt h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl ⟨h, h2.symm⟩
  · exact Finset.disjoint_filter.mpr fun b _ h1 h2 => lt_asymm h1.1 h2.1

/- English proof (translation)
Rewrite using `[← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b), ← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b + c)]`. Simplify using `only [weylK]`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Establish `hab : a ≠ b` using `ne_of_lt hb.1`. Distinguish the cases in `hbs : b = s`. Substitute `hbs` using the available equality.

Simplify using `only [Pi.add_apply, Pi.single_apply, hab, ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `has : a = s`. Substitute `has` using the available equality. Simplify using `only [Pi.add_apply, Pi.single_apply, hbs, ↓reduceIte]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.add_apply, Pi.single_apply, hbs, has, ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weylK_shift_mul {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (s : Fin n) (c : ℝ) :
    weylK ε (Λ + Pi.single s c) *
        ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b) =
      weylK ε Λ *
        ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) := by
  rw [← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b),
    ← weylRatio_prodW ε s (fun b => (Λ + rhoC ε) s - (Λ + rhoC ε) b + c)]
  simp only [weylK]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hab : a ≠ b := ne_of_lt hb.1
  by_cases hbs : b = s
  · subst hbs
    simp only [Pi.add_apply, Pi.single_apply, hab, ↓reduceIte]
    ring
  · by_cases has : a = s
    · subst has
      simp only [Pi.add_apply, Pi.single_apply, hbs, ↓reduceIte]
      ring
    · simp only [Pi.add_apply, Pi.single_apply, hbs, has, ↓reduceIte]
      ring

/- English proof (translation)
Introduce `h`. Simplify using `only [Pi.add_apply] at h`. Break down `lt_or_gt_of_ne hbs with hlt | hlt` into its components or cases. Establish `h1` using `weylRatio_rhoC_sub_ge_one ε hlt he`. Establish `h2` using `hΛ b s hlt he`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `weylRatio_rhoC_sub_ge_one ε hlt he.symm`. Establish `h2` using `hΛ s b hlt he.symm`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weylRatio_ell_ne {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) {s b : Fin n}
    (hbs : b ≠ s) (he : ε b = ε s) : (Λ + rhoC ε) s - (Λ + rhoC ε) b ≠ 0 := by
  intro h
  simp only [Pi.add_apply] at h
  rcases lt_or_gt_of_ne hbs with hlt | hlt
  · have h1 := weylRatio_rhoC_sub_ge_one ε hlt he
    have h2 := hΛ b s hlt he
    linarith
  · have h1 := weylRatio_rhoC_sub_ge_one ε hlt he.symm
    have h2 := hΛ s b hlt he.symm
    linarith

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun b hb => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb exact weylRatio_ell_ne ε Λ hΛ hb.1 hb.2`.
-/
theorem weylRatio_prod_ne {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n) :
    ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s), ((Λ + rhoC ε) s - (Λ + rhoC ε) b) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun b hb => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact weylRatio_ell_ne ε Λ hΛ hb.1 hb.2

/- English proof (translation)
Rewrite using `[Finset.prod_div_distrib, ← mul_div_assoc, eq_div_iff (weylRatio_prod_ne ε Λ hΛ s)]`. Conclude with `weylK_shift_mul ε Λ s c`.
-/
theorem weylK_shift {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n) (c : ℝ) :
    weylK ε (Λ + Pi.single s c) =
      weylK ε Λ * ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
        (((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b)) := by
  rw [Finset.prod_div_distrib, ← mul_div_assoc, eq_div_iff (weylRatio_prod_ne ε Λ hΛ s)]
  exact weylK_shift_mul ε Λ s c

/- English proof (translation)
Establish `h : c • (Pi.single s (1 : ℝ) : Fin n → ℝ) = Pi.single s c`. Use extensionality with `x`. Apply the tactic sequence `by_cases hx : x = s <;> simp [hx]`. Rewrite using `[h]`. Conclude with `weylK_shift ε Λ hΛ s c`.
-/
theorem weylK_add_smul_single {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (s : Fin n)
    (c : ℝ) :
    weylK ε (Λ + c • (Pi.single s (1 : ℝ) : Fin n → ℝ)) = weylK ε Λ *
      ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
        ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b) := by
  have h : c • (Pi.single s (1 : ℝ) : Fin n → ℝ) = Pi.single s c := by
    ext x
    by_cases hx : x = s <;> simp [hx]
  rw [h]
  exact weylK_shift ε Λ hΛ s c

/- English proof (translation)
Establish `hji : j ≠ i` using `fun h => hij (by rw [h])`. Establish `hF : ∀ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b = (Λ + rhoC ε) j - (Λ + rhoC ε) b`. Introduce `b hb`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Establish `hbi : b ≠ i` using `fun h => hij (by rw [← h, hb.2])`.

Simplify using `only [Pi.add_apply, Pi.single_apply, hji, hbi, ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree. Establish `hP0 : ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b) = ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + rhoC ε) j - (Λ + rhoC ε) b)` using `Finset.prod_congr rfl hF`. Establish `hP1 : ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b + -1) = ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1)` using `Finset.prod_congr rfl fun b hb => by rw [hF b hb]; ring`. Establish `hmul` using `weylK_shift_mul ε (Λ + Pi.single i 1) j (-1)`.

Rewrite `hmul` using `[hP0, hP1, weylK_shift ε Λ hΛ i 1]`. Establish `hΛe : Λ + (Pi.single i 1 - Pi.single j 1) = Λ + Pi.single i 1 + Pi.single j (-1)`. Rewrite using `[sub_eq_add_neg, ← Pi.single_neg, add_assoc]`. Rewrite using `[hΛe, Finset.prod_div_distrib (s := univ.filter (fun b => b ≠ j ∧ ε b = ε j)), ← mul_div_assoc, eq_div_iff (weylRatio_prod_ne ε Λ hΛ j), hmul]`.
-/
theorem weylK_two {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) {i j : Fin n}
    (hij : ε i ≠ ε j) :
    weylK ε (Λ + (Pi.single i 1 - Pi.single j 1)) =
      weylK ε Λ *
        (∏ b ∈ univ.filter (fun b => b ≠ i ∧ ε b = ε i),
          (((Λ + rhoC ε) i - (Λ + rhoC ε) b + 1) / ((Λ + rhoC ε) i - (Λ + rhoC ε) b))) *
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
          (((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) / ((Λ + rhoC ε) j - (Λ + rhoC ε) b)) := by
  have hji : j ≠ i := fun h => hij (by rw [h])
  have hF : ∀ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b =
        (Λ + rhoC ε) j - (Λ + rhoC ε) b := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hbi : b ≠ i := fun h => hij (by rw [← h, hb.2])
    simp only [Pi.add_apply, Pi.single_apply, hji, hbi, ↓reduceIte]
    ring
  have hP0 : ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      ((Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b) =
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + rhoC ε) j - (Λ + rhoC ε) b) :=
    Finset.prod_congr rfl hF
  have hP1 : ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      ((Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b + -1) =
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) :=
    Finset.prod_congr rfl fun b hb => by rw [hF b hb]; ring
  have hmul := weylK_shift_mul ε (Λ + Pi.single i 1) j (-1)
  rw [hP0, hP1, weylK_shift ε Λ hΛ i 1] at hmul
  have hΛe : Λ + (Pi.single i 1 - Pi.single j 1) = Λ + Pi.single i 1 + Pi.single j (-1) := by
    rw [sub_eq_add_neg, ← Pi.single_neg, add_assoc]
  rw [hΛe, Finset.prod_div_distrib (s := univ.filter (fun b => b ≠ j ∧ ε b = ε j)), ← mul_div_assoc, eq_div_iff (weylRatio_prod_ne ε Λ hΛ j), hmul]

/- English proof (translation)
The claim follows from `weylK_two ε Λ hΛ hij`.
-/
theorem weylK_add_single_sub_single {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ)
    (i j : Fin n) (hij : ε i ≠ ε j) :
    weylK ε (Λ + ((Pi.single i (1 : ℝ) : Fin n → ℝ) - Pi.single j 1)) = weylK ε Λ *
      (∏ b ∈ univ.filter (fun b => b ≠ i ∧ ε b = ε i),
        ((Λ + rhoC ε) i - (Λ + rhoC ε) b + 1) / ((Λ + rhoC ε) i - (Λ + rhoC ε) b)) *
      (∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
        ((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) / ((Λ + rhoC ε) j - (Λ + rhoC ε) b)) :=
  weylK_two ε Λ hΛ hij

end ReciprocityTheory.ChartRestriction.DS.HW
