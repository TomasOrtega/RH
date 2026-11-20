import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylPos

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Unfold `weylK`. Use `Finset.prod_eq_zero (Finset.mem_univ a) ?_` and prove the remaining obligations. Use `Finset.prod_eq_zero (i := b) (Finset.mem_filter.2 ⟨Finset.mem_univ b, hab, hε⟩) ?_` and prove the remaining obligations. Rewrite using `[h, sub_self, zero_div]`.
-/
theorem weylK_eq_zero_of_eq (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) (hε : ε a = ε b)
    (h : (μ + rhoC ε) a = (μ + rhoC ε) b) : weylK ε μ = 0 := by
  unfold weylK
  refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
  refine Finset.prod_eq_zero (i := b) (Finset.mem_filter.2 ⟨Finset.mem_univ b, hab, hε⟩) ?_
  rw [h, sub_self, zero_div]

/- English proof (translation)
Use `set S := univ.filter fun c => c < s ∧ ε c = ε s with hS`. Establish `hne : S.Nonempty` using `⟨a, by simp [hS, has, hε]⟩`. Establish `hm` using `S.max'_mem hne`. Simplify using `only [hS, mem_filter, mem_univ, true_and] at hm`. Use `⟨S.max' hne, S.le_max' a (by simp [hS, has, hε]), hm.1, hm.2, fun c h1 h2 he => ?_⟩` and prove the remaining obligations.

Establish `: c ∈ S` using `by simp [hS, h2, he.trans hm.2]`. Conclude with `absurd (S.le_max' c this) (not_le.2 h1)`.
-/
theorem exists_consec_pred (ε : Fin n → Bool) {a s : Fin n} (has : a < s) (hε : ε a = ε s) :
    ∃ a', a ≤ a' ∧ a' < s ∧ ε a' = ε s ∧ ∀ c, a' < c → c < s → ε c ≠ ε a' := by
  set S := univ.filter fun c => c < s ∧ ε c = ε s with hS
  have hne : S.Nonempty := ⟨a, by simp [hS, has, hε]⟩
  have hm := S.max'_mem hne
  simp only [hS, mem_filter, mem_univ, true_and] at hm
  refine ⟨S.max' hne, S.le_max' a (by simp [hS, has, hε]), hm.1, hm.2, fun c h1 h2 he => ?_⟩
  have : c ∈ S := by simp [hS, h2, he.trans hm.2]
  exact absurd (S.le_max' c this) (not_le.2 h1)

/- English proof (translation)
Use `set S := univ.filter fun c => s < c ∧ ε c = ε s with hS`. Establish `hne : S.Nonempty` using `⟨b, by simp [hS, hsb, hε]⟩`. Establish `hm` using `S.min'_mem hne`. Simplify using `only [hS, mem_filter, mem_univ, true_and] at hm`. Use `⟨S.min' hne, hm.1, S.min'_le b (by simp [hS, hsb, hε]), hm.2.symm, fun c h1 h2 he => ?_⟩` and prove the remaining obligations.

Establish `: c ∈ S` using `by simp [hS, h1, he]`. Conclude with `absurd (S.min'_le c this) (not_le.2 h2)`.
-/
theorem exists_consec_succ (ε : Fin n → Bool) {s b : Fin n} (hsb : s < b) (hε : ε s = ε b) :
    ∃ b', s < b' ∧ b' ≤ b ∧ ε s = ε b' ∧ ∀ c, s < c → c < b' → ε c ≠ ε s := by
  set S := univ.filter fun c => s < c ∧ ε c = ε s with hS
  have hne : S.Nonempty := ⟨b, by simp [hS, hsb, hε]⟩
  have hm := S.min'_mem hne
  simp only [hS, mem_filter, mem_univ, true_and] at hm
  refine ⟨S.min' hne, hm.1, S.min'_le b (by simp [hS, hsb, hε]), hm.2.symm, fun c h1 h2 he => ?_⟩
  have : c ∈ S := by simp [hS, h1, he]
  exact absurd (S.min'_le c this) (not_le.2 h2)

/- English proof (translation)
Take `⟨m, rfl⟩` from `hx`. Take `⟨k, rfl⟩` from `hy`. Establish `e1 : m ≤ k` using `by exact_mod_cast h1`. Establish `e2 : k < m + 1` using `by exact_mod_cast h2`. Establish `: k = m` using `by omega`.

Rewrite using `[this]`.
-/
private theorem int_eq_of_le_lt {x y : ℝ} (hx : ∃ m : ℤ, x = m) (hy : ∃ m : ℤ, y = m) (h1 : x ≤ y)
    (h2 : y < x + 1) : y = x := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  have e1 : m ≤ k := by exact_mod_cast h1
  have e2 : k < m + 1 := by exact_mod_cast h2
  have : k = m := by omega
  rw [this]

/- English proof (translation)
Establish `hbs' : ε b = ε s` using `hε.symm.trans has`. Establish `hma` using `hμ a has`. Establish `hmb` using `hμ b hbs'`. Establish `hΛ` using `hdom a b hab hε`. Establish `hbs : b = s`.

Assume the negation of the conclusion as `hne`. Rewrite `hmb` using `[if_neg hne]`. Apply the tactic sequence `split_ifs at hma <;> linarith`. Substitute `hbs` using the available equality. Establish `has' : a ≠ b` using `ne_of_lt hab`.

Rewrite `hma` using `[if_neg has']`. Rewrite `hmb` using `[if_pos rfl]`. Establish `hEq : Λ a = Λ b` using `int_eq_of_le_lt (hint b) (hint a) hΛ (by linarith)`. Take `⟨a', haa', ha's, hε', hc⟩` from `exists_consec_pred ε hab hε`. Establish `hΛ' : Λ a' = Λ b`.

Establish `h1 : Λ b ≤ Λ a'` using `hdom a' b ha's hε'`. Establish `h2 : Λ a' ≤ Λ a`. Break down `eq_or_lt_of_le haa' with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hdom a a' h (hε.trans hε'.symm)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρ` using `rhoC_consec ε ha's hε' hc`. Establish `hma'` using `hμ a' hε'`. Rewrite `hma'` using `[if_neg (ne_of_lt ha's)]`. Use `weylK_eq_zero_of_eq ε μ ha's hε' ?_` and prove the remaining obligations.

Simplify using `only [Pi.add_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weylK_eq_zero_of_up (ε : Fin n → Bool) (Λ μ : Fin n → ℝ) (s : Fin n) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (hμ : ∀ c, ε c = ε s → μ c = Λ c + if c = s then 1 else 0)
    {a b : Fin n} (hab : a < b) (hε : ε a = ε b) (has : ε a = ε s) (hlt : μ a < μ b) : weylK ε μ = 0 := by
  have hbs' : ε b = ε s := hε.symm.trans has
  have hma := hμ a has
  have hmb := hμ b hbs'
  have hΛ := hdom a b hab hε

  have hbs : b = s := by
    by_contra hne
    rw [if_neg hne] at hmb
    split_ifs at hma <;> linarith
  subst hbs
  have has' : a ≠ b := ne_of_lt hab
  rw [if_neg has'] at hma
  rw [if_pos rfl] at hmb
  have hEq : Λ a = Λ b := int_eq_of_le_lt (hint b) (hint a) hΛ (by linarith)
  obtain ⟨a', haa', ha's, hε', hc⟩ := exists_consec_pred ε hab hε
  have hΛ' : Λ a' = Λ b := by
    have h1 : Λ b ≤ Λ a' := hdom a' b ha's hε'
    have h2 : Λ a' ≤ Λ a := by
      rcases eq_or_lt_of_le haa' with h | h
      · rw [h]
      · exact hdom a a' h (hε.trans hε'.symm)
    linarith
  have hρ := rhoC_consec ε ha's hε' hc
  have hma' := hμ a' hε'
  rw [if_neg (ne_of_lt ha's)] at hma'
  refine weylK_eq_zero_of_eq ε μ ha's hε' ?_
  simp only [Pi.add_apply]
  linarith

/- English proof (translation)
Establish `hbs' : ε b = ε s` using `hε.symm.trans has`. Establish `hma` using `hμ a has`. Establish `hmb` using `hμ b hbs'`. Establish `hΛ` using `hdom a b hab hε`. Establish `has : a = s`.

Assume the negation of the conclusion as `hne`. Rewrite `hma` using `[if_neg hne]`. Apply the tactic sequence `split_ifs at hmb <;> linarith`. Substitute `has` using the available equality. Rewrite `hmb` using `[if_neg (ne_of_lt hab).symm]`.

Rewrite `hma` using `[if_pos rfl]`. Establish `hEq : Λ a = Λ b` using `int_eq_of_le_lt (hint b) (hint a) hΛ (by linarith)`. Take `⟨b', hab', hb'b, hε', hc⟩` from `exists_consec_succ ε hab hε`. Establish `hΛ' : Λ b' = Λ a`. Establish `h1 : Λ b' ≤ Λ a` using `hdom a b' hab' hε'`.

Establish `h2 : Λ b ≤ Λ b'`. Break down `eq_or_lt_of_le hb'b with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hdom b' b h (hε'.symm.trans hε)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hρ` using `rhoC_consec ε hab' hε' hc`. Establish `hmb'` using `hμ b' hε'.symm`. Rewrite `hmb'` using `[if_neg (ne_of_lt hab').symm]`. Use `weylK_eq_zero_of_eq ε μ hab' hε' ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weylK_eq_zero_of_down (ε : Fin n → Bool) (Λ μ : Fin n → ℝ) (s : Fin n) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (hμ : ∀ c, ε c = ε s → μ c = Λ c - if c = s then 1 else 0)
    {a b : Fin n} (hab : a < b) (hε : ε a = ε b) (has : ε a = ε s) (hlt : μ a < μ b) : weylK ε μ = 0 := by
  have hbs' : ε b = ε s := hε.symm.trans has
  have hma := hμ a has
  have hmb := hμ b hbs'
  have hΛ := hdom a b hab hε

  have has : a = s := by
    by_contra hne
    rw [if_neg hne] at hma
    split_ifs at hmb <;> linarith
  subst has
  rw [if_neg (ne_of_lt hab).symm] at hmb
  rw [if_pos rfl] at hma
  have hEq : Λ a = Λ b := int_eq_of_le_lt (hint b) (hint a) hΛ (by linarith)
  obtain ⟨b', hab', hb'b, hε', hc⟩ := exists_consec_succ ε hab hε
  have hΛ' : Λ b' = Λ a := by
    have h1 : Λ b' ≤ Λ a := hdom a b' hab' hε'
    have h2 : Λ b ≤ Λ b' := by
      rcases eq_or_lt_of_le hb'b with h | h
      · rw [h]
      · exact hdom b' b h (hε'.symm.trans hε)
    linarith
  have hρ := rhoC_consec ε hab' hε' hc
  have hmb' := hμ b' hε'.symm
  rw [if_neg (ne_of_lt hab').symm] at hmb'
  refine weylK_eq_zero_of_eq ε μ hab' hε' ?_
  simp only [Pi.add_apply]
  linarith

/- English proof (translation)
Unfold `KDom at h`. Use `push Not at h`. Take `⟨a, b, hab, hε, hlt⟩` from `h`. Conclude with `⟨a, b, hab, hε, hlt⟩`.
-/
theorem exists_viol_of_not_kDom (ε : Fin n → Bool) (μ : Fin n → ℝ) (h : ¬ KDom ε μ) :
    ∃ a b, a < b ∧ ε a = ε b ∧ μ a < μ b := by
  unfold KDom at h
  push Not at h
  obtain ⟨a, b, hab, hε, hlt⟩ := h
  exact ⟨a, b, hab, hε, hlt⟩

/- English proof (translation)
Take `⟨a, b, hab, hε, hlt⟩` from `exists_viol_of_not_kDom ε _ h`. Establish `hμ : ∀ c, (Λ + stdWt n s) c = Λ c + if c = s then 1 else 0`. Introduce `c`. Simplify using `only [Pi.add_apply, stdWt, Pi.single_apply]`. Distinguish the cases in `has : ε a = ε s`.

Conclude with `weylK_eq_zero_of_up ε Λ _ s hint hdom (fun c _ => hμ c) hab hε has hlt`. It suffices to derive a contradiction. Establish `ha : a ≠ s` using `fun h => has (h ▸ rfl)`. Establish `hb : b ≠ s` using `fun h => has (h ▸ hε)`. Rewrite `hlt` using `[hμ, hμ, if_neg ha, if_neg hb]`.

Combine the linear relations using `[hdom a b hab hε]`.
-/
theorem weylK_std_vanish (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (s : Fin n) (h : ¬ KDom ε (Λ + stdWt n s)) : weylK ε (Λ + stdWt n s) = 0 := by
  obtain ⟨a, b, hab, hε, hlt⟩ := exists_viol_of_not_kDom ε _ h
  have hμ : ∀ c, (Λ + stdWt n s) c = Λ c + if c = s then 1 else 0 := by
    intro c
    simp only [Pi.add_apply, stdWt, Pi.single_apply]
  by_cases has : ε a = ε s
  · exact weylK_eq_zero_of_up ε Λ _ s hint hdom (fun c _ => hμ c) hab hε has hlt
  · exfalso
    have ha : a ≠ s := fun h => has (h ▸ rfl)
    have hb : b ≠ s := fun h => has (h ▸ hε)
    rw [hμ, hμ, if_neg ha, if_neg hb] at hlt
    linarith [hdom a b hab hε]

/- English proof (translation)
Take `⟨a, b, hab, hε, hlt⟩` from `exists_viol_of_not_kDom ε _ h`. Establish `hμ : ∀ c, (Λ + dualWt n s) c = Λ c - if c = s then 1 else 0`. Introduce `c`. Simplify using `only [Pi.add_apply, dualWt, Pi.neg_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> ring`.

Distinguish the cases in `has : ε a = ε s`. Conclude with `weylK_eq_zero_of_down ε Λ _ s hint hdom (fun c _ => hμ c) hab hε has hlt`. It suffices to derive a contradiction. Establish `ha : a ≠ s` using `fun h => has (h ▸ rfl)`. Establish `hb : b ≠ s` using `fun h => has (h ▸ hε)`.

Rewrite `hlt` using `[hμ, hμ, if_neg ha, if_neg hb]`. Combine the linear relations using `[hdom a b hab hε]`.
-/
theorem weylK_dual_vanish (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (s : Fin n) (h : ¬ KDom ε (Λ + dualWt n s)) : weylK ε (Λ + dualWt n s) = 0 := by
  obtain ⟨a, b, hab, hε, hlt⟩ := exists_viol_of_not_kDom ε _ h
  have hμ : ∀ c, (Λ + dualWt n s) c = Λ c - if c = s then 1 else 0 := by
    intro c
    simp only [Pi.add_apply, dualWt, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> ring
  by_cases has : ε a = ε s
  · exact weylK_eq_zero_of_down ε Λ _ s hint hdom (fun c _ => hμ c) hab hε has hlt
  · exfalso
    have ha : a ≠ s := fun h => has (h ▸ rfl)
    have hb : b ≠ s := fun h => has (h ▸ hε)
    rw [hμ, hμ, if_neg ha, if_neg hb] at hlt
    linarith [hdom a b hab hε]

/- English proof (translation)
Take `⟨⟨i, j⟩, hi, hj⟩` from `p`. Take `⟨a, b, hab, hε, hlt⟩` from `exists_viol_of_not_kDom ε _ h`. Establish `hμ : ∀ c, (Λ + pWt ε β ⟨(i, j), hi, hj⟩) c = Λ c + (if c = i then 1 else 0) - (if c = j then 1 else 0)`. Introduce `c`. Simplify using `only [Pi.add_apply, pWt, Pi.sub_apply, Pi.single_apply]`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hai : ε a = ε i`. Use `weylK_eq_zero_of_up ε Λ _ i hint hdom (fun c hc => ?_) hab hε hai hlt` and prove the remaining obligations. Establish `hcj : c ≠ j`. Introduce and unpack `rfl`.

Simplify using `only at hi hj`. Rewrite `hj` using `[hc, hi]`. Apply the tactic sequence `cases β <;> simp at hj`. Rewrite using `[hμ, if_neg hcj, sub_zero]`. Establish `haj : ε a = ε j`.

Simplify using `only at hi hj`. Rewrite `hai` using `[hi]`. Rewrite using `[hj]`. Apply the tactic sequence `cases h1 : ε a <;> cases β <;> simp_all`. Use `weylK_eq_zero_of_down ε Λ _ j hint hdom (fun c hc => ?_) hab hε haj hlt` and prove the remaining obligations.

Establish `hci : c ≠ i`. Introduce and unpack `rfl`. Conclude with `hai (haj.trans hc.symm)`. Rewrite using `[hμ, if_neg hci, add_zero]`.
-/
theorem weylK_p_vanish (ε : Fin n → Bool) (β : Bool) (Λ : Fin n → ℝ) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (p : pIdx ε β) (h : ¬ KDom ε (Λ + pWt ε β p)) : weylK ε (Λ + pWt ε β p) = 0 := by
  obtain ⟨⟨i, j⟩, hi, hj⟩ := p
  obtain ⟨a, b, hab, hε, hlt⟩ := exists_viol_of_not_kDom ε _ h
  have hμ : ∀ c, (Λ + pWt ε β ⟨(i, j), hi, hj⟩) c =
      Λ c + (if c = i then 1 else 0) - (if c = j then 1 else 0) := by
    intro c
    simp only [Pi.add_apply, pWt, Pi.sub_apply, Pi.single_apply]
    ring
  by_cases hai : ε a = ε i
  ·
    refine weylK_eq_zero_of_up ε Λ _ i hint hdom (fun c hc => ?_) hab hε hai hlt
    have hcj : c ≠ j := by
      rintro rfl
      simp only at hi hj
      rw [hc, hi] at hj
      cases β <;> simp at hj
    rw [hμ, if_neg hcj, sub_zero]
  ·
    have haj : ε a = ε j := by
      simp only at hi hj
      rw [hi] at hai
      rw [hj]
      cases h1 : ε a <;> cases β <;> simp_all
    refine weylK_eq_zero_of_down ε Λ _ j hint hdom (fun c hc => ?_) hab hε haj hlt
    have hci : c ≠ i := by
      rintro rfl
      exact hai (haj.trans hc.symm)
    rw [hμ, if_neg hci, add_zero]

end ReciprocityTheory.ChartRestriction.DS.HW
