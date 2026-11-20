import Mathlib

/- English proof (translation)
Introduce `s L g ⟨a, haL, ha⟩`. Take `⟨a0, ha0L, ha0⟩` from `L.exists_min_image g ⟨a, haL⟩`. Establish `hm0 : g a0 ≤ 0` using `le_trans (ha0 a haL) ha`. Set `S : ℤ → Finset (Fin s)` to `fun t => L.filter (fun x => g x ≤ t)`. Set `J : ℤ → Prop` to `fun t => g a0 ≤ t ∧ t + 1 ≤ ((S t).card : ℤ) ∧ 2 * ∑ x ∈ S t, g x ≤ ((S t).card : ℤ) * (((S t).card : ℤ) - 1)`.

Establish `base : J (g a0)`. Establish `hmem : a0 ∈ S (g a0)` using `Finset.mem_filter.2 ⟨ha0L, le_refl _⟩`. Establish `hpos : 1 ≤ ((S (g a0)).card : ℤ)`. Conclude with `Finset.card_pos.2 ⟨a0, hmem⟩` after adjusting the coercions. Establish `hsum : ∑ x ∈ S (g a0), g x ≤ 0` using `Finset.sum_nonpos (fun x hx => le_trans (Finset.mem_filter.1 hx).2 hm0)`.

Use `⟨le_refl _, by linarith, ?_⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Establish `step : ∀ t, J t → (∃ b ∈ L, g b = t + 1) → J (t + 1)`. Introduce `t ⟨hmt, hk, hs⟩ ⟨b, hbL, hb⟩`. Set `E` to `L.filter (fun x => g x = t + 1)`.

Establish `hsplit : S (t + 1) = S t ∪ E` using `by show L.filter _ = L.filter _ ∪ L.filter _`. Rewrite using `[← Finset.filter_or]`. Conclude with `Finset.filter_congr (fun x _ => by omega)`. Establish `hdisj : Disjoint (S t) E` using `Finset.disjoint_filter.2 (fun x _ h1 h2 => by omega)`. Establish `hcard : ((S (t + 1)).card : ℤ) = (S t).card + E.card`.

Rewrite using `[hsplit, Finset.card_union_of_disjoint hdisj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsumE : ∑ x ∈ E, g x = (E.card : ℤ) * (t + 1)`. Rewrite using `[Finset.sum_eq_card_nsmul (fun x hx => (Finset.mem_filter.1 hx).2), nsmul_eq_mul]`.

Establish `hsum : ∑ x ∈ S (t + 1), g x = ∑ x ∈ S t, g x + (E.card : ℤ) * (t + 1)`. Rewrite using `[hsplit, Finset.sum_union hdisj, hsumE]`. Establish `hc : 1 ≤ (E.card : ℤ)`. Conclude with `Finset.card_pos.2 ⟨b, Finset.mem_filter.2 ⟨hbL, hb⟩⟩` after adjusting the coercions. Use `⟨by linarith, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcard]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hcard, hsum]`. Establish `h1 : (E.card : ℤ) * (t + 1) ≤ (E.card : ℤ) * (S t).card` using `mul_le_mul_of_nonneg_left hk (by linarith)`. Establish `h2 : 0 ≤ (E.card : ℤ) * ((E.card : ℤ) - 1)` using `mul_nonneg (by linarith) (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `key : ∃ t, J t ∧ ∀ b ∈ L, g b ≠ t + 1`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hall : ∀ n : ℕ, J (g a0 + n)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using base`. Consider the case `succ n ih`. Use `step _ ih (hne _ ih)` as an intermediate fact.

Use `push_cast`. Rewrite using `[← add_assoc]` and apply the resulting hypothesis. Establish `hn : (((-g a0).toNat : ℕ) : ℤ) = -g a0` using `Int.toNat_of_nonneg (by linarith)`. Establish `h1` using `(hall (L.card + (-g a0).toNat)).2.1`. Establish `hle : (S (g a0 + ((L.card + (-g a0).toNat : ℕ) : ℤ))).card ≤ L.card` using `Finset.card_filter_le _ _`.

Establish `hle' : ((S (g a0 + ((L.card + (-g a0).toNat : ℕ) : ℤ))).card : ℤ) ≤ L.card`. Conclude with `hle` after adjusting the coercions. Move the coercions through the operations in `at h1 hle'`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨t, ⟨hmt, hk, hs⟩, hgap⟩` from `key`.

Use `⟨S t, Finset.filter_subset _ _, ⟨a0, Finset.mem_filter.2 ⟨ha0L, hmt⟩⟩, ?_, hs⟩` and prove the remaining obligations. Introduce `x hx b hbL hbS`. Establish `hx'` using `(Finset.mem_filter.1 hx).2`. Establish `hnb : ¬ g b ≤ t` using `fun h => hbS (Finset.mem_filter.2 ⟨hbL, h⟩)`. Establish `hne` using `hgap b hbL`.

Conclude with `le_abs.mpr (Or.inr (by omega))`.
-/
theorem UpperTheory.Lit.Mix.comb :
    ∀ (s : ℕ) (L : Finset (Fin s)) (g : Fin s → ℤ), (∃ a ∈ L, g a ≤ 0) → ∃ S : Finset (Fin s), S ⊆ L ∧ S.Nonempty ∧ (∀ a ∈ S, ∀ b ∈ L, b ∉ S → 2 ≤ |g a - g b|) ∧ 2 * ∑ a ∈ S, g a ≤ (S.card : ℤ) * ((S.card : ℤ) - 1) := by
  intro s L g ⟨a, haL, ha⟩
  obtain ⟨a0, ha0L, ha0⟩ := L.exists_min_image g ⟨a, haL⟩
  have hm0 : g a0 ≤ 0 := le_trans (ha0 a haL) ha
  let S : ℤ → Finset (Fin s) := fun t => L.filter (fun x => g x ≤ t)
  let J : ℤ → Prop := fun t => g a0 ≤ t ∧ t + 1 ≤ ((S t).card : ℤ) ∧
    2 * ∑ x ∈ S t, g x ≤ ((S t).card : ℤ) * (((S t).card : ℤ) - 1)
  have base : J (g a0) := by
    have hmem : a0 ∈ S (g a0) := Finset.mem_filter.2 ⟨ha0L, le_refl _⟩
    have hpos : 1 ≤ ((S (g a0)).card : ℤ) := by
      exact_mod_cast Finset.card_pos.2 ⟨a0, hmem⟩
    have hsum : ∑ x ∈ S (g a0), g x ≤ 0 :=
      Finset.sum_nonpos (fun x hx => le_trans (Finset.mem_filter.1 hx).2 hm0)
    refine ⟨le_refl _, by linarith, ?_⟩
    nlinarith
  have step : ∀ t, J t → (∃ b ∈ L, g b = t + 1) → J (t + 1) := by
    intro t ⟨hmt, hk, hs⟩ ⟨b, hbL, hb⟩
    let E := L.filter (fun x => g x = t + 1)
    have hsplit : S (t + 1) = S t ∪ E := by
      show L.filter _ = L.filter _ ∪ L.filter _
      rw [← Finset.filter_or]
      exact Finset.filter_congr (fun x _ => by omega)
    have hdisj : Disjoint (S t) E :=
      Finset.disjoint_filter.2 (fun x _ h1 h2 => by omega)
    have hcard : ((S (t + 1)).card : ℤ) = (S t).card + E.card := by
      rw [hsplit, Finset.card_union_of_disjoint hdisj]; push_cast; ring
    have hsumE : ∑ x ∈ E, g x = (E.card : ℤ) * (t + 1) := by
      rw [Finset.sum_eq_card_nsmul (fun x hx => (Finset.mem_filter.1 hx).2), nsmul_eq_mul]
    have hsum : ∑ x ∈ S (t + 1), g x = ∑ x ∈ S t, g x + (E.card : ℤ) * (t + 1) := by
      rw [hsplit, Finset.sum_union hdisj, hsumE]
    have hc : 1 ≤ (E.card : ℤ) := by
      exact_mod_cast Finset.card_pos.2 ⟨b, Finset.mem_filter.2 ⟨hbL, hb⟩⟩
    refine ⟨by linarith, ?_, ?_⟩
    · rw [hcard]; linarith
    · rw [hcard, hsum]
      have h1 : (E.card : ℤ) * (t + 1) ≤ (E.card : ℤ) * (S t).card :=
        mul_le_mul_of_nonneg_left hk (by linarith)
      have h2 : 0 ≤ (E.card : ℤ) * ((E.card : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  have key : ∃ t, J t ∧ ∀ b ∈ L, g b ≠ t + 1 := by
    by_contra hne
    push_neg at hne
    have hall : ∀ n : ℕ, J (g a0 + n) := by
      intro n
      induction n with
      | zero => simpa using base
      | succ n ih =>
        have := step _ ih (hne _ ih)
        push_cast
        rwa [← add_assoc]
    have hn : (((-g a0).toNat : ℕ) : ℤ) = -g a0 := Int.toNat_of_nonneg (by linarith)
    have h1 := (hall (L.card + (-g a0).toNat)).2.1
    have hle : (S (g a0 + ((L.card + (-g a0).toNat : ℕ) : ℤ))).card ≤ L.card :=
      Finset.card_filter_le _ _
    have hle' : ((S (g a0 + ((L.card + (-g a0).toNat : ℕ) : ℤ))).card : ℤ) ≤ L.card := by
      exact_mod_cast hle
    push_cast at h1 hle'
    linarith
  obtain ⟨t, ⟨hmt, hk, hs⟩, hgap⟩ := key
  refine ⟨S t, Finset.filter_subset _ _, ⟨a0, Finset.mem_filter.2 ⟨ha0L, hmt⟩⟩, ?_, hs⟩
  intro x hx b hbL hbS
  have hx' := (Finset.mem_filter.1 hx).2
  have hnb : ¬ g b ≤ t := fun h => hbS (Finset.mem_filter.2 ⟨hbL, h⟩)
  have hne := hgap b hbL
  exact le_abs.mpr (Or.inr (by omega))
