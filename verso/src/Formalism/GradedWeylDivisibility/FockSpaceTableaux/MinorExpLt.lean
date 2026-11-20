import Formalism.GradedWeylDivisibility.StatementC

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(simp only [cmIdx, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, finProdFinEquiv_apply_val]; done)`. Consider the case `(simp [cmIdx, finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]; done)`. Consider the case `(simp [cmIdx]; ring)`.
-/
private theorem cmIdx_val_eq {r n : ℕ} (v : Fin r × Fin n) :
    ((cmIdx r n v : Fin (n * r)) : ℕ) = v.1.val + r * v.2.val := by
  first
  | rfl
  | (simp only [cmIdx, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
      Prod.snd_swap, finProdFinEquiv_apply_val]; done)
  | (simp [cmIdx, finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]; done)
  | (simp [cmIdx]; ring)

/- English proof (translation)
Establish `h0 : ((cmIdx r n v : Fin (n * r)) : ℕ) < ((cmIdx r n w : Fin (n * r)) : ℕ)` using `h`. Rewrite `h0` using `[cmIdx_val_eq, cmIdx_val_eq]`. Establish `hv1` using `v.1.isLt`. Establish `hw1` using `w.1.isLt`. Break down `lt_trichotomy v.2.val w.2.val with h1 | h1 | h1` into its components or cases.

Conclude with `Or.inl h1`. Use `Or.inr ⟨Fin.ext h1, ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[h1]`. Use `show v.1.val < w.1.val`. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Establish `hm : r * (w.2.val + 1) ≤ r * v.2.val` using `by first`. Consider the case `exact Nat.mul_le_mul_left r h1`. Consider the case `exact Nat.mul_le_mul_left h1 r`. Consider the case `exact Nat.mul_le_mul (le_refl r) h1`.

Rewrite `hm` using `[Nat.mul_add, Nat.mul_one]`. Use `first`. Consider the case `omega`. Consider the case `linarith`.
-/
private theorem col_lt_or_col_eq_row_lt_of_cmIdx_lt {r n : ℕ} {v w : Fin r × Fin n}
    (h : cmIdx r n v < cmIdx r n w) :
    v.2.val < w.2.val ∨ (v.2 = w.2 ∧ v.1 < w.1) := by
  have h0 : ((cmIdx r n v : Fin (n * r)) : ℕ) < ((cmIdx r n w : Fin (n * r)) : ℕ) := h
  rw [cmIdx_val_eq, cmIdx_val_eq] at h0
  have hv1 := v.1.isLt
  have hw1 := w.1.isLt
  rcases lt_trichotomy v.2.val w.2.val with h1 | h1 | h1
  · exact Or.inl h1
  · refine Or.inr ⟨Fin.ext h1, ?_⟩
    rw [h1] at h0
    show v.1.val < w.1.val
    omega
  · exfalso
    have hm : r * (w.2.val + 1) ≤ r * v.2.val := by
      first
      | exact Nat.mul_le_mul_left r h1
      | exact Nat.mul_le_mul_left h1 r
      | exact Nat.mul_le_mul (le_refl r) h1
    rw [Nat.mul_add, Nat.mul_one] at hm
    first
    | omega
    | linarith

/- English proof (translation)
Use `first`. Consider the case `(simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)`. Consider the case `(rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply])`. Consider the case `(simp; done)`.
-/
private theorem domCongr_cmIdx_apply_cmIdx {r n : ℕ} (x : Fin r × Fin n →₀ ℕ) (v : Fin r × Fin n) :
    (Finsupp.domCongr (cmIdx r n) x) (cmIdx r n v) = x v := by
  first
  | (simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)
  | (rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply])
  | (simp; done)

/- English proof (translation)
Rewrite using `[Finsupp.finset_sum_apply]`. Distinguish the cases in `h : t.val < s`. Rewrite using `[dif_pos h, Finset.sum_eq_single ⟨t.val, h⟩]`. Rewrite using `[Finsupp.single_apply]`. Distinguish the cases in `hb : τ ⟨t.val, h⟩ = b`.

Establish `hp : (τ ⟨t.val, h⟩, Fin.castLE hs ⟨t.val, h⟩) = (b, t)` using `by first`. Consider the case `exact Prod.ext hb (Fin.ext rfl)`. Consider the case `exact Prod.ext_iff.2 ⟨hb, Fin.ext rfl⟩`. Consider the case `(subst hb; rfl)`. Rewrite using `[if_pos hp, if_pos hb]`.

Rewrite using `[if_neg, if_neg hb]`. Introduce `he`. Conclude with `hb (congrArg Prod.fst he)`. Introduce `q _ hq`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `he`. Apply `hq` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Establish `h2 : (Fin.castLE hs q).val = t.val` using `congrArg (fun x => (x.2 : ℕ)) he`. Conclude with `h2`.

Introduce `hq`. Conclude with `absurd (Finset.mem_univ _) hq`. Rewrite using `[dif_neg h]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q _`.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `he`. Apply `h` to reduce the goal to its premises. Establish `h2 : (Fin.castLE hs q).val = t.val` using `congrArg (fun x => (x.2 : ℕ)) he`. Establish `h3` using `q.isLt`.

Establish `h4 : (Fin.castLE hs q).val = q.val` using `rfl`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_single_castLE_apply' {r n s : ℕ} (τ : Fin s → Fin r) (hs : s ≤ n) (b : Fin r) (t : Fin n) :
    (∑ q : Fin s, Finsupp.single (τ q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
      if h : t.val < s then (if τ ⟨t.val, h⟩ = b then 1 else 0) else 0 := by
  rw [Finsupp.finset_sum_apply]
  by_cases h : t.val < s
  · rw [dif_pos h, Finset.sum_eq_single ⟨t.val, h⟩]
    · rw [Finsupp.single_apply]
      by_cases hb : τ ⟨t.val, h⟩ = b
      · have hp : (τ ⟨t.val, h⟩, Fin.castLE hs ⟨t.val, h⟩) = (b, t) := by
          first
          | exact Prod.ext hb (Fin.ext rfl)
          | exact Prod.ext_iff.2 ⟨hb, Fin.ext rfl⟩
          | (subst hb; rfl)
        rw [if_pos hp, if_pos hb]
      · rw [if_neg, if_neg hb]
        intro he
        exact hb (congrArg Prod.fst he)
    · intro q _ hq
      rw [Finsupp.single_apply, if_neg]
      intro he
      apply hq
      apply Fin.ext
      have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
      exact h2
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro q _
    rw [Finsupp.single_apply, if_neg]
    intro he
    apply h
    have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
    have h3 := q.isLt
    have h4 : (Fin.castLE hs q).val = q.val := rfl
    omega

/- English proof (translation)
Use `first`. Consider the case `exact ⟨i, h1, h2⟩`. Consider the case `exact Finsupp.Lex.lt_of_forall_lt_of_lt _ _ i h1 h2`. Consider the case `(show Finsupp.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)`. Consider the case `(show Pi.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)`.

Consider the case `(rw [Finsupp.lex_def]; exact ⟨i, h1, h2⟩)`.
-/
private theorem toLex_lt_of_eq_below_of_apply_lt {N : ℕ} (x y : Fin N →₀ ℕ) (i : Fin N)
    (h1 : ∀ j, j < i → x j = y j) (h2 : x i < y i) : toLex x < toLex y := by
  first
  | exact ⟨i, h1, h2⟩
  | exact Finsupp.Lex.lt_of_forall_lt_of_lt _ _ i h1 h2
  | (show Finsupp.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)
  | (show Pi.Lex (· < ·) (· < ·) x y; exact ⟨i, h1, h2⟩)
  | (rw [Finsupp.lex_def]; exact ⟨i, h1, h2⟩)

/- English proof (translation)
The claim follows from `h`.
-/
private theorem colLex_lt_of_toLex_domCongr_cmIdx_lt {r n : ℕ} {c d : Fin r × Fin n →₀ ℕ}
    (h : toLex (Finsupp.domCongr (cmIdx r n) c) <
      toLex (Finsupp.domCongr (cmIdx r n) d)) :
    c ≺[colLex r n] d := h

/- English proof (translation)
Introduce `r n s I hs hI σ hσ`. Establish `hex : ∃ q, σ q ≠ q`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hσ` to reduce the goal to its premises.

Use extensionality with `x`. Use `first`. Consider the case `(rw [h x]; rfl)`. Consider the case `simp [h x]`. Take `⟨q0, hq0, hmin⟩` from `(wellFounded_lt (α := Fin s)).has_min {q | σ q ≠ q} hex`.

Establish `hq0' : σ q0 ≠ q0` using `hq0`. Establish `hfix : ∀ q, q < q0 → σ q = q` using `fun q hq => by`. Assume the negation of the conclusion as `h`. Conclude with `hmin q h hq`. Establish `hgt : q0 < σ q0`.

Break down `lt_trichotomy (σ q0) q0 with h | h | h` into its components or cases. Conclude with `absurd (σ.injective (hfix _ h)) h.ne`. Conclude with `absurd h hq0'`. Conclude with `h`. Establish `hIlt : I q0 < I (σ q0)` using `hI hgt`.

Establish `hA : ∀ (b : Fin r) (t : Fin n), (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) = if h : t.val < s then (if I (σ ⟨t.val, h⟩) = b then 1 else 0) else 0` using `fun b t => sum_single_castLE_apply' (fun q => I (σ q)) hs b t`. Establish `hB : ∀ (b : Fin r) (t : Fin n), (∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) = if h : t.val < s then (if I ⟨t.val, h⟩ = b then 1 else 0) else 0` using `fun b t => sum_single_castLE_apply' I hs b t`. Establish `hcq : (Fin.castLE hs q0).val = q0.val` using `rfl`. Establish `ht0 : (Fin.castLE hs q0).val < s` using `q0.isLt`. Establish `e1 : (⟨(Fin.castLE hs q0).val, ht0⟩ : Fin s) = q0` using `Fin.ext rfl`.

Apply `colLex_lt_of_toLex_domCongr_cmIdx_lt` to reduce the goal to its premises. Apply `toLex_lt_of_eq_below_of_apply_lt _ _ (cmIdx r n (I q0, Fin.castLE hs q0))` to reduce the goal to its premises. Introduce `j hj`. Take `⟨v, rfl⟩` from `(cmIdx r n).surjective j`. Rewrite using `[domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx]`.

Take `⟨b, t⟩` from `v`. Rewrite using `[hA, hB]`. Establish `hlt` using `col_lt_or_col_eq_row_lt_of_cmIdx_lt hj`. Apply the tactic sequence `try dsimp only at hlt`. Break down `hlt with hlt | ⟨rfl, hb⟩` into its components or cases.

Establish `ht : t.val < s`. Use `q0.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hlt' : (⟨t.val, ht⟩ : Fin s) < q0` using `by show t.val < q0.val`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[dif_pos ht, dif_pos ht, hfix _ hlt']`. Rewrite using `[dif_pos ht0, dif_pos ht0, e1, if_neg (lt_trans hb hIlt).ne', if_neg hb.ne']`. Rewrite using `[domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx, hA, hB]`. Rewrite using `[dif_pos ht0, dif_pos ht0, e1, if_neg hIlt.ne', if_pos (rfl : I q0 = I q0)]`. Conclude with `Nat.zero_lt_one`.
-/
theorem minorExponentLt : MinorExpLt := by
  intro r n s I hs hI σ hσ
  have hex : ∃ q, σ q ≠ q := by
    by_contra h
    push_neg at h
    apply hσ
    ext x
    first
    | (rw [h x]; rfl)
    | simp [h x]
  obtain ⟨q0, hq0, hmin⟩ := (wellFounded_lt (α := Fin s)).has_min {q | σ q ≠ q} hex
  have hq0' : σ q0 ≠ q0 := hq0
  have hfix : ∀ q, q < q0 → σ q = q := fun q hq => by
    by_contra h
    exact hmin q h hq
  have hgt : q0 < σ q0 := by
    rcases lt_trichotomy (σ q0) q0 with h | h | h
    · exact absurd (σ.injective (hfix _ h)) h.ne
    · exact absurd h hq0'
    · exact h
  have hIlt : I q0 < I (σ q0) := hI hgt
  have hA : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I (σ ⟨t.val, h⟩) = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' (fun q => I (σ q)) hs b t
  have hB : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I ⟨t.val, h⟩ = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' I hs b t
  have hcq : (Fin.castLE hs q0).val = q0.val := rfl
  have ht0 : (Fin.castLE hs q0).val < s := q0.isLt
  have e1 : (⟨(Fin.castLE hs q0).val, ht0⟩ : Fin s) = q0 := Fin.ext rfl
  apply colLex_lt_of_toLex_domCongr_cmIdx_lt
  apply toLex_lt_of_eq_below_of_apply_lt _ _ (cmIdx r n (I q0, Fin.castLE hs q0))
  · intro j hj
    obtain ⟨v, rfl⟩ := (cmIdx r n).surjective j
    rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx]
    obtain ⟨b, t⟩ := v
    rw [hA, hB]
    have hlt := col_lt_or_col_eq_row_lt_of_cmIdx_lt hj
    try dsimp only at hlt
    rcases hlt with hlt | ⟨rfl, hb⟩
    · have ht : t.val < s := by
        have := q0.isLt
        omega
      have hlt' : (⟨t.val, ht⟩ : Fin s) < q0 := by
        show t.val < q0.val
        omega
      rw [dif_pos ht, dif_pos ht, hfix _ hlt']
    · rw [dif_pos ht0, dif_pos ht0, e1, if_neg (lt_trans hb hIlt).ne', if_neg hb.ne']
  · rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx, hA, hB]
    rw [dif_pos ht0, dif_pos ht0, e1, if_neg hIlt.ne', if_pos (rfl : I q0 = I q0)]
    exact Nat.zero_lt_one

end Formalism.GradedWeylDivisibility
