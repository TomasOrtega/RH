import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]`. Use `congr 1`. Distinguish the cases in `hy : y = b`. Substitute `hy` using the available equality. Simplify using `[Matrix.mul_apply, single_apply]`.

Simplify using `[Matrix.mul_apply, single_apply, hy, Ne.symm hy]`.
-/
theorem mul_transvection_apply' {n : ℕ} (a b : Fin n) (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    (M * transvection a b c) x y = M x y + if y = b then M x a * c else 0 := by
  rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = b
  · subst hy; simp [Matrix.mul_apply, single_apply]
  · simp [Matrix.mul_apply, single_apply, hy, Ne.symm hy]

/- English proof (translation)
Introduce `n P h1 hmul htr`. Set `S : GL (Fin n) ℂ → Finset (Fin n × Fin n)` to `fun U => Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ U.val p.1 p.2 ≠ 0)`. It suffices to establish `H : ∀ k, ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → (S U).card = k → P U from fun U hU hd => H _ U hU hd rfl`. Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`.

Consider the case `_ k ih`. Introduce `U hU hd hk`. Break down `(S U).eq_empty_or_nonempty with hS | hne` into its components or cases. Establish `: U = 1`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Simplify using `only [Units.val_one, Matrix.one_apply]`. Break down `lt_trichotomy i j with hij | hij | hij` into its components or cases. Rewrite using `[if_neg hij.ne]`. Assume the negation of the conclusion as `h`.

Establish `: (i, j) ∈ S U` using `by simp [S, hij, h]`. Rewrite `this` using `[hS]`. Simplify using `at this`. Substitute `hij` using the available equality. Simplify using `[hd]`.

Rewrite using `[if_neg hij.ne']`. Conclude with `hU hij`. Rewrite using `[this]`. Conclude with `h1`. Take `⟨p, hp, hmin⟩` from `Finset.exists_min_image (S U) (fun p => p.2) hne`.

Take `⟨a, b⟩` from `p`. Simplify using `only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Take `⟨hab, hs⟩` from `hp`. Use `set s := U.val a b with hsdef`. Establish `col : ∀ x, U.val x a = if x = a then 1 else 0`.

Introduce `x`. Use `split_ifs with hx`. Substitute `hx` using the available equality. Conclude with `hd x`. Break down `lt_trichotomy x a with hxa | hxa | hxa` into its components or cases.

Assume the negation of the conclusion as `h`. Establish `hm` using `hmin (x, a) (by simp [S, hxa, h])`. Simplify using `at hm`. Conclude with `absurd (lt_of_le_of_lt hm hab) (lt_irrefl _)`. Conclude with `absurd hxa hx`.

Conclude with `hU hxa`. Set `T : ℂ → GL (Fin n) ℂ` to `fun c => ⟨transvection a b c, transvection a b (-c), by rw [transvection_mul_transvection_same _ _ hab.ne]; simp, by rw [transvection_mul_transvection_same _ _ hab.ne]; simp⟩`. Set `U'` to `U * T (-s)`. Establish `ent : ∀ x y, U'.val x y = U.val x y + if y = b ∧ x = a then -s else 0`. Introduce `x y`.

Use `show (U.val * transvection a b (-s)) x y = _`. Rewrite using `[mul_transvection_apply', col]`. Apply the tactic sequence `by_cases hy : y = b <;> by_cases hx : x = a <;> simp [hy, hx]`. Establish `hU' : U'.val.BlockTriangular id`. Introduce `x y hxy`.

Rewrite using `[ent, hU hxy]`. Simplify using `only [id] at hxy`. Rewrite using `[if_neg]`. Use the proof step `· simp`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `absurd (hab.trans hxy) (lt_irrefl _)`. Establish `hd' : ∀ i, U'.val i i = 1`. Introduce `i`. Rewrite using `[ent, hd]`. Rewrite using `[if_neg]`.

Use the proof step `· simp`. Introduce and unpack `⟨rfl, h⟩`. Conclude with `hab.ne h.symm`. Establish `hlt : (S U').card < k`. Rewrite using `[← hk]`.

Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`. Use `⟨(a, b), ?_, ?_⟩` and prove the remaining obligations. Simplify `hs` using `[S, hab]`. Simplify using `[S, ent, hsdef]`.

Introduce `q hq`. Simplify using `only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢`. Use `⟨hq.1, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hqe : q.2 = b ∧ q.1 = a`. Take `⟨q1, q2⟩` from `q`.

Simplify using `only at hqe`. Take `⟨rfl, rfl⟩` from `hqe`. Conclude with `hs`. Use `hq.2` as an intermediate fact. Rewrite `this` using `[ent, if_neg hqe, add_zero]`.

Conclude with `this`. Establish `PU' : P U'` using `ih _ hlt U' hU' hd' rfl`. Establish `PT : P (T s)` using `htr a b hab s (T s) rfl`. Establish `hUeq : U = U' * T s`. Apply `Units.ext` to reduce the goal to its premises.

Use `show U.val = U.val * transvection a b (-s) * transvection a b s`. Rewrite using `[mul_assoc, transvection_mul_transvection_same _ _ hab.ne]`. Simplify using the standard rewrite rules. Rewrite using `[hUeq]`. Conclude with `hmul _ _ PU' PT`.
-/
theorem unitriangular_induction_transvection :
    ∀ (n : ℕ) (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) →
      (∀ (i j : Fin n), i < j → ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s → P B) →
      ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → P U := by
  intro n P h1 hmul htr
  let S : GL (Fin n) ℂ → Finset (Fin n × Fin n) := fun U =>
    Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ U.val p.1 p.2 ≠ 0)
  suffices H : ∀ k, ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) →
      (S U).card = k → P U from fun U hU hd => H _ U hU hd rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U hU hd hk
  rcases (S U).eq_empty_or_nonempty with hS | hne
  · have : U = 1 := by
      apply Units.ext
      ext i j
      simp only [Units.val_one, Matrix.one_apply]
      rcases lt_trichotomy i j with hij | hij | hij
      · rw [if_neg hij.ne]
        by_contra h
        have : (i, j) ∈ S U := by simp [S, hij, h]
        rw [hS] at this; simp at this
      · subst hij; simp [hd]
      · rw [if_neg hij.ne']
        exact hU hij
    rw [this]; exact h1
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (S U) (fun p => p.2) hne
    obtain ⟨a, b⟩ := p
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hab, hs⟩ := hp
    set s := U.val a b with hsdef
    have col : ∀ x, U.val x a = if x = a then 1 else 0 := by
      intro x
      split_ifs with hx
      · subst hx; exact hd x
      · rcases lt_trichotomy x a with hxa | hxa | hxa
        · by_contra h
          have hm := hmin (x, a) (by simp [S, hxa, h])
          simp at hm
          exact absurd (lt_of_le_of_lt hm hab) (lt_irrefl _)
        · exact absurd hxa hx
        · exact hU hxa
    let T : ℂ → GL (Fin n) ℂ := fun c =>
      ⟨transvection a b c, transvection a b (-c),
        by rw [transvection_mul_transvection_same _ _ hab.ne]; simp,
        by rw [transvection_mul_transvection_same _ _ hab.ne]; simp⟩
    let U' := U * T (-s)
    have ent : ∀ x y, U'.val x y = U.val x y + if y = b ∧ x = a then -s else 0 := by
      intro x y
      show (U.val * transvection a b (-s)) x y = _
      rw [mul_transvection_apply', col]
      by_cases hy : y = b <;> by_cases hx : x = a <;> simp [hy, hx]
    have hU' : U'.val.BlockTriangular id := by
      intro x y hxy
      rw [ent, hU hxy]
      simp only [id] at hxy
      rw [if_neg]; · simp
      rintro ⟨rfl, rfl⟩
      exact absurd (hab.trans hxy) (lt_irrefl _)
    have hd' : ∀ i, U'.val i i = 1 := by
      intro i
      rw [ent, hd]
      rw [if_neg]; · simp
      rintro ⟨rfl, h⟩
      exact hab.ne h.symm
    have hlt : (S U').card < k := by
      rw [← hk]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨(a, b), ?_, ?_⟩
        · simpa [S, hab] using hs
        · simp [S, ent, hsdef]
      · intro q hq
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        refine ⟨hq.1, ?_⟩
        by_cases hqe : q.2 = b ∧ q.1 = a
        · obtain ⟨q1, q2⟩ := q
          simp only at hqe
          obtain ⟨rfl, rfl⟩ := hqe
          exact hs
        · have := hq.2
          rw [ent, if_neg hqe, add_zero] at this
          exact this
    have PU' : P U' := ih _ hlt U' hU' hd' rfl
    have PT : P (T s) := htr a b hab s (T s) rfl
    have hUeq : U = U' * T s := by
      apply Units.ext
      show U.val = U.val * transvection a b (-s) * transvection a b s
      rw [mul_assoc, transvection_mul_transvection_same _ _ hab.ne]
      simp
    rw [hUeq]
    exact hmul _ _ PU' PT

end GlobalTheory
