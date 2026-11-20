import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem mul_transvection_apply' {n : ℕ} (a b : Fin n) (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    (M * transvection a b c) x y = M x y + if y = b then M x a * c else 0 := by
  rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = b
  · subst hy; simp [Matrix.mul_apply, single_apply]
  · simp [Matrix.mul_apply, single_apply, hy, Ne.symm hy]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Separate the alternatives or extract the components of the hypothesis.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
