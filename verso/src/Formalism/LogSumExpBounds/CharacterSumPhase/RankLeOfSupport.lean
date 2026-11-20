import Formalism.LogSumExpBounds.NuclearBound

namespace Formalism.NuclearRankWeightBounds.P

open Matrix Finset

/- English proof (translation)
Unfold `Matrix.rank`. Establish `h : LinearMap.range (A + B).mulVecLin ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin`. Introduce `x hx`. Take `⟨v, rfl⟩` from `LinearMap.mem_range.1 hx`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.add_mulVec]`.

Conclude with `Submodule.add_mem_sup (LinearMap.mem_range.2 ⟨v, rfl⟩) (LinearMap.mem_range.2 ⟨v, rfl⟩)`. Conclude with `(Submodule.finrank_mono h).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)`.
-/
lemma rank_add_le' {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have h : LinearMap.range (A + B).mulVecLin
      ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    intro x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hx
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup (LinearMap.mem_range.2 ⟨v, rfl⟩) (LinearMap.mem_range.2 ⟨v, rfl⟩)
  exact (Submodule.finrank_mono h).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

/- English proof (translation)
Use `le_min ?_ ?_` and prove the remaining obligations. Apply `Matrix.rank_le_card_of_support_subset A S` to reduce the goal to its premises. Introduce `a ha`. Assume the negation of the conclusion as `hn`. Apply `ha` to reduce the goal to its premises.

Use function extensionality and compare the values at `b`. Assume the negation of the conclusion as `hb`. Conclude with `hn (h a b hb).1`. Rewrite using `[← Matrix.rank_transpose]`. Apply `Matrix.rank_le_card_of_support_subset Aᵀ S'` to reduce the goal to its premises.

Introduce `b hb'`. Assume the negation of the conclusion as `hn`. Apply `hb'` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Assume the negation of the conclusion as `ha`.

Conclude with `hn (h a b ha).2`.
-/
lemma rank_le_of_support {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (S S' : Finset (Fin N))
    (h : ∀ a b, A a b ≠ 0 → a ∈ S ∧ b ∈ S') : A.rank ≤ min S.card S'.card := by
  refine le_min ?_ ?_
  · apply Matrix.rank_le_card_of_support_subset A S
    intro a ha
    by_contra hn
    apply ha
    funext b
    by_contra hb
    exact hn (h a b hb).1
  · rw [← Matrix.rank_transpose]
    apply Matrix.rank_le_card_of_support_subset Aᵀ S'
    intro b hb'
    by_contra hn
    apply hb'
    funext a
    by_contra ha
    exact hn (h a b ha).2

/- English proof (translation)
Introduce `N ep Y hY`. Use `set T := (univ : Finset (Fin N)).filter (fun a => ep a = true) with hT`. Use `set F := (univ : Finset (Fin N)).filter (fun a => ep a = false) with hF`. Use `set P : Matrix (Fin N) (Fin N) ℂ := diagonal (fun a => if ep a = true then 1 else 0) with hP`. Use `set Q : Matrix (Fin N) (Fin N) ℂ := diagonal (fun a => if ep a = true then 0 else 1) with hQ`.

Establish `hsplit : Y = Y * P + Y * Q`. Use extensionality with `a b`. Simplify using `only [hP, hQ, Matrix.add_apply, Matrix.mul_diagonal]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h1 : (Y * P).rank ≤ min F.card T.card`.

Apply `rank_le_of_support _ F T` to reduce the goal to its premises. Introduce `a b hab`. Simplify using `only [hP, Matrix.mul_diagonal] at hab`. Consider the cases of `hb : ep b`. Simplify using `[hb] at hab`.

Establish `hY' : Y a b ≠ 0` using `by simpa [hb] using hab`. Consider the cases of `ha : ep a`. Simplify using `[hT, hF, ha, hb]`. Conclude with `absurd (hY a b (by rw [ha, hb])) hY'`. Establish `h2 : (Y * Q).rank ≤ min T.card F.card`.

Apply `rank_le_of_support _ T F` to reduce the goal to its premises. Introduce `a b hab`. Simplify using `only [hQ, Matrix.mul_diagonal] at hab`. Consider the cases of `hb : ep b`. Establish `hY' : Y a b ≠ 0` using `by simpa [hb] using hab`.

Consider the cases of `ha : ep a`. Conclude with `absurd (hY a b (by rw [ha, hb])) hY'`. Simplify using `[hT, hF, ha, hb]`. Simplify using `[hb] at hab`. Establish `h3 : Y.rank ≤ (Y * P).rank + (Y * Q).rank`.

Combine the equalities or inequalities in the displayed calculation. Establish `hq : Formalism.NuclearRankWeightBounds.D.q0 ep = min T.card F.card` using `rfl`. Rewrite using `[hq]`. Use `min_comm F.card T.card` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem rank_block_holds : Formalism.NuclearRankWeightBounds.D.RankBlock := by
  intro N ep Y hY
  classical
  set T := (univ : Finset (Fin N)).filter (fun a => ep a = true) with hT
  set F := (univ : Finset (Fin N)).filter (fun a => ep a = false) with hF
  set P : Matrix (Fin N) (Fin N) ℂ := diagonal (fun a => if ep a = true then 1 else 0) with hP
  set Q : Matrix (Fin N) (Fin N) ℂ := diagonal (fun a => if ep a = true then 0 else 1) with hQ
  have hsplit : Y = Y * P + Y * Q := by
    ext a b
    simp only [hP, hQ, Matrix.add_apply, Matrix.mul_diagonal]
    split_ifs <;> simp
  have h1 : (Y * P).rank ≤ min F.card T.card := by
    apply rank_le_of_support _ F T
    intro a b hab
    simp only [hP, Matrix.mul_diagonal] at hab
    cases hb : ep b
    · simp [hb] at hab
    · have hY' : Y a b ≠ 0 := by simpa [hb] using hab
      cases ha : ep a
      · simp [hT, hF, ha, hb]
      · exact absurd (hY a b (by rw [ha, hb])) hY'
  have h2 : (Y * Q).rank ≤ min T.card F.card := by
    apply rank_le_of_support _ T F
    intro a b hab
    simp only [hQ, Matrix.mul_diagonal] at hab
    cases hb : ep b
    · have hY' : Y a b ≠ 0 := by simpa [hb] using hab
      cases ha : ep a
      · exact absurd (hY a b (by rw [ha, hb])) hY'
      · simp [hT, hF, ha, hb]
    · simp [hb] at hab
  have h3 : Y.rank ≤ (Y * P).rank + (Y * Q).rank := by
    calc Y.rank = (Y * P + Y * Q).rank := congrArg Matrix.rank hsplit
      _ ≤ _ := rank_add_le' _ _
  have hq : Formalism.NuclearRankWeightBounds.D.q0 ep = min T.card F.card := rfl
  rw [hq]
  have := min_comm F.card T.card
  omega

end Formalism.NuclearRankWeightBounds.P
