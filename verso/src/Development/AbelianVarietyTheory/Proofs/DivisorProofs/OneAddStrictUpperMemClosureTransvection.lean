import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.UpperTransvection

/- English proof (translation)
Use `set S := Submonoid.closure {M : Matrix (Fin N) (Fin N) R | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r}`. It suffices to establish `key : ∀ n : ℕ, ∀ c : Matrix (Fin N) (Fin N) R, (∀ a b, b ≤ a → c a b = 0) → (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0).card ≤ n → 1 + c ∈ S from key _ c hc le_rfl`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `c _ hcard`. Establish `hc0 : c = 0`. Use extensionality with `i j`. Assume the negation of the conclusion as `h`. Establish `: (i, j) ∈ (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0)`.

Simplify using `using h`. Rewrite `hcard` using `[Nat.le_zero, Finset.card_eq_zero]`. Simplify using `[hcard] at this`. Substitute `hc0` using the available equality. Simplify using `using S.one_mem`.

Consider the case `succ n ih`. Introduce `c hc hcard`. Use `set T := (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) with hT`. Break down `T.eq_empty_or_nonempty with hE | hne` into its components or cases. Conclude with `ih c hc (by rw [← hT, hE]; simp)`.

Take `⟨p, hpT, hpmin⟩` from `Finset.exists_min_image T (fun p => p.1) hne`. Take `⟨a, b⟩` from `p`. Establish `hab : c a b ≠ 0` using `by simpa [hT] using hpT`. Establish `hlt : a < b`. Assume the negation of the conclusion as `h`.

Conclude with `hab (hc a b (not_lt.mp h))`. Establish `hcol : ∀ i, c i a = 0`. Introduce `i`. Assume the negation of the conclusion as `h`. Establish `hi : (i, a) ∈ T` using `by simpa [hT] using h`.

Establish `h1` using `hpmin _ hi`. Establish `h2 : a ≤ i` using `h1`. Conclude with `h (hc i a h2)`. Use `set r := c a b`. Use `set c' := c - Matrix.single a b r with hc'`.

Establish `hc'_apply : ∀ i j, c' i j = if i = a ∧ j = b then 0 else c i j`. Introduce `i j`. Simplify using `only [hc', Matrix.sub_apply, Matrix.single_apply]`. Distinguish the cases in `h : i = a ∧ j = b`. Take `⟨rfl, rfl⟩` from `h`.

Simplify using `[r]`. Establish `h' : ¬ (a = i ∧ b = j)` using `fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩`. Simplify using `[h, h']`. Establish `hc'up : ∀ i j, j ≤ i → c' i j = 0`. Introduce `i j hji`.

Rewrite using `[hc'_apply]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `hc i j hji`. Establish `hT' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0) ⊆ T.erase (a, b)`.

Introduce `q hq`. Take `⟨i, j⟩` from `q`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hq`. Rewrite `hq` using `[hc'_apply]`. Use `split_ifs at hq with h`.

Conclude with `absurd rfl hq`. Rewrite using `[Finset.mem_erase]`. Use `⟨?_, by simpa [hT] using hq⟩` and prove the remaining obligations. Introduce `heq`. Simplify using `only [Prod.mk.injEq] at heq`.

Conclude with `h heq`. Establish `hcard' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0).card ≤ n`. Use `Finset.card_le_card hT'` as an intermediate fact. Rewrite `this` using `[Finset.card_erase_of_mem hpT]`. Use linear arithmetic over natural numbers and integers.

Establish `hmem' : 1 + c' ∈ S` using `ih c' hc'up hcard'`. Establish `hcolz : c' * Matrix.single a b r = 0`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `k _`. Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[hc'_apply]`. Use `split_ifs`.

Simplify using the standard rewrite rules. Rewrite using `[hcol]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `heq : 1 + c = (1 + c') * Matrix.transvection a b r`.

Rewrite using `[Matrix.transvection, add_mul, one_mul, mul_add, mul_one, hcolz, add_zero, hc']`. Normalize the expressions using the abelian group laws. Rewrite using `[heq]`. Use `S.mul_mem hmem' (Submonoid.subset_closure ⟨a, b, r, hlt.ne, rfl⟩)` and prove the remaining obligations.
-/
theorem upper_mem_closure (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R)
    (hc : ∀ a b, b ≤ a → c a b = 0) :
    1 + c ∈ Submonoid.closure
      {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  classical
  set S := Submonoid.closure
      {M : Matrix (Fin N) (Fin N) R | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r}
  suffices key : ∀ n : ℕ, ∀ c : Matrix (Fin N) (Fin N) R, (∀ a b, b ≤ a → c a b = 0) →
      (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0).card ≤ n → 1 + c ∈ S from
    key _ c hc le_rfl
  intro n
  induction n with
  | zero =>
    intro c _ hcard
    have hc0 : c = 0 := by
      ext i j
      by_contra h
      have : (i, j) ∈ (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) := by
        simpa using h
      rw [Nat.le_zero, Finset.card_eq_zero] at hcard
      simp [hcard] at this
    subst hc0
    simpa using S.one_mem
  | succ n ih =>
    intro c hc hcard
    set T := (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) with hT
    rcases T.eq_empty_or_nonempty with hE | hne
    · exact ih c hc (by rw [← hT, hE]; simp)
    obtain ⟨p, hpT, hpmin⟩ := Finset.exists_min_image T (fun p => p.1) hne
    obtain ⟨a, b⟩ := p
    have hab : c a b ≠ 0 := by simpa [hT] using hpT
    have hlt : a < b := by
      by_contra h
      exact hab (hc a b (not_lt.mp h))

    have hcol : ∀ i, c i a = 0 := by
      intro i
      by_contra h
      have hi : (i, a) ∈ T := by simpa [hT] using h
      have h1 := hpmin _ hi
      have h2 : a ≤ i := h1
      exact h (hc i a h2)
    set r := c a b
    set c' := c - Matrix.single a b r with hc'
    have hc'_apply : ∀ i j, c' i j = if i = a ∧ j = b then 0 else c i j := by
      intro i j
      simp only [hc', Matrix.sub_apply, Matrix.single_apply]
      by_cases h : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h; simp [r]
      · have h' : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
        simp [h, h']
    have hc'up : ∀ i j, j ≤ i → c' i j = 0 := by
      intro i j hji
      rw [hc'_apply]; split_ifs
      · rfl
      · exact hc i j hji
    have hT' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0) ⊆ T.erase (a, b) := by
      intro q hq
      obtain ⟨i, j⟩ := q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [hc'_apply] at hq
      split_ifs at hq with h
      · exact absurd rfl hq
      · rw [Finset.mem_erase]
        refine ⟨?_, by simpa [hT] using hq⟩
        intro heq
        simp only [Prod.mk.injEq] at heq
        exact h heq
    have hcard' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0).card ≤ n := by
      have := Finset.card_le_card hT'
      rw [Finset.card_erase_of_mem hpT] at this
      omega
    have hmem' : 1 + c' ∈ S := ih c' hc'up hcard'
    have hcolz : c' * Matrix.single a b r = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [hc'_apply]; split_ifs
        · simp
        · rw [hcol]; simp
      · simp
    have heq : 1 + c = (1 + c') * Matrix.transvection a b r := by
      rw [Matrix.transvection, add_mul, one_mul, mul_add, mul_one, hcolz, add_zero, hc']
      abel
    rw [heq]
    refine S.mul_mem hmem' (Submonoid.subset_closure ⟨a, b, r, hlt.ne, rfl⟩)

end GlobalTheory.UpperTransvection
