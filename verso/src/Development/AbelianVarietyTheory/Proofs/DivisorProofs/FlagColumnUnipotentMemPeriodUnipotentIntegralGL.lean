import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

namespace GlobalTheory.DiagVol

/- English proof (translation)
Use `set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if s = t then y r else 0) with hE`. Establish `hyt : y t = 0` using `hz t (lt_irrefl _)`. Establish `hEE : E * E = 0`. Use extensionality with `r s`. Simplify using `only [hE, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]`.

Rewrite using `[Finset.sum_eq_single t]`. Simplify using `[hyt]`. Introduce `u _ hu`. Simplify using `[hu]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ t) h`. Establish `h1 : (1 + E) * (1 - E) = 1`. Establish `: (1 + E) * (1 - E) = 1 - E * E` using `by noncomm_ring`. Rewrite using `[this, hEE, sub_zero]`. Establish `h2 : (1 - E) * (1 + E) = 1`.

Establish `: (1 - E) * (1 + E) = 1 - E * E` using `by noncomm_ring`. Rewrite using `[this, hEE, sub_zero]`. Set `x : GL (n ⊕ Fin c) k` to `⟨1 + E, 1 - E, h1, h2⟩`. Establish `hone : ∀ i j : n ⊕ Fin c, (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) i j ∈ 𝒪[k]`. Introduce `i j`.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `hEi : ∀ i j, E i j ∈ 𝒪[k]`.

Introduce `i j`. Simplify using `only [hE, Matrix.of_apply]`. Use `split_ifs`. Conclude with `hy i`. Conclude with `zero_mem _`.

Establish `hInN : ∀ p : ℕ, (∀ r, y r ≠ 0 → lev p r < lev (n` using `n) (c := c) p t) → InN p x := by`. Introduce `p hp r s hrs`. Use `show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s`. Rewrite using `[Matrix.add_apply, add_eq_left]`. Simplify using `only [hE, Matrix.of_apply]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Assume the negation of the conclusion as `hne`. Conclude with `absurd hrs (not_le.2 (hp r hne))`. Both sides reduce to the same expression.

Use `⟨x, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show x ∈ N k n c ((c + 1) / 2) ⊔ N k n c (c / 2 + 1)`. Consider the cases of `t with`. Consider the case `inr j`. Use `Subgroup.mem_sup_left (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))` and prove the remaining obligations.

Establish `hlt : ordL c r < ordL c (Sum.inr j : n ⊕ Fin c)`. Assume the negation of the conclusion as `h`. Conclude with `hr (hz r h)`. Consider the cases of `r with`. Consider the case `inl a => simp [ordL, lev] at hlt ⊢`.

Use linear arithmetic over natural numbers and integers. Consider the case `inr i => simp [ordL, lev] at hlt ⊢`. Use linear arithmetic over natural numbers and integers. Consider the case `inl a0`. Use `Subgroup.mem_sup_right (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))` and prove the remaining obligations.

Establish `hlt : ordL c r < ordL c (Sum.inl a0 : n ⊕ Fin c)`. Assume the negation of the conclusion as `h`. Conclude with `hr (hz r h)`. Consider the cases of `r with`. Consider the case `inl a => simp [ordL, lev] at hlt ⊢`.

Consider the case `inr i => simp [ordL, lev] at hlt ⊢`. Use linear arithmetic over natural numbers and integers. Use `(mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Use `show (1 + E) i j ∈ 𝒪[k]`. Rewrite using `[Matrix.add_apply]`.

Conclude with `add_mem (hone i j) (hEi i j)`. Use `show (1 - E) i j ∈ 𝒪[k]`. Rewrite using `[Matrix.sub_apply]`. Conclude with `sub_mem (hone i j) (hEi i j)`.
-/
theorem colE_mem_symN_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (t : n ⊕ Fin c) (y : n ⊕ Fin c → k) (hy : ∀ r, y r ∈ 𝒪[k])
    (hz : ∀ r, ¬ ordL c r < ordL c t → y r = 0) :
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c),
      x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if s = t then y r else 0) with hE
  have hyt : y t = 0 := hz t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp only [hE, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Finset.sum_eq_single t]
    · simp [hyt]
    · intro u _ hu; simp [hu]
    · intro h; exact absurd (Finset.mem_univ t) h
  have h1 : (1 + E) * (1 - E) = 1 := by
    have : (1 + E) * (1 - E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  have h2 : (1 - E) * (1 + E) = 1 := by
    have : (1 - E) * (1 + E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  let x : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  have hone : ∀ i j : n ⊕ Fin c, (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hEi : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [hE, Matrix.of_apply]
    split_ifs
    · exact hy i
    · exact zero_mem _
  have hInN : ∀ p : ℕ, (∀ r, y r ≠ 0 → lev p r < lev (n := n) (c := c) p t) → InN p x := by
    intro p hp r s hrs
    show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
    rw [Matrix.add_apply, add_eq_left]
    simp only [hE, Matrix.of_apply]
    split_ifs with h
    · subst h
      by_contra hne
      exact absurd hrs (not_le.2 (hp r hne))
    · rfl
  refine ⟨x, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · show x ∈ N k n c ((c + 1) / 2) ⊔ N k n c (c / 2 + 1)
    cases t with
    | inr j =>
      refine Subgroup.mem_sup_left (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inr j : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢; omega
      | inr i => simp [ordL, lev] at hlt ⊢; omega
    | inl a0 =>
      refine Subgroup.mem_sup_right (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inl a0 : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢
      | inr i => simp [ordL, lev] at hlt ⊢; omega
  · refine (mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      rw [Matrix.add_apply]; exact add_mem (hone i j) (hEi i j)
    · show (1 - E) i j ∈ 𝒪[k]
      rw [Matrix.sub_apply]; exact sub_mem (hone i j) (hEi i j)

end GlobalTheory.DiagVol
