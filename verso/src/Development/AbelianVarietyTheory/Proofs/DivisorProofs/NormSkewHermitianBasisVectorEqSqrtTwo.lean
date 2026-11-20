import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

/- English proof (translation)
Establish `hdd : ‖((d a * d b : ℝ) : ℂ)‖ = 1`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_mul]`. Apply the tactic sequence `rcases hd a with h | h <;> rcases hd b with h' | h' <;> simp [h, h']`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Use `⟨(a, b), (b, a), ?_, ?_⟩` and prove the remaining obligations.

Introduce `e`. Simplify using `only [Prod.mk.injEq] at e`. Conclude with `h.ne e.1`. Introduce and unpack `⟨a', b'⟩`. Simplify using `only [boxEnt, if_pos h, Prod.mk.injEq]`.

Apply the tactic sequence `split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)`. Substitute `h` using the available equality. Establish `haz : a ≠ z` using `fun e => hab (by rw [e])`. Use `⟨(a, a), (z, z), ?_, ?_⟩` and prove the remaining obligations. Introduce `e`.

Simplify using `only [Prod.mk.injEq] at e`. Conclude with `haz e.1`. Introduce and unpack `⟨a', b'⟩`. Simplify using `only [boxEnt, lt_irrefl, if_false, Prod.mk.injEq]`. Apply the tactic sequence `split_ifs <;> simp_all`.

Use `⟨(b, a), (a, b), ?_, ?_⟩` and prove the remaining obligations. Introduce `e`. Simplify using `only [Prod.mk.injEq] at e`. Conclude with `h.ne e.1`. Introduce and unpack `⟨a', b'⟩`.

Simplify using `only [boxEnt, if_neg (not_lt.2 h.le), if_pos h, Prod.mk.injEq]`. Apply the tactic sequence `split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)`.
-/
theorem boxEnt_norm_sq_eq {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b : Fin r)
    (hab : (a, b) ≠ (z, z)) :
    ∃ P Q : Fin r × Fin r, P ≠ Q ∧ ∀ p : Fin r × Fin r,
      ‖boxEnt d z a b p.1 p.2‖ ^ 2 = (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
  have hdd : ‖((d a * d b : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rcases hd a with h | h <;> rcases hd b with h' | h' <;> simp [h, h']
  rcases lt_trichotomy a b with h | h | h
  · refine ⟨(a, b), (b, a), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)
  · subst h
    have haz : a ≠ z := fun e => hab (by rw [e])
    refine ⟨(a, a), (z, z), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact haz e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, lt_irrefl, if_false, Prod.mk.injEq]
      split_ifs <;> simp_all
  · refine ⟨(b, a), (a, b), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_neg (not_lt.2 h.le), if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)

/- English proof (translation)
Introduce `E _ _ _ r Ψ d z hd k`. Take `⟨τ, ⟨⟨a, b⟩, hab⟩⟩` from `k`. Take `⟨P, Q, hPQ, hPn⟩` from `boxEnt_norm_sq_eq (d τ) (hd τ) z a b hab`. Rewrite using `[EuclideanSpace.norm_eq]`. Use `congr 1`.

Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single τ]`. Establish `: ∀ p : Fin r × Fin r, ‖(boxVec d z ⟨τ, ⟨(a, b), hab⟩⟩) (τ, p)‖ ^ 2 = (if p = P then 1 else 0) + (if p = Q then 1 else 0)`. Introduce `p`. Rewrite using `[← hPn p]`. Simplify using `[boxVec]`.

Simplify using `only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Evaluate the numerical expressions. Introduce `τ' _ hτ'`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p _`.

Simplify using `[boxVec, hτ']`. Simplify using the standard rewrite rules.
-/
theorem norm_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, ‖boxVec d z k‖ = √2 := by
  intro E _ _ _ r Ψ d z hd k
  obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
  obtain ⟨P, Q, hPQ, hPn⟩ := boxEnt_norm_sq_eq (d τ) (hd τ) z a b hab
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · have : ∀ p : Fin r × Fin r, ‖(boxVec d z ⟨τ, ⟨(a, b), hab⟩⟩) (τ, p)‖ ^ 2 =
        (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
      intro p
      rw [← hPn p]
      simp [boxVec]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    norm_num
  · intro τ' _ hτ'
    apply Finset.sum_eq_zero
    intro p _
    simp [boxVec, hτ']
  · simp

end GlobalTheory.CovTop.VolUp.FrameBox
