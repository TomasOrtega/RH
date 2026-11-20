import Mathlib

/- English proof (translation)
Introduce `R ι _ _ A Y B a b h`. Rewrite `h` using `[Matrix.mul_apply]`. Take `⟨d, -, hd⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Establish `h1` using `left_ne_zero_of_mul hd`. Rewrite `h1` using `[Matrix.mul_apply]`.

Take `⟨c, -, hc⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h1`. Conclude with `⟨c, d, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc, right_ne_zero_of_mul hd⟩`.
-/
theorem UpperTheory.Reformulated.B.Qk1.triple_ne :
    ∀ {R ι : Type} [inst : CommRing R] [inst_1 : Fintype ι]
    {A Y B : Matrix ι ι R} {a b : ι},
    (A * Y * B) a b ≠ (0 : R) → ∃ (c : ι) (d : ι), A a c ≠ (0 : R) ∧ Y c d ≠ (0 : R) ∧ B d b ≠ (0 : R) := by
  intro R ι _ _ A Y B a b h
  rw [Matrix.mul_apply] at h
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hd
  rw [Matrix.mul_apply] at h1
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  exact ⟨c, d, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc, right_ne_zero_of_mul hd⟩
