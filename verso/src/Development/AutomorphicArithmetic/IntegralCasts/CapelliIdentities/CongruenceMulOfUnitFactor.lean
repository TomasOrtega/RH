import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza4.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.Yza4.Cg :
    {l : ℕ} → [inst : Fact (Nat.Prime l)] → ℕ → UpperTheory.Reformulated.B.Yza4.Qbar l → UpperTheory.Reformulated.B.Yza4.Qbar l → Prop :=
    fun {l : ℕ} [Fact (Nat.Prime l)] (n : ℕ) (a b : UpperTheory.Reformulated.B.Yza4.Qbar l) ↦
      ‖a - b‖ ≤ ‖(↑l : UpperTheory.Reformulated.B.Yza4.Qbar l) ^ n‖

/- English proof (translation)
Introduce `l _ n P h un D h1 h2 hu hh`. Unfold `UpperTheory.Reformulated.B.Yza4.Cg at *`. Rewrite `h1`, the goal using `[sub_zero]`. Use `set c : ℝ := ‖(↑l : PadicAlgCl l) ^ n‖ with hc`. Establish `hc0 : 0 ≤ c` using `norm_nonneg _`.

Establish `hmul : ∀ a b : PadicAlgCl l, ‖a * b‖ = ‖a‖ * ‖b‖` using `fun a b => norm_mul a b`. Establish `key : un * (D * h) = P * h + (un * D - P) * h` using `by ring`. Establish `h3 : ‖(un * D - P) * h‖ ≤ c`. Rewrite using `[hmul, norm_sub_rev]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h4 : ‖un * (D * h)‖ ≤ c`. Rewrite using `[key]`. Conclude with `(PadicAlgCl.isNonarchimedean l _ _).trans (max_le h1 h3)`. Rewrite `h4` using `[hmul, hu, one_mul]`. Conclude with `h4`.
-/
theorem UpperTheory.Reformulated.B.Yza4.congruence_mul_of_unit_factor :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {n : ℕ} {P h un D : UpperTheory.Reformulated.B.Yza4.Qbar l},
      UpperTheory.Reformulated.B.Yza4.Cg n (P * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) →
        UpperTheory.Reformulated.B.Yza4.Cg n P (un * D) →
          ‖un‖ = (1 : ℝ) → ‖h‖ ≤ (1 : ℝ) → UpperTheory.Reformulated.B.Yza4.Cg n (D * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) := by
  intro l _ n P h un D h1 h2 hu hh
  unfold UpperTheory.Reformulated.B.Yza4.Cg at *
  rw [sub_zero] at h1 ⊢
  set c : ℝ := ‖(↑l : PadicAlgCl l) ^ n‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hmul : ∀ a b : PadicAlgCl l, ‖a * b‖ = ‖a‖ * ‖b‖ := fun a b => norm_mul a b
  have key : un * (D * h) = P * h + (un * D - P) * h := by ring
  have h3 : ‖(un * D - P) * h‖ ≤ c := by
    rw [hmul, norm_sub_rev]
    calc ‖P - un * D‖ * ‖h‖ ≤ c * 1 := mul_le_mul h2 hh (norm_nonneg _) hc0
      _ = c := mul_one c
  have h4 : ‖un * (D * h)‖ ≤ c := by
    rw [key]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le h1 h3)
  rw [hmul, hu, one_mul] at h4
  exact h4
