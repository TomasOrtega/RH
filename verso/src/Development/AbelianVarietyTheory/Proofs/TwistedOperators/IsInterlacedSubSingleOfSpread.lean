import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

namespace GlobalTheory.SepReal

/- English proof (translation)
Introduce `n ε lam ε' mu hI hw hm hne s`. Establish `h01 : ∀ a, (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 0 ∨ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 1`. Introduce `a`. Distinguish the cases in `h : a = s`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Establish `hb : ∀ a, 0 ≤ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ∧ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ≤ 1`. Introduce `a`. Apply the tactic sequence `rcases h01 a with h | h <;> rw [h] <;> norm_num`.

Establish `key : ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim (lam - Pi.single s 1) mu y < Sum.elim (lam - Pi.single s 1) mu x ↔ Sum.elim lam mu y < Sum.elim lam mu x`. Introduce and unpack `(a | i) (c | j)`. Simplify using `only [Sum.elim_inl, Pi.sub_apply]`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality.

Simplify using the standard rewrite rules. Establish `hw'` using `hw a c hac`. Establish `ha` using `h01 a`. Establish `hc` using `h01 c`. Generalize the expression as in `(Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = da at ha`.

Generalize the expression as in `(Pi.single s (1:ℝ) : Fin (n+1) → ℝ) c = dc at hc`. Apply the tactic sequence `rcases le_abs.1 hw' with h | h <;> rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>`. Apply the tactic sequence `constructor <;> intro h' <;> linarith`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]`. Establish `hba` using `hb a`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`. Use `hm a j h` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]`. Establish `hbc` using `hb c`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `h'`. Establish `hlt : mu i < lam c` using `lt_of_le_of_ne (not_lt.1 h') (fun e => hne c i e.symm)`. Use `hm c i hlt` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Introduce `x y h hz`. Rewrite `h` using `[key]`. Conclude with `hI x y h (fun z hz' => hz z ⟨(key z y).2 hz'.1, (key x z).2 hz'.2⟩)`.
-/
theorem interlaced_sub_single : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ},
    GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) →
      (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  intro n ε lam ε' mu hI hw hm hne s
  have h01 : ∀ a, (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 0 ∨ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 1 := by
    intro a
    by_cases h : a = s
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hb : ∀ a, 0 ≤ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ∧ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ≤ 1 := by
    intro a
    rcases h01 a with h | h <;> rw [h] <;> norm_num
  have key : ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim (lam - Pi.single s 1) mu y < Sum.elim (lam - Pi.single s 1) mu x ↔
      Sum.elim lam mu y < Sum.elim lam mu x := by
    rintro (a | i) (c | j)
    · simp only [Sum.elim_inl, Pi.sub_apply]
      by_cases hac : a = c
      · subst hac; simp
      · have hw' := hw a c hac
        have ha := h01 a
        have hc := h01 c
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = da at ha
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) c = dc at hc
        rcases le_abs.1 hw' with h | h <;> rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
          constructor <;> intro h' <;> linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hba := hb a
      constructor
      · intro h; linarith
      · intro h; have := hm a j h; linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hbc := hb c
      constructor
      · intro h
        by_contra h'
        have hlt : mu i < lam c := lt_of_le_of_ne (not_lt.1 h') (fun e => hne c i e.symm)
        have := hm c i hlt
        linarith
      · intro h; linarith
    · simp
  intro x y h hz
  rw [key] at h
  exact hI x y h (fun z hz' => hz z ⟨(key z y).2 hz'.1, (key x z).2 hz'.2⟩)

end GlobalTheory.SepReal
