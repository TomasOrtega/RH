import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FockLin

open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

variable {K : Type} [Field K] {n' m : ℕ} {vec : Fin n' → Bool} {TT : Finset (Fin n')} {d : Fin n' → ℕ} {c : ℕ}

/- English proof (translation)
Use `⟨0, by simp, fun G _ H _ => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero, fockR_zero_right, combo_zero, map_zero, fockR_zero_left]`.
-/
theorem ok_zero_left (s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c 0 s := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_right, combo_zero, map_zero, fockR_zero_left]

/- English proof (translation)
Use `⟨0, by simp, fun G _ H _ => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero, fockR_zero_left, combo_zero, map_zero, fockR_zero_left]`.
-/
theorem ok_zero_right (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c β 0 := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_left, combo_zero, map_zero, fockR_zero_left]

/- English proof (translation)
Take `⟨f₁, hf₁, e₁⟩` from `h₁`. Take `⟨f₂, hf₂, e₂⟩` from `h₂`. Use `⟨f₁ + f₂, fun l hl => ?_, fun G hG H hH => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_union.1 (Finsupp.support_add hl) with h | h exacts [hf₁ l h, hf₂ l h]` into its components or cases. Rewrite using `[mul_add, fockR_add_right, e₁ G hG H hH, e₂ G hG H hH, combo_add, map_add, fockR_add_left]`.
-/
theorem ok_add_left {β₁ β₂ s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h₁ : Ok K n' m vec TT d c β₁ s) (h₂ : Ok K n' m vec TT d c β₂ s) : Ok K n' m vec TT d c (β₁ + β₂) s := by
  obtain ⟨f₁, hf₁, e₁⟩ := h₁
  obtain ⟨f₂, hf₂, e₂⟩ := h₂
  refine ⟨f₁ + f₂, fun l hl => ?_, fun G hG H hH => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with h | h
    exacts [hf₁ l h, hf₂ l h]
  · rw [mul_add, fockR_add_right, e₁ G hG H hH, e₂ G hG H hH, combo_add, map_add,
      fockR_add_left]

/- English proof (translation)
Take `⟨f₁, hf₁, e₁⟩` from `h₁`. Take `⟨f₂, hf₂, e₂⟩` from `h₂`. Use `⟨f₁ + f₂, fun l hl => ?_, fun G hG H hH => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_union.1 (Finsupp.support_add hl) with h | h exacts [hf₁ l h, hf₂ l h]` into its components or cases. Rewrite using `[mul_add, fockR_add_left, e₁ G hG H hH, e₂ G hG H hH, combo_add, map_add, fockR_add_left]`.
-/
theorem ok_add_right {β s₁ s₂ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h₁ : Ok K n' m vec TT d c β s₁) (h₂ : Ok K n' m vec TT d c β s₂) : Ok K n' m vec TT d c β (s₁ + s₂) := by
  obtain ⟨f₁, hf₁, e₁⟩ := h₁
  obtain ⟨f₂, hf₂, e₂⟩ := h₂
  refine ⟨f₁ + f₂, fun l hl => ?_, fun G hG H hH => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with h | h
    exacts [hf₁ l h, hf₂ l h]
  · rw [mul_add, fockR_add_left, e₁ G hG H hH, e₂ G hG H hH, combo_add, map_add,
      fockR_add_left]

/- English proof (translation)
Take `⟨f, hf, e⟩` from `h`. Use `⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul_comm, fockR_smul_right, e G hG H hH, combo_smul, map_smul, fockR_smul_left]`.
-/
theorem ok_smul_left (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c (a • β) s := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩
  rw [mul_smul_comm, fockR_smul_right, e G hG H hH, combo_smul, map_smul,
    fockR_smul_left]

/- English proof (translation)
Take `⟨f, hf, e⟩` from `h`. Use `⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul_comm, fockR_smul_left, e G hG H hH, combo_smul, map_smul, fockR_smul_left]`.
-/
theorem ok_smul_right (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c β (a • s) := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩
  rw [mul_smul_comm, fockR_smul_left, e G hG H hH, combo_smul, map_smul,
    fockR_smul_left]

/- English proof (translation)
Introduce `K _ n' m vec TT d c M hM β hβ s hs`. Unfold `PI.TO.tensorLat at hβ hs`. Establish `key : ∀ F : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, (∀ t, F t ∈ M t) → Ok K n' m vec TT d c (∏ t, PI.TO.blockEmb K t (F t)) s`. Introduce `F hF`. Proceed by induction on `hs using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨S, hS, rfl⟩` from `hx`. Conclude with `hM F S hF hS`. Consider the case `zero => exact ok_zero_right _`. Consider the case `add x y _ _ hx hy => exact ok_add_right hx hy`.

Consider the case `smul a x _ hx => exact ok_smul_right a hx`. Proceed by induction on `hβ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨F, hF, rfl⟩` from `hx`. Conclude with `key F hF`.

Consider the case `zero => exact ok_zero_left _`. Consider the case `add x y _ _ hx hy => exact ok_add_left hx hy`. Consider the case `smul a x _ hx => exact ok_smul_left a hx`.
-/
theorem stepSpan : StepSpan := by
  intro K _ n' m vec TT d c M hM β hβ s hs
  unfold PI.TO.tensorLat at hβ hs
  have key : ∀ F : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, (∀ t, F t ∈ M t) →
      Ok K n' m vec TT d c (∏ t, PI.TO.blockEmb K t (F t)) s := by
    intro F hF
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, hS, rfl⟩ := hx
      exact hM F S hF hS
    | zero => exact ok_zero_right _
    | add x y _ _ hx hy => exact ok_add_right hx hy
    | smul a x _ hx => exact ok_smul_right a hx
  induction hβ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact key F hF
  | zero => exact ok_zero_left _
  | add x y _ _ hx hy => exact ok_add_left hx hy
  | smul a x _ hx => exact ok_smul_left a hx

end PI.TOW
