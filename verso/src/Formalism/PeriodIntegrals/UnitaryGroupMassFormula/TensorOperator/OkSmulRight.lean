import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FockLin

open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

variable {K : Type} [Field K] {n' m : ℕ} {vec : Fin n' → Bool} {TT : Finset (Fin n')} {d : Fin n' → ℕ} {c : ℕ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem ok_zero_left (s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c 0 s := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_right, combo_zero, map_zero, fockR_zero_left]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem ok_zero_right (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c β 0 := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_left, combo_zero, map_zero, fockR_zero_left]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.
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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.
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
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem ok_smul_left (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c (a • β) s := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩
  rw [mul_smul_comm, fockR_smul_right, e G hG H hH, combo_smul, map_smul,
    fockR_smul_left]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem ok_smul_right (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c β (a • s) := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩
  rw [mul_smul_comm, fockR_smul_left, e G hG H hH, combo_smul, map_smul,
    fockR_smul_left]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Extract witnesses or component facts from the available result. Treat this case separately. Treat this case separately. Treat this case separately.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
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
