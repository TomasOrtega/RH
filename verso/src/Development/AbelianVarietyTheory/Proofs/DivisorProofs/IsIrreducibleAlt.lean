import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.IndLineGL

namespace GlobalTheory.MidMixedCell

/- English proof (translation)
Introduce `hG hBZ hB k _ _ _ _ a a' m α₀ β₀ hα hβ hαu hβu hlt b hb`. Take `⟨hrow, hcol⟩` from `b.2`. Establish `r0 : b.1 false 0 + b.1 false 1 + b.1 false 2 = a`. Establish `h` using `hrow false`. Rewrite `h` using `[Fin.sum_univ_three]`.

Simplify using `using h`. Establish `r1 : b.1 true 0 + b.1 true 1 + b.1 true 2 = a'`. Establish `h` using `hrow true`. Rewrite `h` using `[Fin.sum_univ_three]`. Simplify using `using h`.

Establish `c0 : b.1 false 0 + b.1 true 0 = 1`. Establish `h` using `hcol 0`. Rewrite `h` using `[Fintype.sum_bool]`. Rewrite using `[add_comm]`. Conclude with `h.trans (Fintype.card_fin 1)`.

Establish `c2 : b.1 false 2 + b.1 true 2 = 1`. Establish `h` using `hcol 2`. Rewrite `h` using `[Fintype.sum_bool]`. Rewrite using `[add_comm]`. Conclude with `h.trans (Fintype.card_fin 1)`.

Establish `hmix` using `GlobalTheory.MixedCell.isIrreducible hG hBZ hB k (b.1 false 1) (b.1 true 1) (by omega) α₀ β₀ hα hβ hαu hβu`. Unfold `cellMid`. Establish `hcases : (b.1 false 0 = 1 ∧ b.1 false 2 = 0 ∧ b.1 true 0 = 0 ∧ b.1 true 2 = 1) ∨ (b.1 false 0 = 0 ∧ b.1 false 2 = 1 ∧ b.1 true 0 = 1 ∧ b.1 true 2 = 0)` using `by omega`. Break down `hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩` into its components or cases. Establish `e1 : α₀ * absPow k ((((b.1 false 0 : ℕ) : ℂ) - (b.1 false 2 : ℕ)) / 2) = α₀ * absPow k (1 / 2)`.

Rewrite using `[h1, h2]`. Evaluate the numerical expressions. Establish `e2 : β₀ * absPow k ((((b.1 true 0 : ℕ) : ℂ) - (b.1 true 2 : ℕ)) / 2) = β₀ * absPow k (-(1 / 2))`. Rewrite using `[h3, h4]`. Evaluate the numerical expressions.

Rewrite using `[e1, e2]`. Conclude with `hmix.1`. Establish `e1 : α₀ * absPow k ((((b.1 false 0 : ℕ) : ℂ) - (b.1 false 2 : ℕ)) / 2) = α₀ * absPow k (-(1 / 2))`. Rewrite using `[h1, h2]`. Evaluate the numerical expressions.

Establish `e2 : β₀ * absPow k ((((b.1 true 0 : ℕ) : ℂ) - (b.1 true 2 : ℕ)) / 2) = β₀ * absPow k (1 / 2)`. Rewrite using `[h3, h4]`. Evaluate the numerical expressions. Rewrite using `[e1, e2]`. Conclude with `hmix.2`.
-/
theorem isIrreducible : GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) → (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) → a' < a →
    ∀ b : SizeMatrix (Two (Fin a) (Fin a')) (fun j : Fin 3 => Fin (blk3 m j)),
      b.1 false 0 ≠ b.1 false 2 → (cellMid k α₀ β₀ b.1).IsIrreducible := by
  intro hG hBZ hB k _ _ _ _ a a' m α₀ β₀ hα hβ hαu hβu hlt b hb
  obtain ⟨hrow, hcol⟩ := b.2
  have r0 : b.1 false 0 + b.1 false 1 + b.1 false 2 = a := by
    have h := hrow false
    rw [Fin.sum_univ_three] at h
    simpa using h
  have r1 : b.1 true 0 + b.1 true 1 + b.1 true 2 = a' := by
    have h := hrow true
    rw [Fin.sum_univ_three] at h
    simpa using h
  have c0 : b.1 false 0 + b.1 true 0 = 1 := by
    have h := hcol 0
    rw [Fintype.sum_bool] at h
    rw [add_comm]; exact h.trans (Fintype.card_fin 1)
  have c2 : b.1 false 2 + b.1 true 2 = 1 := by
    have h := hcol 2
    rw [Fintype.sum_bool] at h
    rw [add_comm]; exact h.trans (Fintype.card_fin 1)
  have hmix := GlobalTheory.MixedCell.isIrreducible hG hBZ hB k (b.1 false 1) (b.1 true 1) (by omega) α₀ β₀ hα hβ hαu hβu
  unfold cellMid
  have hcases : (b.1 false 0 = 1 ∧ b.1 false 2 = 0 ∧ b.1 true 0 = 0 ∧ b.1 true 2 = 1) ∨
      (b.1 false 0 = 0 ∧ b.1 false 2 = 1 ∧ b.1 true 0 = 1 ∧ b.1 true 2 = 0) := by omega
  rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have e1 : α₀ * absPow k ((((b.1 false 0 : ℕ) : ℂ) - (b.1 false 2 : ℕ)) / 2) = α₀ * absPow k (1 / 2) := by
      rw [h1, h2]; norm_num
    have e2 : β₀ * absPow k ((((b.1 true 0 : ℕ) : ℂ) - (b.1 true 2 : ℕ)) / 2) = β₀ * absPow k (-(1 / 2)) := by
      rw [h3, h4]; norm_num
    rw [e1, e2]
    exact hmix.1
  · have e1 : α₀ * absPow k ((((b.1 false 0 : ℕ) : ℂ) - (b.1 false 2 : ℕ)) / 2) = α₀ * absPow k (-(1 / 2)) := by
      rw [h1, h2]; norm_num
    have e2 : β₀ * absPow k ((((b.1 true 0 : ℕ) : ℂ) - (b.1 true 2 : ℕ)) / 2) = β₀ * absPow k (1 / 2) := by
      rw [h3, h4]; norm_num
    rw [e1, e2]
    exact hmix.2

end GlobalTheory.MidMixedCell
