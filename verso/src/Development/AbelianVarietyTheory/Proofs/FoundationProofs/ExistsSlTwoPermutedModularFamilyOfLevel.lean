import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FamOfLevel

/- English proof (translation)
Simplify using `[redGL]`.
-/
theorem redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) : redGL N (γ * δ) = redGL N γ * redGL N δ := by
  simp [redGL]

/- English proof (translation)
Rewrite using `[CongruenceSubgroup.Gamma_mem', redGL]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Matrix.SpecialLinearGroup.toGL_injective` to reduce the goal to its premises. Simplify using `using h`.

Introduce `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem redGL_eq_one_iff (N : ℕ) (γ : SL(2, ℤ)) : redGL N γ = 1 ↔ γ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem', redGL]
  constructor
  · intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    simpa using h
  · intro h
    rw [h]; simp

/- English proof (translation)
Establish `hη : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma N`. Rewrite using `[← redGL_eq_one_iff, redGL_mul, h, ← redGL_mul, mul_inv_cancel]`. Simplify using `[redGL]`. Establish `: γ = (γ * δ⁻¹) * δ` using `by group`. Rewrite using `[this, SlashAction.slash_mul, hf _ hη]`.
-/
theorem slash_eq_of_redGL_eq (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) {γ δ : SL(2, ℤ)}
    (h : redGL N γ = redGL N δ) : f ∣[k] γ = f ∣[k] δ := by
  have hη : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma N := by
    rw [← redGL_eq_one_iff, redGL_mul, h, ← redGL_mul, mul_inv_cancel]
    simp [redGL]
  have : γ = (γ * δ⁻¹) * δ := by group
  rw [this, SlashAction.slash_mul, hf _ hη]

/- English proof (translation)
Set `F : GL (Fin 2) (ZMod N) → ℍ → ℂ` to `fun α => if h : ∃ γ : SL(2, ℤ), α = redGL N γ then f ∣[k] h.choose else 0`. Establish `hF : ∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ`. Introduce `γ`. Establish `h : ∃ δ : SL(2, ℤ), redGL N γ = redGL N δ` using `⟨γ, rfl⟩`. Simplify using `only [F, dif_pos h]`.

Conclude with `slash_eq_of_redGL_eq N k f hf h.choose_spec.symm`. Use `⟨F, ?_, hF, ?_⟩` and prove the remaining obligations. Introduce `α γ`. Rewrite using `[gact_one]`. Distinguish the cases in `h : ∃ δ : SL(2, ℤ), α = redGL N δ`.

Take `⟨δ, rfl⟩` from `h`. Rewrite using `[hF, ← redGL_mul, hF, SlashAction.slash_mul]`. Establish `h' : ¬ ∃ δ : SL(2, ℤ), α * redGL N γ = redGL N δ`. Introduce and unpack `⟨δ, hδ⟩`. Apply `h` to reduce the goal to its premises.

Use `⟨δ * γ⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[redGL_mul, ← hδ, mul_assoc, ← redGL_mul, mul_inv_cancel]`. Simplify using `[redGL]`. Simplify using `only [F, dif_neg h, dif_neg h']`. Conclude with `SlashAction.zero_slash _ _`.

Introduce `α`. Distinguish the cases in `h : ∃ γ : SL(2, ℤ), α = redGL N γ`. Conclude with `Or.inl h`. Use `right`. Simplify using `only [F, dif_neg h]`.
-/
theorem exists_family (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) :
    ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧
      (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧
      ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  classical
  let F : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α =>
    if h : ∃ γ : SL(2, ℤ), α = redGL N γ then f ∣[k] h.choose else 0
  have hF : ∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ := by
    intro γ
    have h : ∃ δ : SL(2, ℤ), redGL N γ = redGL N δ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact slash_eq_of_redGL_eq N k f hf h.choose_spec.symm
  refine ⟨F, ?_, hF, ?_⟩
  · intro α γ
    rw [gact_one]
    by_cases h : ∃ δ : SL(2, ℤ), α = redGL N δ
    · obtain ⟨δ, rfl⟩ := h
      rw [hF, ← redGL_mul, hF, SlashAction.slash_mul]
    · have h' : ¬ ∃ δ : SL(2, ℤ), α * redGL N γ = redGL N δ := by
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ * γ⁻¹, ?_⟩
        rw [redGL_mul, ← hδ, mul_assoc, ← redGL_mul, mul_inv_cancel]
        simp [redGL]
      simp only [F, dif_neg h, dif_neg h']
      exact SlashAction.zero_slash _ _
  · intro α
    by_cases h : ∃ γ : SL(2, ℤ), α = redGL N γ
    · exact Or.inl h
    · right; simp only [F, dif_neg h]

end GlobalTheory.FamOfLevel
