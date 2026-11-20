import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [act, Fin.sum_univ_two]`.
-/
theorem act_one_gen (x : Fin 2 → ℚ) : act x 1 = x := by
  funext i
  fin_cases i <;> simp [act, Fin.sum_univ_two]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem act_mul_gen (x : Fin 2 → ℚ) (γ δ : SL(2, ℤ)) : act x (γ * δ) = act (act x γ) δ := by
  funext i
  simp only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

/- English proof (translation)
Set `H : Subgroup SL(2, ℤ)` to `{ carrier := {γ | ∀ x τ, P x → f x (γ • τ) = f (act x γ) τ} one_mem' := by`. Introduce `x τ _`. Simplify using `[act_one_gen]`. Use the proof step `mul_mem' := by`. Introduce `γ δ hγ hδ x τ hx`.

Rewrite using `[mul_smul, hγ x _ hx, hδ _ τ (hP x γ hx), act_mul_gen]`. Use the proof step `inv_mem' := by`. Introduce `γ hγ x τ hx`. Establish `h` using `hγ (act x γ⁻¹) (γ⁻¹ • τ) (hP x _ hx)`. Rewrite `h` using `[smul_inv_smul, ← act_mul_gen, inv_mul_cancel, act_one_gen]`.

Conclude with `h.symm }`. Establish `hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ H`. Rewrite using `[Subgroup.closure_le]`. Introduce `γ hγ`. Break down `hγ with rfl | rfl` into its components or cases.

Conclude with `hS`. Conclude with `hT`. Introduce `γ`. Establish `: γ ∈ H` using `hle (by rw [_root_.SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ)`. Conclude with `this`.
-/
theorem modular_law_of_generators (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ)
    (hP : ∀ x γ, P x → P (act x γ))
    (hS : ∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ)
    (hT : ∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) :
    ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {γ | ∀ x τ, P x → f x (γ • τ) = f (act x γ) τ}
      one_mem' := by
        intro x τ _
        simp [act_one_gen]
      mul_mem' := by
        intro γ δ hγ hδ x τ hx
        rw [mul_smul, hγ x _ hx, hδ _ τ (hP x γ hx), act_mul_gen]
      inv_mem' := by
        intro γ hγ x τ hx
        have h := hγ (act x γ⁻¹) (γ⁻¹ • τ) (hP x _ hx)
        rw [smul_inv_smul, ← act_mul_gen, inv_mul_cancel, act_one_gen] at h
        exact h.symm }
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ H := by
    rw [Subgroup.closure_le]
    intro γ hγ
    rcases hγ with rfl | rfl
    · exact hS
    · exact hT
  intro γ
  have : γ ∈ H := hle (by rw [_root_.SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ)
  exact this

end GlobalTheory.Sieg
