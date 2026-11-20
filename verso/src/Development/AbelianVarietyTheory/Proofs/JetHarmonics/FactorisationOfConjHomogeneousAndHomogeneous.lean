import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `T Wp Wq _ _ _ _ _ _ l l' J A Bb hA hB hJA hJB`. Distinguish the cases in `h1 : ∀ x, l x = 0`. Use `⟨0, fun x y X => ?_⟩` and prove the remaining obligations. Use extensionality with `c`. Establish `h0` using `hA y 0 c 0`.

Rewrite using `[hJA, h1 x, map_zero]`. Simplify using `using h0`. Distinguish the cases in `h2 : ∀ y, l' y = 0`. Use `⟨0, fun x y X => ?_⟩` and prove the remaining obligations. Use extensionality with `c`.

Establish `h0` using `hB x 0 c 0`. Rewrite using `[hJB, h2 y, map_zero]`. Simplify using `using h0`. Use `push Not at h1 h2`. Take `⟨x₀, hx⟩` from `h1`.

Take `⟨y₀, hy⟩` from `h2`. Establish `hadj : ∀ (a : Wq) (b v : Wp), ContinuousLinearMap.adjoint ((innerSL ℂ a).smulRight b) v = ⟪b, v⟫_ℂ • a`. Introduce `a b v`. Use `ext_inner_right ℂ fun w => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_left, inner_smul_left]`.

Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right, inner_conj_symm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp : ⟪l x₀, l x₀⟫_ℂ ≠ 0` using `fun h => hx (inner_self_eq_zero.mp h)`. Establish `hq : ⟪l' y₀, l' y₀⟫_ℂ ≠ 0` using `fun h => hy (inner_self_eq_zero.mp h)`. Establish `key : ∀ y a c, A y a c = (⟪a, l' y⟫_ℂ * (⟪l x₀, l x₀⟫_ℂ)⁻¹) • Bb x₀ (l x₀) c`.

Introduce `y a c`. Establish `e1` using `hJA x₀ y ((innerSL ℂ a).smulRight (l x₀)) c`. Establish `e2` using `hJB x₀ y ((innerSL ℂ a).smulRight (l x₀)) c`. Rewrite `e1` using `[hadj, hA]`. Rewrite `e2` using `[ContinuousLinearMap.smulRight_apply, hB, innerSL_apply_apply, e1]`.

Establish `hs : star ⟪l x₀, l x₀⟫_ℂ = ⟪l x₀, l x₀⟫_ℂ` using `inner_conj_symm (𝕜 := ℂ) _ _`. Rewrite `e2` using `[hs]`. Rewrite using `[mul_comm, mul_smul, ← e2, smul_smul, inv_mul_cancel₀ hp, one_smul]`. Use `⟨((⟪l' y₀, l' y₀⟫_ℂ)⁻¹ * (⟪l x₀, l x₀⟫_ℂ)⁻¹) • J x₀ y₀ ((innerSL ℂ (l' y₀)).smulRight (l x₀)), fun x y X => ?_⟩` and prove the remaining obligations. Use extensionality with `c`.

Rewrite using `[ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hJB x₀, ContinuousLinearMap.smulRight_apply, hB, innerSL_apply_apply, hJA, key, ContinuousLinearMap.adjoint_inner_left, smul_smul, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem factorisation_of_two_partial_integrations : ∀ (T Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (l : T → Wp) (l' : T → Wq) (J : T → T → (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (A : T → Wq → Wq → Wp) (Bb : T → Wp → Wq → Wp), (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) → (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) → (∀ x y X c, J x y X c = A y (ContinuousLinearMap.adjoint X (l x)) c) → (∀ x y X c, J x y X c = Bb x (X (l' y)) c) → ∃ OO : Wq →L[ℂ] Wp, ∀ x y X, J x y X = ⟪l x, X (l' y)⟫_ℂ • OO := by
  intro T Wp Wq _ _ _ _ _ _ l l' J A Bb hA hB hJA hJB
  by_cases h1 : ∀ x, l x = 0
  · refine ⟨0, fun x y X => ?_⟩
    ext c
    have h0 := hA y 0 c 0
    rw [hJA, h1 x, map_zero]
    simpa using h0
  by_cases h2 : ∀ y, l' y = 0
  · refine ⟨0, fun x y X => ?_⟩
    ext c
    have h0 := hB x 0 c 0
    rw [hJB, h2 y, map_zero]
    simpa using h0
  push Not at h1 h2
  obtain ⟨x₀, hx⟩ := h1
  obtain ⟨y₀, hy⟩ := h2
  have hadj : ∀ (a : Wq) (b v : Wp),
      ContinuousLinearMap.adjoint ((innerSL ℂ a).smulRight b) v = ⟪b, v⟫_ℂ • a := by
    intro a b v
    refine ext_inner_right ℂ fun w => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_smul_left]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right,
      inner_conj_symm]
    ring
  have hp : ⟪l x₀, l x₀⟫_ℂ ≠ 0 := fun h => hx (inner_self_eq_zero.mp h)
  have hq : ⟪l' y₀, l' y₀⟫_ℂ ≠ 0 := fun h => hy (inner_self_eq_zero.mp h)
  have key : ∀ y a c, A y a c = (⟪a, l' y⟫_ℂ * (⟪l x₀, l x₀⟫_ℂ)⁻¹) • Bb x₀ (l x₀) c := by
    intro y a c
    have e1 := hJA x₀ y ((innerSL ℂ a).smulRight (l x₀)) c
    have e2 := hJB x₀ y ((innerSL ℂ a).smulRight (l x₀)) c
    rw [hadj, hA] at e1
    rw [ContinuousLinearMap.smulRight_apply, hB, innerSL_apply_apply, e1] at e2
    have hs : star ⟪l x₀, l x₀⟫_ℂ = ⟪l x₀, l x₀⟫_ℂ := inner_conj_symm (𝕜 := ℂ) _ _
    rw [hs] at e2
    rw [mul_comm, mul_smul, ← e2, smul_smul, inv_mul_cancel₀ hp, one_smul]
  refine ⟨((⟪l' y₀, l' y₀⟫_ℂ)⁻¹ * (⟪l x₀, l x₀⟫_ℂ)⁻¹) •
    J x₀ y₀ ((innerSL ℂ (l' y₀)).smulRight (l x₀)), fun x y X => ?_⟩
  ext c
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hJB x₀,
    ContinuousLinearMap.smulRight_apply, hB, innerSL_apply_apply, hJA, key,
    ContinuousLinearMap.adjoint_inner_left, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory
