import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `τ`. Establish `hP : {p : Fin 2 → ℤ | ¬ (2 * τ.im < Complex.normSq ((p 0 : ℂ) * τ + p 1))}.Finite` using `Filter.eventually_cofinite.1 ((ModularGroup.tendsto_normSq_coprime_pair τ).eventually_gt_atTop (2 * τ.im))`. Establish `hrow : ∀ p : Fin 2 → ℤ, {γ : SL(2, ℤ) | γ 1 = p ∧ |(γ • τ).re| ≤ 1 / 2}.Finite`. Introduce `p`. Distinguish the cases in `hp : IsCoprime (p 0) (p 1)`.

Establish `h` using `Filter.eventually_cofinite.1 ((ModularGroup.tendsto_abs_re_smul τ hp).eventually_gt_atTop (1 / 2 : ℝ))`. Use `(h.image Subtype.val).subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨h1, h2⟩`. Conclude with `⟨⟨γ, h1⟩, not_lt.2 h2, rfl⟩`. Use `Set.finite_empty.subset ?_` and prove the remaining obligations.

Introduce and unpack `γ ⟨h1, -⟩`. Conclude with `hp (h1 ▸ ModularGroup.bottom_row_coprime γ)`. Use `(hP.biUnion fun p _ => hrow p).subset ?_` and prove the remaining obligations. Introduce `γ hγ`. Establish `h3` using `ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ`.

Establish `hpos` using `(γ • τ).im_pos`. Establish `hhalf : (1 : ℝ) / 2 ≤ (γ • τ).im` using `by nlinarith`. Rewrite `hhalf` using `[ModularGroup.im_smul_eq_div_normSq, le_div_iff₀ (Complex.normSq_pos.2 (denom_ne_zero _ _))]`. Rewrite using `[Set.mem_iUnion₂]`. Use `⟨γ 1, ?_, rfl, hγ.2⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq, not_lt]`. Simplify using `[UpperHalfPlane.denom] at hhalf ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem finite_smul_mem_fd : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  intro τ
  have hP : {p : Fin 2 → ℤ | ¬ (2 * τ.im < Complex.normSq ((p 0 : ℂ) * τ + p 1))}.Finite :=
    Filter.eventually_cofinite.1
      ((ModularGroup.tendsto_normSq_coprime_pair τ).eventually_gt_atTop (2 * τ.im))
  have hrow : ∀ p : Fin 2 → ℤ, {γ : SL(2, ℤ) | γ 1 = p ∧ |(γ • τ).re| ≤ 1 / 2}.Finite := by
    intro p
    by_cases hp : IsCoprime (p 0) (p 1)
    · have h := Filter.eventually_cofinite.1
        ((ModularGroup.tendsto_abs_re_smul τ hp).eventually_gt_atTop (1 / 2 : ℝ))
      refine (h.image Subtype.val).subset ?_
      rintro γ ⟨h1, h2⟩
      exact ⟨⟨γ, h1⟩, not_lt.2 h2, rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro γ ⟨h1, -⟩
      exact hp (h1 ▸ ModularGroup.bottom_row_coprime γ)
  refine (hP.biUnion fun p _ => hrow p).subset ?_
  intro γ hγ
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  have hpos := (γ • τ).im_pos
  have hhalf : (1 : ℝ) / 2 ≤ (γ • τ).im := by nlinarith
  rw [ModularGroup.im_smul_eq_div_normSq, le_div_iff₀ (Complex.normSq_pos.2 (denom_ne_zero _ _))] at hhalf
  rw [Set.mem_iUnion₂]
  refine ⟨γ 1, ?_, rfl, hγ.2⟩
  simp only [Set.mem_setOf_eq, not_lt]
  simp [UpperHalfPlane.denom] at hhalf ⊢
  linarith

end GlobalTheory.EisM
