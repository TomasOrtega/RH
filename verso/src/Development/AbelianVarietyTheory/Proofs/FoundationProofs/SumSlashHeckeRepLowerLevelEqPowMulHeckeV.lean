import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Unfold `qs Vo`. Establish `hinj : Function.Injective (fun m : ℕ => l * m)` using `fun x y h => by`. Simplify `h` using `[hl.ne']`. Rewrite using `[← hinj.tsum_eq]`. Use `congr 1`.

Use extensionality with `m`. Simplify using `only [dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Introduce `n hn`. Distinguish the cases in `h : l ∣ n`. Take `⟨m, rfl⟩` from `h`. Conclude with `⟨m, rfl⟩`. Simplify using `[Function.mem_support, h] at hn`.
-/
theorem qExpansionFunction_coeffHeckeVOperator_eq_tsum (l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (τ : ℍ) :
    qs (Vo l a) τ = ∑' m : ℕ, a m * cexp (2 * π * Complex.I * m * ((l : ℂ) * τ)) := by
  unfold qs Vo
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun x y h => by
    simpa [hl.ne'] using h
  rw [← hinj.tsum_eq]
  · congr 1; ext m
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl]
    congr 2; push_cast; ring
  · intro n hn
    by_cases h : l ∣ n
    · obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩
    · simp [Function.mem_support, h] at hn

/- English proof (translation)
Establish `hlC : (0 : ℝ) < l` using `by exact_mod_cast hl`. Set `τ' : ℍ` to `⟨(l : ℂ) * τ, by simpa using mul_pos hlC τ.im_pos⟩`. Establish `hτ' : (τ' : ℂ) = (l : ℂ) * τ` using `rfl`. Establish `key : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ (k - 1) * qs h τ'`. Introduce `j`.

Set `γ : SL(2, ℤ)` to `⟨!![1, 0; (N * (j : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩`. Establish `hγ` using `hf.2 γ (by simp [γ]) τ'`. Establish `hpt : ((γ • τ' : ℍ) : ℂ) = ((l : ℂ) * τ) / (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1)`. Rewrite using `[coe_specialLinearGroup_apply]`. Simplify using `[γ, hτ']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hden : ((((N * (j : ℕ) : ℤ)) : ℂ) * (τ' : ℂ) + 1) = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1)`. Rewrite using `[hτ']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ≠ 0`. Introduce `h0`. Use `congrArg Complex.im h0` as an intermediate fact. Simplify using `at this`. Break down `this with h1 | h1` into its components or cases.

Apply the tactic sequence `have h2 : N * l * (j : ℕ) = 0 := by rcases h1 with (h1 | h1) | h1 <;> simp [h1]`. Simplify using `[h2] at h0`. Conclude with `(τ.im_pos.ne' h1)`. Establish `hγ' : qs h (γ • τ') = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ^ k * qs h τ'`. Rewrite using `[← hden, hγ]`.

Simplify using `[γ, ch]`. Establish `harg : ((l : ℂ) * τ / ((N : ℂ) * l * ((j : ℕ) : ℂ) * τ + 1)) = ((γ • τ' : ℍ) : ℂ)`. Rewrite using `[hpt]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `slz repL`. Simplify using `[Matrix.det_fin_two]`. Rewrite using `[harg, ofComplex_apply, hγ']`. Move the coercions through the operations in `at hne ⊢`. Clear the denominators using the available nonvanishing facts.

Simplify using `only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[qExpansionFunction_coeffHeckeVOperator_eq_tsum l hl h τ]`. Establish `hp : (l : ℂ) * (l : ℂ) ^ (k - 1) = (l : ℂ) ^ k`. Rewrite using `[← pow_succ', Nat.sub_add_cancel hk]`. Rewrite using `[← mul_assoc, hp]`.

Both sides reduce to the same expression.
-/
theorem adjU_sum (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (hk : 1 ≤ k) (hl : 0 < l)
    (hf : MF k N (ch ε) h) (τ : ℍ) :
    ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  have hlC : (0 : ℝ) < l := by exact_mod_cast hl
  let τ' : ℍ := ⟨(l : ℂ) * τ, by simpa using mul_pos hlC τ.im_pos⟩
  have hτ' : (τ' : ℂ) = (l : ℂ) * τ := rfl
  have key : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ (k - 1) * qs h τ' := by
    intro j
    let γ : SL(2, ℤ) := ⟨!![1, 0; (N * (j : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩
    have hγ := hf.2 γ (by simp [γ]) τ'
    have hpt : ((γ • τ' : ℍ) : ℂ) = ((l : ℂ) * τ) / (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [coe_specialLinearGroup_apply]; simp [γ, hτ']; ring
    have hden : ((((N * (j : ℕ) : ℤ)) : ℂ) * (τ' : ℂ) + 1) = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [hτ']; push_cast; ring
    have hne : (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      rcases this with h1 | h1
      · have h2 : N * l * (j : ℕ) = 0 := by rcases h1 with (h1 | h1) | h1 <;> simp [h1]
        simp [h2] at h0
      · exact (τ.im_pos.ne' h1)
    have hγ' : qs h (γ • τ') = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ^ k * qs h τ' := by
      rw [← hden, hγ]; simp [γ, ch]
    have harg : ((l : ℂ) * τ / ((N : ℂ) * l * ((j : ℕ) : ℂ) * τ + 1)) = ((γ • τ' : ℍ) : ℂ) := by
      rw [hpt]; push_cast; ring
    unfold slz repL
    simp [Matrix.det_fin_two]
    rw [harg, ofComplex_apply, hγ']
    push_cast at hne ⊢
    field_simp
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [qExpansionFunction_coeffHeckeVOperator_eq_tsum l hl h τ]
  have hp : (l : ℂ) * (l : ℂ) ^ (k - 1) = (l : ℂ) ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [← mul_assoc, hp]
  rfl
end GlobalTheory.EisM

end
