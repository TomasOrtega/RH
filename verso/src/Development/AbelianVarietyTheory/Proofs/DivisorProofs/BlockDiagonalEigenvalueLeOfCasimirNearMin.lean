import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticOperatorEigenvectorDiagonalBlockIdentitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirEigenNonnegRealUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEigenvalueDropsOffBlockStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Establish `h1 : (x : ℂ) ^ 2 = α * x + β` using `by linear_combination h`. Establish `h2 : ‖(x : ℂ)‖ ^ 2 ≤ ‖α‖ * ‖(x : ℂ)‖ + ‖β‖`. Combine the equalities or inequalities in the displayed calculation. Use `_ = ‖α * x + β‖ := by rw [h1]`. Use `_ ≤ ‖α * x‖ + ‖β‖ := norm_add_le _ _`.

Use `_ = ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by rw [norm_mul]`. Establish `hx : ‖(x : ℂ)‖ = |x|` using `by rw [Complex.norm_real, Real.norm_eq_abs]`. Rewrite `h2` using `[hx]`. Establish `ha` using `norm_nonneg α`. Establish `hb` using `norm_nonneg β`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `ht : ‖α‖ + ‖β‖ + 1 < |x|` using `lt_of_lt_of_le hc (le_abs_self x)`. Use polynomial arithmetic with `[mul_nonneg hb (by linarith : (0:ℝ) ≤ |x| - 1), mul_pos (by linarith : (0:ℝ) < |x| - (‖α‖ + ‖β‖ + 1)) (by linarith : (0:ℝ) < |x|)]`.
-/
theorem real_root_quad_le {x : ℝ} {α β : ℂ} (h : (x : ℂ) ^ 2 - α * x - β = 0) : x ≤ ‖α‖ + ‖β‖ + 1 := by
  have h1 : (x : ℂ) ^ 2 = α * x + β := by linear_combination h
  have h2 : ‖(x : ℂ)‖ ^ 2 ≤ ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by
    calc ‖(x : ℂ)‖ ^ 2 = ‖(x : ℂ) ^ 2‖ := (norm_pow _ _).symm
    _ = ‖α * x + β‖ := by rw [h1]
    _ ≤ ‖α * x‖ + ‖β‖ := norm_add_le _ _
    _ = ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by rw [norm_mul]
  have hx : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hx] at h2
  have ha := norm_nonneg α
  have hb := norm_nonneg β
  by_contra hc
  push_neg at hc
  have ht : ‖α‖ + ‖β‖ + 1 < |x| := lt_of_lt_of_le hc (le_abs_self x)
  nlinarith [mul_nonneg hb (by linarith : (0:ℝ) ≤ |x| - 1),
    mul_pos (by linarith : (0:ℝ) < |x| - (‖α‖ + ‖β‖ + 1)) (by linarith : (0:ℝ) < |x|)]

/- English proof (translation)
Introduce `ι _ _ s α β`. Use `⟨max (‖α‖ + ‖β‖ + 1) ((2 * ‖α‖ + Fintype.card ι + 1) / 4), ?_⟩` and prove the remaining obligations. Introduce `M _ _ F hGl hq hLoc ω hω x y hy hfalse htrue hcas`. Distinguish the cases in `hz : ∀ j, s j = false → ∑ b, F j b (y b) = 0`. Establish `hbc` using `GlobalTheory.T.quadraticOperator_eigenvector_diagonalBlock_identity ι M s F α β x y hq hfalse htrue hz`.

Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, y a ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hy (funext h)`. Establish `h0 : (x : ℂ) ^ 2 - α * x - β = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `ha ((smul_eq_zero.mp (hbc a)).resolve_left hne)`. Conclude with `le_max_of_le_left (real_root_quad_le h0)`. Use `push_neg at hz`. Take `⟨j, hj, hzj⟩` from `hz`.

Establish `hd` using `GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock ι M s F α β x ω y hGl hq hfalse htrue hcas j hj`. Take `⟨U, hU, hUU⟩` from `hLoc {∑ b, F j b (y b)}`. Establish `hzU : ∑ b, F j b (y b) ∈ U` using `hU _ (Finset.mem_singleton_self _)`. Establish `him` using `((GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hUU).1 _ _ hzU hzj hd).1`. Use `set c : ℂ := (ω : ℂ) - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ) with hc`.

Establish `hcre : c = ((c.re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [him])`. Establish `hlt` using `hω c.re _ hzj (by rw [← hcre]; exact hd)`. Establish `hre : c.re = ω - 4 * x + 2 * α.re + ((Finset.univ.filter fun a => s a = true).card : ℝ) - ((Finset.univ.filter fun a => s a = false).card : ℝ)` using `by simp [hc]`. Establish `hr : ((Finset.univ.filter fun a => s a = true).card : ℝ) ≤ Fintype.card ι`. Use `Finset.card_filter_le (Finset.univ : Finset ι) (fun a => s a = true)` as an intermediate fact.

Rewrite `this` using `[Finset.card_univ]`. Conclude with `this` after adjusting the coercions. Establish `hαre : α.re ≤ ‖α‖` using `Complex.re_le_norm α`. Establish `hr'0 : (0:ℝ) ≤ ((Finset.univ.filter fun a => s a = false).card : ℝ)` using `Nat.cast_nonneg _`. Use `le_max_of_le_right ?_` and prove the remaining obligations.

Rewrite using `[le_div_iff₀ (by norm_num : (0:ℝ) < 4)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem diag_eig_le_of_cas_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  intro ι _ _ s α β
  refine ⟨max (‖α‖ + ‖β‖ + 1) ((2 * ‖α‖ + Fintype.card ι + 1) / 4), ?_⟩
  intro M _ _ F hGl hq hLoc ω hω x y hy hfalse htrue hcas
  by_cases hz : ∀ j, s j = false → ∑ b, F j b (y b) = 0
  · have hbc := GlobalTheory.T.quadraticOperator_eigenvector_diagonalBlock_identity ι M s F α β x y hq hfalse htrue hz
    obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (funext h)
    have h0 : (x : ℂ) ^ 2 - α * x - β = 0 := by
      by_contra hne
      exact ha ((smul_eq_zero.mp (hbc a)).resolve_left hne)
    exact le_max_of_le_left (real_root_quad_le h0)
  · push_neg at hz
    obtain ⟨j, hj, hzj⟩ := hz
    have hd := GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock ι M s F α β x ω y hGl hq hfalse htrue hcas j hj
    obtain ⟨U, hU, hUU⟩ := hLoc {∑ b, F j b (y b)}
    have hzU : ∑ b, F j b (y b) ∈ U := hU _ (Finset.mem_singleton_self _)
    have him := ((GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hUU).1 _ _ hzU hzj hd).1
    set c : ℂ := (ω : ℂ) - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ) with hc
    have hcre : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hlt := hω c.re _ hzj (by rw [← hcre]; exact hd)
    have hre : c.re = ω - 4 * x + 2 * α.re + ((Finset.univ.filter fun a => s a = true).card : ℝ)
      - ((Finset.univ.filter fun a => s a = false).card : ℝ) := by simp [hc]
    have hr : ((Finset.univ.filter fun a => s a = true).card : ℝ) ≤ Fintype.card ι := by
      have := Finset.card_filter_le (Finset.univ : Finset ι) (fun a => s a = true)
      rw [Finset.card_univ] at this
      exact_mod_cast this
    have hαre : α.re ≤ ‖α‖ := Complex.re_le_norm α
    have hr'0 : (0:ℝ) ≤ ((Finset.univ.filter fun a => s a = false).card : ℝ) := Nat.cast_nonneg _
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    linarith

end GlobalTheory.HoweR
