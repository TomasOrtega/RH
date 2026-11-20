import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Take `⟨C, A, hC⟩` from `ha`. Take `⟨C', A', hC'⟩` from `hb`. Establish `C0 : 0 ≤ C`. Use `hC 0` as an intermediate fact. Simplify using `at this`.

Conclude with `le_trans (norm_nonneg _) this`. Establish `C0' : 0 ≤ C'`. Use `hC' 0` as an intermediate fact. Simplify using `at this`. Conclude with `le_trans (norm_nonneg _) this`.

Use `⟨C * C', A + A' + 1, fun n => ?_⟩` and prove the remaining obligations. Unfold `mul`. Establish `hn : (1 : ℝ) ≤ (n : ℝ) + 1` using `by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[norm_mul]`. Establish `h1 : ((p.1 : ℝ) + 1) ≤ (n : ℝ) + 1`. Establish `: p.1 ≤ n` using `by omega`.

Conclude with `Nat.add_le_add_right this 1` after adjusting the coercions. Establish `h2 : ((p.2 : ℝ) + 1) ≤ (n : ℝ) + 1`. Establish `: p.2 ≤ n` using `by omega`. Conclude with `Nat.add_le_add_right this 1` after adjusting the coercions. Establish `e1 : ‖a p.1‖ ≤ C * ((n : ℝ) + 1) ^ A` using `(hC p.1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 A) C0)`.

Establish `e2 : ‖b p.2‖ ≤ C' * ((n : ℝ) + 1) ^ A'` using `(hC' p.2).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 A') C0')`. Combine the equalities or inequalities in the displayed calculation. Use `_ = (n + 1 : ℕ) * (C * C' * ((n : ℝ) + 1) ^ (A + A')) := by`. Rewrite using `[Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]`. Use `_ = C * C' * ((n : ℝ) + 1) ^ (A + A' + 1) := by push_cast; ring`.
-/
theorem polyB_mul (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : PolyB (mul a b) := by
  obtain ⟨C, A, hC⟩ := ha
  obtain ⟨C', A', hC'⟩ := hb
  have C0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  have C0' : 0 ≤ C' := by
    have := hC' 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * C', A + A' + 1, fun n => ?_⟩
  unfold mul
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2‖
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖a p.1 * b p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, C * C' * ((n : ℝ) + 1) ^ (A + A') := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [norm_mul]
        have h1 : ((p.1 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : p.1 ≤ n := by omega
          exact_mod_cast Nat.add_le_add_right this 1
        have h2 : ((p.2 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : p.2 ≤ n := by omega
          exact_mod_cast Nat.add_le_add_right this 1
        have e1 : ‖a p.1‖ ≤ C * ((n : ℝ) + 1) ^ A :=
          (hC p.1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 A) C0)
        have e2 : ‖b p.2‖ ≤ C' * ((n : ℝ) + 1) ^ A' :=
          (hC' p.2).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 A') C0')
        calc ‖a p.1‖ * ‖b p.2‖ ≤ (C * ((n : ℝ) + 1) ^ A) * (C' * ((n : ℝ) + 1) ^ A') :=
              mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
          _ = C * C' * ((n : ℝ) + 1) ^ (A + A') := by rw [pow_add]; ring
    _ = (n + 1 : ℕ) * (C * C' * ((n : ℝ) + 1) ^ (A + A')) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    _ = C * C' * ((n : ℝ) + 1) ^ (A + A' + 1) := by push_cast; ring

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `sa` using `(GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 τ`. Establish `sb` using `(GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).1 τ`. Unfold `qs`. Rewrite using `[tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm sa sb]`.

Use `congr 1`. Use function extensionality and compare the values at `n`. Unfold `mul`. Rewrite using `[Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `e : cexp (2 * π * Complex.I * (n : ℂ) * τ) = cexp (2 * π * Complex.I * (p.1 : ℂ) * τ) * cexp (2 * π * Complex.I * (p.2 : ℂ) * τ)`. Rewrite using `[← Complex.exp_add, ← hp]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qs_mul (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) :
    qs (mul a b) = fun τ => qs a τ * qs b τ := by
  funext τ
  have sa := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 τ
  have sb := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).1 τ
  unfold qs
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm sa sb]
  congr 1
  funext n
  unfold mul
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have e : cexp (2 * π * Complex.I * (n : ℂ) * τ) =
      cexp (2 * π * Complex.I * (p.1 : ℂ) * τ) * cexp (2 * π * Complex.I * (p.2 : ℂ) * τ) := by
    rw [← Complex.exp_add, ← hp]
    congr 1
    push_cast
    ring
  rw [e]
  ring

/- English proof (translation)
Use `⟨fun a b ha hb => ⟨polyB_mul a b ha hb, qs_mul a b ha hb⟩, ?_⟩` and prove the remaining obligations. Introduce `k k' L χ χ' a b ha hb`. Use `⟨polyB_mul a b ha.1 hb.1, ?_⟩` and prove the remaining obligations. Introduce `γ hγ τ`. Rewrite using `[qs_mul a b ha.1 hb.1]`.

Simplify using `only`. Rewrite using `[ha.2 γ hγ τ, hb.2 γ hγ τ, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_main : (∀ a b : ℕ → ℂ, PolyB a → PolyB b → PolyB (mul a b) ∧ qs (mul a b) = fun τ => qs a τ * qs b τ) ∧ ∀ (k k' L : ℕ) (χ χ' : ℤ → ℂ) (a b : ℕ → ℂ), MF k L χ a → MF k' L χ' b → MF (k + k') L (fun d => χ d * χ' d) (mul a b) := by
  refine ⟨fun a b ha hb => ⟨polyB_mul a b ha hb, qs_mul a b ha hb⟩, ?_⟩
  intro k k' L χ χ' a b ha hb
  refine ⟨polyB_mul a b ha.1 hb.1, ?_⟩
  intro γ hγ τ
  rw [qs_mul a b ha.1 hb.1]
  simp only
  rw [ha.2 γ hγ τ, hb.2 γ hγ τ, pow_add]
  ring

end GlobalTheory.EisM
