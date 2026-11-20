import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralTupleLatticeCountBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCmFieldEqTwoMulTotallyRealSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorBoundMatrixMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledEmbeddingNormBoundHostFieldStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Introduce `D κ _ _ m n T S hST L hL`. Take `⟨M, hM0, hM⟩` from `GlobalTheory.T.exists_denominator_bound_matrix_mul D.host.E κ (Fin m) T`. Take `⟨N, C₁, hC₁, hcount⟩` from `GlobalTheory.T.weighted_integral_tuple_lattice_count_bound D (κ × Fin n) (M * L) (Nat.mul_pos hM0 hL)`. Take `⟨C₂, hC₂, hnorm⟩` from `GlobalTheory.T.exists_scaledEmbeddingNorm_bound_hostField D κ m n T`. Use `⟨N, C₂ ^ N * C₁, mul_nonneg (pow_nonneg (by linarith) _) hC₁, ?_⟩` and prove the remaining obligations.

Introduce `s hs B hB`. Use `set e : Matrix (Fin m) (Fin n) D.host.E → (κ × Fin n → D.host.E) := fun ξ p => (T * ξ) p.1 p.2 with he`. Establish `he_inj : Function.Injective e`. Introduce `ξ ξ' h`. Establish `h' : T * ξ = T * ξ'` using `Matrix.ext fun k j => congrFun h (k, j)`.

Combine the equalities or inequalities in the displayed calculation. Use `set s' : κ × Fin n → ℝ := fun p => s p.1 with hs'`. Establish `hs'pos : ∀ p, 0 < s' p` using `fun p => hs p.1`. Establish `hc` using `hcount s' hs'pos`. Use `set G : (κ × Fin n → D.host.E) → ℝ≥0∞ := {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)}.indicator (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s' k) ^ N)⁻¹)) with hG`.

Establish `hterm : ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C₂ ^ N) * G (e ξ)`. Introduce `ξ`. Distinguish the cases in `hξ : ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)`. Rewrite using `[Set.indicator_of_mem (by exact hξ : ξ ∈ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]`. Establish `hmem : e ξ ∈ {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)}`.

Introduce `p`. Use `hM L (fun i => ξ i p.2) (fun i => hξ i p.2) p.1` as an intermediate fact. Simplify `this` using `[he, Matrix.mul_apply]`. Rewrite using `[hG, Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `hA` using `hnorm s hs B hB ξ`. Use `set W := ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ with hW`. Use `set A := ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 with hAdef`. Establish `hW0 : 0 ≤ W` using `by positivity`. Establish `hA0 : 0 ≤ A` using `Finset.sum_nonneg (fun p _ => div_nonneg (by positivity) (hs p.1).le)`.

Establish `h1 : 1 + A ≤ C₂ * (1 + W)` using `by nlinarith`. Establish `hp1 : 0 < (1 + A) ^ N` using `by positivity`. Establish `hp2 : 0 < (1 + W) ^ N` using `by positivity`. Establish `h2 : (1 + A) ^ N ≤ C₂ ^ N * (1 + W) ^ N`. Rewrite using `[← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 N`.

Rewrite using `[← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp2 hp1]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Set.indicator_of_notMem (by exact hξ : ξ ∉ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]`. Conclude with `bot_le`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← ENNReal.ofReal_mul (pow_nonneg (by linarith) _), mul_assoc]`. Use `congr 2`. Rewrite using `[Fintype.prod_prod_type]`. Use `congr 1`. Use `Finset.prod_congr rfl (fun k _ => ?_)` and prove the remaining obligations.

Simplify using `only [hs', Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← pow_mul, GlobalTheory.T.finrank_cmField_eq_two_mul_totallyRealSubfield D]`. Put the polynomial expressions in normal form.
-/
theorem lattice_count_diag_mul : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E) (S : Matrix (Fin m) κ D.host.E), S * T = 1 → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D κ _ _ m n T S hST L hL
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.exists_denominator_bound_matrix_mul D.host.E κ (Fin m) T
  obtain ⟨N, C₁, hC₁, hcount⟩ := GlobalTheory.T.weighted_integral_tuple_lattice_count_bound D (κ × Fin n) (M * L) (Nat.mul_pos hM0 hL)
  obtain ⟨C₂, hC₂, hnorm⟩ := GlobalTheory.T.exists_scaledEmbeddingNorm_bound_hostField D κ m n T
  refine ⟨N, C₂ ^ N * C₁, mul_nonneg (pow_nonneg (by linarith) _) hC₁, ?_⟩
  intro s hs B hB
  set e : Matrix (Fin m) (Fin n) D.host.E → (κ × Fin n → D.host.E) := fun ξ p => (T * ξ) p.1 p.2 with he
  have he_inj : Function.Injective e := by
    intro ξ ξ' h
    have h' : T * ξ = T * ξ' := Matrix.ext fun k j => congrFun h (k, j)
    calc ξ = S * T * ξ := by rw [hST, Matrix.one_mul]
      _ = S * T * ξ' := by rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc]
      _ = ξ' := by rw [hST, Matrix.one_mul]
  set s' : κ × Fin n → ℝ := fun p => s p.1 with hs'
  have hs'pos : ∀ p, 0 < s' p := fun p => hs p.1
  have hc := hcount s' hs'pos
  set G : (κ × Fin n → D.host.E) → ℝ≥0∞ := {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)}.indicator (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s' k) ^ N)⁻¹)) with hG
  have hterm : ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C₂ ^ N) * G (e ξ) := by
    intro ξ
    by_cases hξ : ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)
    · rw [Set.indicator_of_mem (by exact hξ : ξ ∈ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]
      have hmem : e ξ ∈ {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)} := by
        intro p
        have := hM L (fun i => ξ i p.2) (fun i => hξ i p.2) p.1
        simpa [he, Matrix.mul_apply] using this
      rw [hG, Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
      apply ENNReal.ofReal_le_ofReal
      have hA := hnorm s hs B hB ξ
      set W := ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ with hW
      set A := ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 with hAdef
      have hW0 : 0 ≤ W := by positivity
      have hA0 : 0 ≤ A := Finset.sum_nonneg (fun p _ => div_nonneg (by positivity) (hs p.1).le)
      have h1 : 1 + A ≤ C₂ * (1 + W) := by nlinarith
      have hp1 : 0 < (1 + A) ^ N := by positivity
      have hp2 : 0 < (1 + W) ^ N := by positivity
      have h2 : (1 + A) ^ N ≤ C₂ ^ N * (1 + W) ^ N := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 N
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp2 hp1]
      linarith
    · rw [Set.indicator_of_notMem (by exact hξ : ξ ∉ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]
      exact bot_le
  calc _ ≤ ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ENNReal.ofReal (C₂ ^ N) * G (e ξ) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C₂ ^ N) * ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, G (e ξ) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (C₂ ^ N) * ∑' η, G η := by gcongr; exact ENNReal.tsum_comp_le_tsum_of_injective he_inj G
    _ ≤ ENNReal.ofReal (C₂ ^ N) * ENNReal.ofReal (C₁ * ∏ p, max 1 (s' p) ^ Module.finrank ℚ D.host.E) := by gcongr
    _ = ENNReal.ofReal (C₂ ^ N * C₁ * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (by linarith) _), mul_assoc]
      congr 2
      rw [Fintype.prod_prod_type]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      simp only [hs', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_mul, GlobalTheory.T.finrank_cmField_eq_two_mul_totallyRealSubfield D]
      ring_nf

end GlobalTheory
