import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FinrankCompactUnitaryPolyFunDegLELeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralNormSqReproducingKernelLeFinrankStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteRealSpanningCompactLieAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryPolynomialSpectralGapStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirInverseTopDegreeBoundStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirPowPairingModerateGrowthBouStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KFourier
open MeasureTheory

/- English proof (translation)
Use `show 0 ≤ ∑ i, ∑ j, ‖y i j‖ ^ 2`. Conclude with `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity`.
-/
theorem hs_nonneg' {n : ℕ} (y : Mx n) : 0 ≤ hs y := by
  show 0 ≤ ∑ i, ∑ j, ‖y i j‖ ^ 2
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/- English proof (translation)
Introduce `n ε N F hD hG hC e he u hu`. Take `⟨r, X, hX, hsp⟩` from `GlobalTheory.T.exists_finite_real_spanning_compactLieAlgebra ε`. Take `⟨c, α, hc, hα, hgap⟩` from `GlobalTheory.T.compactUnitary_polynomial_spectral_gap ε X hX hsp`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : ∃ M : ℕ, (n : ℝ) ^ 2 + 2 < α * M := by`. Take `⟨M, hM⟩` from `exists_nat_gt (((n : ℝ) ^ 2 + 2) / α)`.

Conclude with `⟨M, by rw [div_lt_iff₀ hα] at hM; linarith⟩`. Take `⟨C0, hC0⟩` from `GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX 0 u hu`. Take `⟨C, hCM⟩` from `GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX M u hu`. Establish `hlnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ((c * x ^ α) ^ M)⁻¹` using `fun x hx => inv_nonneg.mpr (pow_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hx _)) _)`. Set `B : ℕ → ℝ` to `fun i => |C| * ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)`.

Use `⟨fun i => if i = 0 then |C0| * Real.sqrt (Module.finrank ℂ (polyV ε 0)) else B i, ?_, ?_⟩` and prove the remaining obligations. Use `(summable_nat_add_iff 1).mp ?_` and prove the remaining obligations. Establish `hp : (n : ℝ) ^ 2 - α * M < -1` using `by linarith`. Establish `hsm : Summable (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ ((n : ℝ) ^ 2 - α * M))` using `(summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)`. Use `Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hsm.mul_left (|C| * (c ^ M)⁻¹ * 2 ^ (n ^ 2)))` and prove the remaining obligations.

Simplify using `only [Nat.add_one_ne_zero, if_false, B]`. Conclude with `mul_nonneg (mul_nonneg (abs_nonneg _) (hlnn _ (Nat.cast_nonneg _))) (by positivity)`. Simplify using `only [Nat.add_one_ne_zero, if_false, B] set x : ℝ := ((i + 1 : ℕ) : ℝ) with hx`. Establish `hx1 : 1 ≤ x` using `by simp [hx]`. Establish `hx0 : 0 < x` using `by linarith`.

Establish `e1 : (c * x ^ α) ^ M = c ^ M * x ^ (α * M)`. Rewrite using `[mul_pow, ← Real.rpow_mul_natCast hx0.le]`. Establish `e2 : (x + 1) ^ (n ^ 2) ≤ 2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2)`. Rewrite using `[show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (by linarith) (by linarith) _`.

Establish `e3 : x ^ ((n : ℝ) ^ 2 - α * M) = x ^ ((n : ℝ) ^ 2) * (x ^ (α * M))⁻¹`. Rewrite using `[Real.rpow_sub hx0, div_eq_mul_inv]`. Rewrite using `[e1, e3, mul_inv]`. Establish `h0 : 0 ≤ |C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹` using `mul_nonneg (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (pow_nonneg hc.le _))) (inv_nonneg.mpr (Real.rpow_nonneg hx0.le _))`. Combine the equalities or inequalities in the displayed calculation.

Introduce `i y hy`. Establish `hy0 : 0 ≤ (1 + hs y) ^ N` using `pow_nonneg (by linarith [hs_nonneg' y]) _`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Simplify using `only [if_true]`. Establish `h` using `hC0 0 (e 0) (he 0).1 y hy`.

Simplify using `only [Function.iterate_zero, id] at h`. Establish `hk` using `GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε 0 (e 0) (he 0)`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_le_sqrt hk) (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg _) hy0)` to reduce the goal to its premises. Use `_ = _ := by ring`.

Establish `hi0 : i ≠ 0` using `hi.ne'`. Simplify using `only [hi0, if_false]`. Establish `hl : 0 < c * (i : ℝ) ^ α` using `mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hi) _)`. Take `⟨s, hsP, hse, hsn⟩` from `GlobalTheory.T.compactUnitaryCasimir_inverse_topDegree_bound ε X hX i (c * (i : ℝ) ^ α) hl (fun p hp hq => hgap i hi p hp hq) M (e i) (he i).1 (fun q hq => by rw [← (he i).2.1 q hq]; congr 1; funext k; ring)`. Establish `h` using `hCM i s hsP y hy`.

Rewrite `h` using `[hse]`. Establish `hk` using `GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε i (e i) (he i)`. Establish `hd : (Module.finrank ℂ (polyV ε i) : ℝ) ≤ ((i : ℝ) + 1) ^ (2 * n ^ 2)`. Conclude with `GlobalTheory.T.finrank_compactUnitaryPolyFunDegLE_le ε i` after adjusting the coercions. Establish `hsq : Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) ≤ ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)`.

Establish `h1 : ∫ k, ‖s k‖ ^ 2 ∂(muK ε) ≤ (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem kFourier_coeff_decay : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ e : ℕ → KG ε → ℂ, (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∃ b : ℕ → ℝ, Summable b ∧ ∀ i, ∀ y ∈ UJset ε, ‖∫ k, e i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N := by
  intro n ε N F hD hG hC e he u hu
  obtain ⟨r, X, hX, hsp⟩ := GlobalTheory.T.exists_finite_real_spanning_compactLieAlgebra ε
  obtain ⟨c, α, hc, hα, hgap⟩ := GlobalTheory.T.compactUnitary_polynomial_spectral_gap ε X hX hsp
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (n : ℝ) ^ 2 + 2 < α * M := by
    obtain ⟨M, hM⟩ := exists_nat_gt (((n : ℝ) ^ 2 + 2) / α)
    exact ⟨M, by rw [div_lt_iff₀ hα] at hM; linarith⟩
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX 0 u hu
  obtain ⟨C, hCM⟩ := GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX M u hu
  have hlnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ((c * x ^ α) ^ M)⁻¹ := fun x hx =>
    inv_nonneg.mpr (pow_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hx _)) _)
  let B : ℕ → ℝ := fun i => |C| * ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)
  refine ⟨fun i => if i = 0 then |C0| * Real.sqrt (Module.finrank ℂ (polyV ε 0)) else B i, ?_, ?_⟩
  · refine (summable_nat_add_iff 1).mp ?_
    have hp : (n : ℝ) ^ 2 - α * M < -1 := by linarith
    have hsm : Summable (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ ((n : ℝ) ^ 2 - α * M)) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hsm.mul_left (|C| * (c ^ M)⁻¹ * 2 ^ (n ^ 2)))
    · simp only [Nat.add_one_ne_zero, if_false, B]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (hlnn _ (Nat.cast_nonneg _))) (by positivity)
    · simp only [Nat.add_one_ne_zero, if_false, B]
      set x : ℝ := ((i + 1 : ℕ) : ℝ) with hx
      have hx1 : 1 ≤ x := by simp [hx]
      have hx0 : 0 < x := by linarith
      have e1 : (c * x ^ α) ^ M = c ^ M * x ^ (α * M) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
      have e2 : (x + 1) ^ (n ^ 2) ≤ 2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2) := by
        rw [show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith) _
      have e3 : x ^ ((n : ℝ) ^ 2 - α * M) = x ^ ((n : ℝ) ^ 2) * (x ^ (α * M))⁻¹ := by
        rw [Real.rpow_sub hx0, div_eq_mul_inv]
      rw [e1, e3, mul_inv]
      have h0 : 0 ≤ |C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹ :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (pow_nonneg hc.le _)))
          (inv_nonneg.mpr (Real.rpow_nonneg hx0.le _))
      calc |C| * ((c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (x + 1) ^ (n ^ 2)
          = (|C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (x + 1) ^ (n ^ 2) := by ring
        _ ≤ (|C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left e2 h0
        _ = _ := by ring
  · intro i y hy
    have hy0 : 0 ≤ (1 + hs y) ^ N := pow_nonneg (by linarith [hs_nonneg' y]) _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [if_true]
      have h := hC0 0 (e 0) (he 0).1 y hy
      simp only [Function.iterate_zero, id] at h
      have hk := GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε 0 (e 0) (he 0)
      calc _ ≤ C0 * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖e 0 k‖ ^ 2 ∂(muK ε)) := h
        _ ≤ |C0| * (1 + hs y) ^ N * Real.sqrt (Module.finrank ℂ (polyV ε 0)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_le_sqrt hk)
              (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg _) hy0)
        _ = _ := by ring
    · have hi0 : i ≠ 0 := hi.ne'
      simp only [hi0, if_false]
      have hl : 0 < c * (i : ℝ) ^ α := mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hi) _)
      obtain ⟨s, hsP, hse, hsn⟩ := GlobalTheory.T.compactUnitaryCasimir_inverse_topDegree_bound ε X hX i (c * (i : ℝ) ^ α) hl
        (fun p hp hq => hgap i hi p hp hq) M (e i) (he i).1
        (fun q hq => by rw [← (he i).2.1 q hq]; congr 1; funext k; ring)
      have h := hCM i s hsP y hy
      rw [hse] at h
      have hk := GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε i (e i) (he i)
      have hd : (Module.finrank ℂ (polyV ε i) : ℝ) ≤ ((i : ℝ) + 1) ^ (2 * n ^ 2) := by
        exact_mod_cast GlobalTheory.T.finrank_compactUnitaryPolyFunDegLE_le ε i
      have hsq : Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) ≤
          ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2) := by
        have h1 : ∫ k, ‖s k‖ ^ 2 ∂(muK ε) ≤ (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2 := by
          calc _ ≤ ((c * (i : ℝ) ^ α) ^ (2 * M))⁻¹ * ∫ k, ‖e i k‖ ^ 2 ∂(muK ε) := hsn
            _ ≤ ((c * (i : ℝ) ^ α) ^ (2 * M))⁻¹ * (((i : ℝ) + 1) ^ (2 * n ^ 2)) :=
                mul_le_mul_of_nonneg_left (hk.trans hd) (inv_nonneg.mpr (pow_nonneg hl.le _))
            _ = _ := by rw [mul_pow ((c * (i : ℝ) ^ α) ^ M)⁻¹, inv_pow, ← pow_mul, ← pow_mul, mul_comm M 2, mul_comm (n ^ 2) 2]
        calc _ ≤ Real.sqrt ((((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2) :=
              Real.sqrt_le_sqrt h1
          _ = _ := Real.sqrt_sq (mul_nonneg (hlnn _ (Nat.cast_nonneg _)) (by positivity))
      calc _ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) := h
        _ ≤ |C| * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_nonneg _)
        _ ≤ |C| * (1 + hs y) ^ N * (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg (abs_nonneg _) hy0)
        _ = _ := by simp only [B]; ring

end GlobalTheory.KFourier
end
