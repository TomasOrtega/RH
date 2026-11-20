import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.MpDiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem mem_Bl_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  obtain ⟨ρ, hρ, H⟩ := GlobalTheory.T.arith_global_maximum_principle_off_divisor k X p D hX P s hs hs0 δ hδ
  refine ⟨max 0 (-Real.log ρ), le_max_left _ _, fun N m f hf hfs => ?_⟩
  set C : ℝ := max 0 (-Real.log ρ) with hC
  have key := H N f (2 * Real.exp (C * m)) hf (fun σ y hy => ?_)
  · have e : Real.exp (δ * N) * (2 * Real.exp (C * m)) = 2 * Real.exp (δ * N + C * m) := by
      rw [Real.exp_add]; ring
    rwa [e] at key
  · obtain ⟨hp1, hp2⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs m
    have hm := (GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 _ _ f (s ^ m) hf hp1).2 σ y
    rw [hp2 σ y] at hm
    simp only [mul_zero, add_zero, mul_one, zero_add] at hm
    have h2 := hfs.2 σ y
    rw [hm] at h2
    have hn : 0 ≤ P.nu N 0 σ y f := by unfold Pair.nu; positivity
    have h1 : 1 ≤ Real.exp C * P.nu 0 1 σ y s := by
      have : Real.exp (-Real.log ρ) ≤ Real.exp C := Real.exp_le_exp.2 (le_max_right _ _)
      rw [Real.exp_neg, Real.exp_log hρ] at this
      calc (1 : ℝ) = ρ⁻¹ * ρ := (inv_mul_cancel₀ hρ.ne').symm
        _ ≤ Real.exp C * P.nu 0 1 σ y s :=
          mul_le_mul this hy hρ.le (Real.exp_pos _).le
    have h3 : 1 ≤ Real.exp (C * m) * P.nu 0 1 σ y s ^ m := by
      rw [mul_comm C, Real.exp_nat_mul, ← mul_pow]
      exact one_le_pow₀ h1
    calc P.nu N 0 σ y f ≤ P.nu N 0 σ y f * (Real.exp (C * m) * P.nu 0 1 σ y s ^ m) :=
          le_mul_of_one_le_right hn h3
      _ = Real.exp (C * m) * (P.nu N 0 σ y f * P.nu 0 1 σ y s ^ m) := by ring
      _ ≤ Real.exp (C * m) * 2 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = 2 * Real.exp (C * m) := mul_comm _ _

end GlobalTheory.VolBr.MpDiv
