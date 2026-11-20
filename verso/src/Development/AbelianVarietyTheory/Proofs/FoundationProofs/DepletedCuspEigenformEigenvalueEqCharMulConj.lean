import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeTAdjointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralSelfNeZeroCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeightStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisMReal

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (fun n => c * a n) = fun τ => c * qs a τ := by
  funext τ
  unfold qs
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pet_smul_right (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ h (fun τ => c * f τ) = c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pet_smul_left (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ (fun τ => c * h τ) f = conj c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [map_mul]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem eig_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g →
    q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  intro k N q χ g hk hN hg hq hqN
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight N hN
  have hT : To k (ch χ q) q g = fun n => g q * g n := hg.eig q hq hqN
  have hadj := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k N N q χ ρ g g hk hN dvd_rfl hq hqN hρ hg.cf hg.cf.1
  have hne : g ≠ 0 := by
    intro h0
    have := hg.one
    rw [h0] at this
    simp at this
  have hP := GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm k N N χ ρ g hk hN dvd_rfl hρ hg.cf hne
  rw [hT, qs_smul, pet_smul_right, pet_smul_left] at hadj
  exact mul_right_cancel₀ hP (hadj.trans (by ring) : g q * pet k ρ (qs g) (qs g) = ch χ q * conj (g q) * pet k ρ (qs g) (qs g))

end GlobalTheory.EisMReal
