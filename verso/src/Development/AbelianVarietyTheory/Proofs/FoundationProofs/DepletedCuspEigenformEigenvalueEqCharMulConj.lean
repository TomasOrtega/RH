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
Use function extensionality and compare the values at `τ`. Unfold `qs`. Rewrite using `[← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `n`.

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
Unfold `pet`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pet_smul_right (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ h (fun τ => c * f τ) = c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  ring

/- English proof (translation)
Unfold `pet`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Simplify using `only [map_mul]`.

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
Introduce `k N q χ g hk hN hg hq hqN`. Take `⟨ρ, hρ⟩` from `GlobalTheory.T.exists_gammaZeroPartitionWeight N hN`. Establish `hT : To k (ch χ q) q g = fun n => g q * g n` using `hg.eig q hq hqN`. Establish `hadj` using `GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k N N q χ ρ g g hk hN dvd_rfl hq hqN hρ hg.cf hg.cf.1`. Establish `hne : g ≠ 0`.

Introduce `h0`. Use `hg.one` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Establish `hP` using `GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm k N N χ ρ g hk hN dvd_rfl hρ hg.cf hne`.

Rewrite `hadj` using `[hT, qs_smul, pet_smul_right, pet_smul_left]`. Conclude with `mul_right_cancel₀ hP (hadj.trans (by ring) : g q * pet k ρ (qs g) (qs g) = ch χ q * conj (g q) * pet k ρ (qs g) (qs g))`.
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
