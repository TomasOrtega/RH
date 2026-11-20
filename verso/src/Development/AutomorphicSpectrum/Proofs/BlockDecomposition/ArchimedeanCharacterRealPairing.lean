import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSInf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.JSPair

def dotL (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] Cinf E :=
  ∑ i : Fin k, (ContinuousLinearMap.mul ℝ (Cinf E)).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)

/- English proof (translation)
Simplify using `[dotL, ContinuousLinearMap.sum_apply]`.
-/
theorem dotL_apply {E : Type} [Field E] [NumberField E] {k : ℕ} (x z : Fin k → Cinf E) :
    dotL E k x z = ∑ i, x i * z i := by
  simp [dotL, ContinuousLinearMap.sum_apply]

/- English proof (translation)
Introduce `E _ _ _ k ψ h8 hψ`. Take `⟨l, hl⟩` from `h8 (InfinitePlace E) (GlobalTheory.CompanionTheory.JSInfStep.chiInf ψ) (hψ.cont.comp GlobalTheory.CompanionTheory.JSInfStep.continuous_sInf) (fun z => hψ.norm _)`. Set `β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ` to `(ContinuousLinearMap.compL ℝ (Fin k → Cinf E) (Cinf E) ℝ (-l)) ∘L dotL E k`. Establish `hβ : ∀ x z, β x z = -l (∑ i, x i * z i)` using `fun x z => by`. Simplify using `[β, dotL_apply]`.

Use `⟨β, fun y hy => ?_, fun x z => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `GlobalTheory.CompanionTheory.JSInfStep.chiInf_nondeg hψ (y i) fun w => ?_` and prove the remaining obligations. Establish `h0` using `hy (Pi.single i w)`. Rewrite `h0` using `[hβ]`.

Establish `e : ∑ j, (Pi.single i w : Fin k → Cinf E) j * y j = y i * w`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[Pi.single_eq_same, mul_comm]`. Introduce `j _ hj`. Rewrite using `[Pi.single_eq_of_ne hj, zero_mul]`.

Simplify using the standard rewrite rules. Rewrite `h0` using `[e]`. Establish `h1 : l (y i * w) = 0` using `neg_eq_zero.1 h0`. Rewrite using `[hl, h1]`. Simplify using the standard rewrite rules.

Use `hl (∑ i, x i * z i)` as an intermediate fact. Rewrite `this` using `[GlobalTheory.CompanionTheory.JSInfStep.chiInf_apply]`. Rewrite using `[this, hβ]`. Simplify using the standard rewrite rules.
-/
theorem exists_pairing : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  intro E _ _ _ k ψ h8 hψ
  obtain ⟨l, hl⟩ := h8 (InfinitePlace E) (GlobalTheory.CompanionTheory.JSInfStep.chiInf ψ)
    (hψ.cont.comp GlobalTheory.CompanionTheory.JSInfStep.continuous_sInf) (fun z => hψ.norm _)
  let β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (Fin k → Cinf E) (Cinf E) ℝ (-l)) ∘L dotL E k
  have hβ : ∀ x z, β x z = -l (∑ i, x i * z i) := fun x z => by
    simp [β, dotL_apply]
  refine ⟨β, fun y hy => ?_, fun x z => ?_⟩
  · funext i
    refine GlobalTheory.CompanionTheory.JSInfStep.chiInf_nondeg hψ (y i) fun w => ?_
    have h0 := hy (Pi.single i w)
    rw [hβ] at h0
    have e : ∑ j, (Pi.single i w : Fin k → Cinf E) j * y j = y i * w := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_comm]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · simp
    rw [e] at h0
    have h1 : l (y i * w) = 0 := neg_eq_zero.1 h0
    rw [hl, h1]
    simp
  · have := hl (∑ i, x i * z i)
    rw [GlobalTheory.CompanionTheory.JSInfStep.chiInf_apply] at this
    rw [this, hβ]
    simp

end GlobalTheory.CompanionTheory.JSPair

end
