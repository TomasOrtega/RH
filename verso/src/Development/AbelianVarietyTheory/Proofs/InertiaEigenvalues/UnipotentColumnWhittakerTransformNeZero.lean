import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLastStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

/- English proof (translation)
Introduce `E _ _ a ψ hψ m f hma hG hf`. Choose the witnesses or unpack the hypotheses as in `⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hf (funext h)`.

Establish `hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀))` using `per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀`. Establish `hΦ0 : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) ≠ 0`. Introduce `h`. Establish `h1` using `congrFun h 0`. Simplify using `only [Pi.zero_apply] at h1`.

Apply `hg₀` to reduce the goal to its premises. Establish `e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1` using `posU_zero _`. Rewrite `h1` using `[e, one_mul]`. Conclude with `h1`. Choose the witnesses or unpack the hypotheses as in `⟨ξ, hξ⟩ : ∃ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, coefF ψ (m + 1) ξ f g₀ ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hΦ0 (GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer h)`. Establish `hξ0 : ξ ≠ 0`. Introduce and unpack `rfl`.

Apply `hξ` to reduce the goal to its premises. Establish `hv` using `hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀`. Establish `e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1`. Introduce `x`. Simplify using `[dot]`.

Simplify using `only [coefF, e, one_mul]`. Conclude with `hv`. Take `⟨γ, hγ, hγξ⟩` from `GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0`. Introduce `h`. Apply `hξ` to reduce the goal to its premises.

Establish `h1` using `congrFun h (ratGL E a γ * g₀)`. Simplify using `only [Pi.zero_apply, colT] at h1`. Rewrite `h1` using `[GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀]`. Establish `e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ`. Use function extensionality and compare the values at `hγξ`.

Rewrite `h1` using `[e]`. Conclude with `h1`.
-/
theorem colT_ne_zero_of_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → f ≠ 0 → colT ψ (m + 1) f ≠ 0 := by
  intro E _ _ a ψ hψ m f hma hG hf
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (funext h)
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ0 : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp only [Pi.zero_apply] at h1
    apply hg₀
    have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
    rw [e, one_mul] at h1
    exact h1
  obtain ⟨ξ, hξ⟩ : ∃ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, coefF ψ (m + 1) ξ f g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ0 (GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer h)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hξ
    have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
    have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
      intro x
      simp [dot]
    simp only [coefF, e, one_mul]
    exact hv
  obtain ⟨γ, hγ, hγξ⟩ := GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
  intro h
  apply hξ
  have h1 := congrFun h (ratGL E a γ * g₀)
  simp only [Pi.zero_apply, colT] at h1
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
  have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ :=
    funext hγξ
  rw [e] at h1
  exact h1

end GlobalTheory.CuspGeneric
