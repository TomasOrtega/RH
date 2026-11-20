import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

/- English proof (translation)
Introduce `d hd`. Establish `h4 : 4 ∣ d + 1` using `by omega`. Take `⟨k, hk⟩` from `h4`. Establish `hk' : (d + 1) / 4 = k` using `by omega`. Rewrite using `[hk']`.

Establish `hdk : (d : ℂ) = 4 * k - 1`. Establish `: ((d + 1 : ℕ) : ℂ) = ((4 * k : ℕ) : ℂ)` using `by rw [hk]`. Move the coercions through the operations in `at this`. Take the linear combination `this`. Establish `hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ)`.

Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Unfold `omegaK`. Establish `hI : Complex.I ^ 2 = -1` using `Complex.I_sq`. Take the linear combination `(-(1:ℂ)/4) * hs + ((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4 * hI - (1/4 : ℂ) * hdk`.
-/
theorem omegaK_quadratic : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  intro d hd
  have h4 : 4 ∣ d + 1 := by omega
  obtain ⟨k, hk⟩ := h4
  have hk' : (d + 1) / 4 = k := by omega
  rw [hk']
  have hdk : (d : ℂ) = 4 * k - 1 := by
    have : ((d + 1 : ℕ) : ℂ) = ((4 * k : ℕ) : ℂ) := by rw [hk]
    push_cast at this
    linear_combination this
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  unfold omegaK
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(1:ℂ)/4) * hs + ((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4 * hI - (1/4 : ℂ) * hdk
end GlobalTheory
