import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem untilt_zero : (0 : Fl l).untilt = 0 :=
  Perfection.teichmuller_zero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Put the expressions in a common number system so they can be compared. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem sh_laws : ∀ (l : ℕ) [Fact l.Prime], sh (1 : Fl l) = 1 ∧ sh (0 : Fl l) = 0 ∧
    (∀ x y : Fl l, sh (x * y) = sh x * sh y) ∧ (∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n) ∧
    (∀ x : Fl l, ‖sh x‖ ≤ 1) ∧ (∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∃ x : Fl l, sh x = c) ∧
    (∀ x y : Fl l, ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ x : Fl l, ‖sh (-x)‖ = ‖sh x‖) := by
  intro l _
  have hmul : ∀ x y : Fl l, sh (x * y) = sh x * sh y := fun x y => by
    simp only [sh, map_mul]; rfl
  have hpow : ∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n := fun x n => by
    simp only [sh, map_pow]; norm_cast
  refine ⟨by simp [sh], by simp [sh, untilt_zero], hmul, hpow, fun x => (GlobalTheory.RingBasics.mem_OC _).1 (x.untilt).2,
    fun c hc => ?_, fun x y => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l ⟨c, (GlobalTheory.RingBasics.mem_OC c).2 hc⟩
    exact ⟨x, by simp [sh, hx]⟩
  · have hm : (x + y).untilt - x.untilt - y.untilt ∈ Ideal.span {(l : OC l)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
        PreTilt.mk_untilt_eq_coeff_zero, PreTilt.mk_untilt_eq_coeff_zero, map_add]
      ring
    have := (GlobalTheory.RingBasics.mem_span_pow_OC 1 _).1 (by rw [pow_one]; exact hm)
    simpa [sh] using this
  · have h2 : sh (-x) ^ 2 = sh x ^ 2 := by rw [← hpow, ← hpow, neg_sq]
    have h3 : ‖sh (-x)‖ ^ 2 = ‖sh x‖ ^ 2 := by rw [← norm_pow, ← norm_pow, h2]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

end GlobalTheory.PSer.Laws
