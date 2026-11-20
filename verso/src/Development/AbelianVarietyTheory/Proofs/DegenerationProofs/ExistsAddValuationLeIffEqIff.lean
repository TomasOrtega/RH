import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuation

namespace GlobalTheory.PadicVal

/- English proof (translation)
Introduce `p _ π h0 h1`. Establish `hL : Real.log ‖π‖ < 0` using `Real.log_neg h0 h1`. Take `⟨v, hv⟩` from `_root_.GlobalTheory.PadicVal.exists_addValuation π h0 h1`. Use `⟨v, fun c r => ?_, fun c r => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hc : c = 0`.

Simplify using `[hc, (Real.exp_pos _).le]`. Take `⟨q, hvq, hlog⟩` from `hv c hc`. Rewrite using `[hvq, WithTop.coe_le_coe, neg_mul, neg_neg, ← Real.log_le_iff_le_exp (norm_pos_iff.2 hc), hlog, mul_comm (Real.log ‖π‖), mul_le_mul_right_of_neg hL]`. Conclude with `Iff.rfl` after adjusting the coercions. Distinguish the cases in `hc : c = 0`.

Simplify using `[hc, (Real.exp_pos _).ne]`. Take `⟨q, hvq, hlog⟩` from `hv c hc`. Rewrite using `[hvq, WithTop.coe_inj, neg_mul, neg_neg]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`.

Rewrite using `[mul_comm, ← hlog, Real.exp_log (norm_pos_iff.2 hc)]`. Introduce `h`. Establish `h2` using `congrArg Real.log h`. Rewrite `h2` using `[Real.log_exp, hlog, mul_comm (Real.log ‖π‖)]`. Conclude with `Rat.cast_injective (mul_right_cancel₀ hL.ne h2)`.
-/
theorem _root_.GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff : ∀ (p : ℕ) [Fact p.Prime] (π : PadicAlgCl p),
    0 < ‖π‖ → ‖π‖ < 1 → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ),
      (∀ (c : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v c ↔
        ‖c‖ ≤ Real.exp (-(-Real.log ‖π‖ * r))) ∧
      ∀ (c : PadicAlgCl p) (r : ℚ), v c = (r : WithTop ℚ) ↔
        ‖c‖ = Real.exp (-(-Real.log ‖π‖ * r)) := by
  intro p _ π h0 h1
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PadicVal.exists_addValuation π h0 h1
  refine ⟨v, fun c r => ?_, fun c r => ?_⟩
  · by_cases hc : c = 0
    · simp [hc, (Real.exp_pos _).le]
    obtain ⟨q, hvq, hlog⟩ := hv c hc
    rw [hvq, WithTop.coe_le_coe, neg_mul, neg_neg,
      ← Real.log_le_iff_le_exp (norm_pos_iff.2 hc), hlog, mul_comm (Real.log ‖π‖),
      mul_le_mul_right_of_neg hL]
    exact_mod_cast Iff.rfl
  · by_cases hc : c = 0
    · simp [hc, (Real.exp_pos _).ne]
    obtain ⟨q, hvq, hlog⟩ := hv c hc
    rw [hvq, WithTop.coe_inj, neg_mul, neg_neg]
    constructor
    · rintro rfl
      rw [mul_comm, ← hlog, Real.exp_log (norm_pos_iff.2 hc)]
    · intro h
      have h2 := congrArg Real.log h
      rw [Real.log_exp, hlog, mul_comm (Real.log ‖π‖)] at h2
      exact Rat.cast_injective (mul_right_cancel₀ hL.ne h2)

end GlobalTheory.PadicVal
