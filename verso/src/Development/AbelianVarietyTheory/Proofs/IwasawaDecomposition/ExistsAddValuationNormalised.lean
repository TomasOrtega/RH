import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuationLeIffEqIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.MemLoc.exists_addValuation_normalised : ∀ (l : ℕ) [Fact l.Prime], ∀ LL : _root_.Formalism.BasicNotions.Loc.FinExt l,
    ∃ v : AddValuation ↥LL.1 (WithTop ℚ), v (l : ↥LL.1) = 1 ∧
      ∀ x : ↥LL.1, 0 ≤ v x ↔ x ∈ _root_.Formalism.BasicNotions.Loc.OL LL := by
  intro l _ LL
  have hprime : l.Prime := Fact.out
  have hnorm : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hl0 : 0 < ‖(l : PadicAlgCl l)‖ := by
    rw [hnorm]
    exact inv_pos.2 (Nat.cast_pos.2 hprime.pos)
  have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [hnorm]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hprime.one_lt)
  have hL : Real.log ‖(l : PadicAlgCl l)‖ < 0 := Real.log_neg hl0 hl1
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PadicVal.exists_addValuation (l : PadicAlgCl l) hl0 hl1
  refine ⟨v.comap LL.1.val.toRingHom, ?_, fun x => ?_⟩
  · have hcast : ((l : ↥LL.1) : PadicAlgCl l) = l := by simp
    show v ((l : ↥LL.1) : PadicAlgCl l) = 1
    rw [hcast]
    obtain ⟨q, hvq, hlog⟩ := hv _ (norm_pos_iff.1 hl0)
    have hq : q = 1 := Rat.cast_injective (by
      have := mul_right_cancel₀ hL.ne (hlog.symm.trans (one_mul _).symm)
      simpa using this)
    rw [hvq, hq]
    rfl
  · show 0 ≤ v (x : PadicAlgCl l) ↔ x ∈ integralClosure ℤ_[l] LL.1
    rw [_root_.GlobalTheory.mem_integralClosure_padicInt_iff]
    by_cases hx : (x : PadicAlgCl l) = 0
    · simp [hx]
    obtain ⟨q, hvq, hlog⟩ := hv _ hx
    rw [hvq, WithTop.coe_nonneg, ← Real.log_nonpos_iff (norm_nonneg _), hlog]
    constructor
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast h) hL.le
    · intro h
      have h' : (0 : ℝ) ≤ q := (mul_le_mul_right_of_neg hL).1 (by simpa using h)
      exact_mod_cast h'

end GlobalTheory.MemLoc
