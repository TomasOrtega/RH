import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisSide

namespace SchrodingerSchwartzBruhat
section
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrSB

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem eq_one_of_pow_two_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ (2 ^ n) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PositiveFormRecursion.main
  | exact _root_.GlobalTheory.PositiveFormRecursion.main
  | (apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveFormRecursion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveFormRecursion.main ..)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLocallyConstant_addChar (ψ : AddChar k ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hb := IsValuativeTopology.hasBasis_nhds_zero' k
  have hU : ψ ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : k) :=
    hψ.continuousAt.preimage_mem_nhds (by
      rw [AddChar.map_zero_eq_one]; exact Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨γ, hγ, hsub⟩ := hb.mem_iff.mp hU
  have hker : ∀ x, ValuativeRel.valuation k x < γ → ψ x = 1 := by
    intro x hx
    have h2 : ∀ n : ℕ, ValuativeRel.valuation k ((2 ^ n : ℕ) • x) < γ := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        have e : (2 ^ (n + 1) : ℕ) • x = (2 ^ n : ℕ) • x + (2 ^ n : ℕ) • x := by
          rw [pow_succ, mul_two, add_smul]
        rw [e]
        exact Valuation.map_add_lt _ ih ih
    apply eq_one_of_pow_two_pow_near
    intro n
    have h3 : ψ ((2 ^ n : ℕ) • x) ∈ Metric.ball (1 : ℂ) (1 / 2) := hsub (h2 n)
    rw [AddChar.map_nsmul_eq_pow, Metric.mem_ball, dist_eq_norm] at h3
    exact h3
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hn : {y : k | ValuativeRel.valuation k (y - x) < γ} ∈ nhds x := by
    have hc : ContinuousAt (fun y : k => y - x) x := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hb.mem_of_mem hγ)
  filter_upwards [hn] with y hy
  have e : ψ y = ψ (y - x) * ψ x := by
    rw [← AddChar.map_add_eq_mul]; simp
  rw [e, hker _ hy, one_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem schr_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  intro k _ _ _ _ _ ψ0 hψ κ _ w φ hφ
  obtain ⟨h1, h2⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hl := isLocallyConstant_addChar ψ0 hψ
  have hcont : Continuous fun x : κ → k => x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2) := by
    refine Continuous.add ?_ continuous_const
    exact continuous_id.dotProduct continuous_const
  have hs : HasCompactSupport fun x : κ → k => φ (x + w.1) :=
    h2.comp_homeomorph (Homeomorph.addRight w.1)
  have hf : IsLocallyConstant fun x : κ → k => φ (x + w.1) :=
    h1.comp_continuous (continuous_add_const w.1)
  refine ⟨?_, ?_⟩
  · exact (hl.comp_continuous hcont).mul hf
  · exact HasCompactSupport.mul_left hs

end GlobalTheory.CompanionTheory.SchrSB

end

end SchrodingerSchwartzBruhat
section

open MeasureTheory Matrix

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | exact SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | (intros; apply SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB <;> assumption)

end
