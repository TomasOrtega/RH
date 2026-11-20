import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisSide

namespace SchrodingerSchwartzBruhat
section
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrSB

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PositiveFormRecursion.main`. Consider the case `exact _root_.GlobalTheory.PositiveFormRecursion.main`. Consider the case `(apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PositiveFormRecursion.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PositiveFormRecursion.main ..)`.
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
Establish `hb` using `IsValuativeTopology.hasBasis_nhds_zero' k`. Establish `hU : ψ ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : k)` using `hψ.continuousAt.preimage_mem_nhds (by`. Rewrite using `[AddChar.map_zero_eq_one]; exact Metric.ball_mem_nhds _ (by norm_num))`. Take `⟨γ, hγ, hsub⟩` from `hb.mem_iff.mp hU`. Establish `hker : ∀ x, ValuativeRel.valuation k x < γ → ψ x = 1`.

Introduce `x hx`. Establish `h2 : ∀ n : ℕ, ValuativeRel.valuation k ((2 ^ n : ℕ) • x) < γ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hx`.

Consider the case `succ n ih`. Establish `e : (2 ^ (n + 1) : ℕ) • x = (2 ^ n : ℕ) • x + (2 ^ n : ℕ) • x`. Rewrite using `[pow_succ, mul_two, add_smul]`. Rewrite using `[e]`. Conclude with `Valuation.map_add_lt _ ih ih`.

Apply `eq_one_of_pow_two_pow_near` to reduce the goal to its premises. Introduce `n`. Establish `h3 : ψ ((2 ^ n : ℕ) • x) ∈ Metric.ball (1 : ℂ) (1 / 2)` using `hsub (h2 n)`. Rewrite `h3` using `[AddChar.map_nsmul_eq_pow, Metric.mem_ball, dist_eq_norm]`. Conclude with `h3`.

Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `hn : {y : k | ValuativeRel.valuation k (y - x) < γ} ∈ nhds x`. Establish `hc : ContinuousAt (fun y : k => y - x) x` using `by fun_prop`. Conclude with `hc.preimage_mem_nhds (by simpa using hb.mem_of_mem hγ)`.

Use `filter_upwards [hn] with y hy`. Establish `e : ψ y = ψ (y - x) * ψ x`. Rewrite using `[← AddChar.map_add_eq_mul]`. Simplify using the standard rewrite rules. Rewrite using `[e, hker _ hy, one_mul]`.
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
Introduce `k _ _ _ _ _ ψ0 hψ κ _ w φ hφ`. Take `⟨h1, h2⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ` from `hφ`. Establish `hl` using `isLocallyConstant_addChar ψ0 hψ`. Establish `hcont : Continuous fun x : κ → k => x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)`. Use `Continuous.add ?_ continuous_const` and prove the remaining obligations.

Conclude with `continuous_id.dotProduct continuous_const`. Establish `hs : HasCompactSupport fun x : κ → k => φ (x + w.1)` using `h2.comp_homeomorph (Homeomorph.addRight w.1)`. Establish `hf : IsLocallyConstant fun x : κ → k => φ (x + w.1)` using `h1.comp_continuous (continuous_add_const w.1)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(hl.comp_continuous hcont).mul hf`.

Conclude with `HasCompactSupport.mul_left hs`.
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
Apply the tactic sequence `first | exact @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | exact SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | (intros; apply SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB <;> assumption)`.
-/
theorem _root_.GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | exact SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | (intros; apply SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB <;> assumption)

end
