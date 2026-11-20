import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Assume the negation of the conclusion and derive a contradiction. Use the polynomial consequences of the given equalities and inequalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem cas_diag_unitOn (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (hU : UnitOn s F U) :
    (∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re) ∧
      (U ≠ ⊥ → ∃ (ω : ℝ) (v : M), v ∈ U ∧ v ≠ 0 ∧ cas s F v = (ω : ℂ) • v) := by
  obtain ⟨hfin, hst, ip, hherm, hpos, hadj⟩ := hU
  have hw : ∀ w ∈ U, (ip w w).im = 0 ∧ 0 ≤ (ip w w).re := by
    intro w hw
    constructor
    · have h := congrArg Complex.im (hherm w hw w hw)
      simp at h
      linarith
    · by_cases h0 : w = 0
      · simp [h0]
      · exact le_of_lt (hpos w hw h0)
  have key : ∀ v ∈ U, ip v (cas s F v) = ∑ a, ∑ b, if s a = s b then ip (F b a v) (F b a v) else 0 := by
    intro v hv
    simp only [cas, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [Module.End.mul_apply]
      exact (hadj b a h.symm v hv (F b a v) (hst b a h.symm v hv)).symm
    · simp
  have hS : ∀ v ∈ U, (ip v (cas s F v)).im = 0 ∧ 0 ≤ (ip v (cas s F v)).re := by
    intro v hv
    rw [key v hv, Complex.im_sum, Complex.re_sum]
    constructor
    · refine Finset.sum_eq_zero fun a _ => ?_
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h
      · exact (hw _ (hst b a h.symm v hv)).1
      · simp
    · refine Finset.sum_nonneg fun a _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_nonneg fun b _ => ?_
      split_ifs with h
      · exact (hw _ (hst b a h.symm v hv)).2
      · simp
  have first : ∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re := by
    intro c v hv h0 hc
    have e := hS v hv
    rw [hc, map_smul, smul_eq_mul, Complex.mul_im, Complex.mul_re] at e
    have r0 := (hw v hv).1
    have rp := hpos v hv h0
    rw [r0] at e
    simp only [mul_zero, zero_add, sub_zero] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp e1 with h | h
      · exact h
      · exact absurd h (ne_of_gt rp)
    · by_contra hneg
      push_neg at hneg
      nlinarith
  refine ⟨first, fun hne => ?_⟩
  have hcU : ∀ x ∈ U, cas s F x ∈ U := by
    intro x hx
    simp only [cas, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    split_ifs with h
    · rw [Module.End.mul_apply]
      exact hst a b h _ (hst b a h.symm x hx)
    · simp
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
  haveI : FiniteDimensional ℂ U := hfin
  let g : Module.End ℂ U := (cas s F).restrict hcU
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue g
  obtain ⟨w, hw'⟩ := hc.exists_hasEigenvector
  have hgw : g w = c • w := Module.End.mem_eigenspace_iff.mp hw'.1
  have hw0 : (w : M) ≠ 0 := fun h => hw'.2 (Subtype.ext h)
  have hcw : cas s F (w : M) = c • (w : M) := by
    have := congrArg Subtype.val hgw
    simpa [g] using this
  have hc' := first c w w.2 hw0 hcw
  refine ⟨c.re, w, w.2, hw0, ?_⟩
  rw [hcw]
  congr 1
  apply Complex.ext <;> simp [hc'.1]

end GlobalTheory.HoweR
