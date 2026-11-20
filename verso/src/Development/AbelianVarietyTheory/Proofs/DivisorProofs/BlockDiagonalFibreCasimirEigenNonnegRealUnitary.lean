import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Take `⟨hfin, hst, ip, hherm, hpos, hadj⟩` from `hU`. Establish `hw : ∀ w ∈ U, (ip w w).im = 0 ∧ 0 ≤ (ip w w).re`. Introduce `w hw`. Prove the components needed by the constructor for the conclusion. Establish `h` using `congrArg Complex.im (hherm w hw w hw)`.

Simplify using `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h0 : w = 0`. Simplify using `[h0]`. Conclude with `le_of_lt (hpos w hw h0)`.

Establish `key : ∀ v ∈ U, ip v (cas s F v) = ∑ a, ∑ b, if s a = s b then ip (F b a v) (F b a v) else 0`. Introduce `v hv`. Simplify using `only [cas, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Rewrite using `[Module.End.mul_apply]`. Conclude with `(hadj b a h.symm v hv (F b a v) (hst b a h.symm v hv)).symm`. Simplify using the standard rewrite rules. Establish `hS : ∀ v ∈ U, (ip v (cas s F v)).im = 0 ∧ 0 ≤ (ip v (cas s F v)).re`. Introduce `v hv`.

Rewrite using `[key v hv, Complex.im_sum, Complex.re_sum]`. Prove the components needed by the constructor for the conclusion. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.im_sum]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Conclude with `(hw _ (hst b a h.symm v hv)).1`. Simplify using the standard rewrite rules. Use `Finset.sum_nonneg fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.re_sum]`.

Use `Finset.sum_nonneg fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `(hw _ (hst b a h.symm v hv)).2`. Simplify using the standard rewrite rules. Establish `first : ∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re`.

Introduce `c v hv h0 hc`. Establish `e` using `hS v hv`. Rewrite `e` using `[hc, map_smul, smul_eq_mul, Complex.mul_im, Complex.mul_re]`. Establish `r0` using `(hw v hv).1`. Establish `rp` using `hpos v hv h0`.

Rewrite `e` using `[r0]`. Simplify using `only [mul_zero, zero_add, sub_zero] at e`. Take `⟨e1, e2⟩` from `e`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Break down `mul_eq_zero.mp e1 with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h (ne_of_gt rp)`. Assume the negation of the conclusion as `hneg push_neg at hneg`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨first, fun hne => ?_⟩` and prove the remaining obligations.

Establish `hcU : ∀ x ∈ U, cas s F x ∈ U`. Introduce `x hx`. Simplify using `only [cas, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Rewrite using `[Module.End.mul_apply]`. Conclude with `hst a b h _ (hst b a h.symm x hx)`. Simplify using the standard rewrite rules. Use `haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne`. Use `haveI : FiniteDimensional ℂ U := hfin`.

Set `g : Module.End ℂ U` to `(cas s F).restrict hcU`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue g`. Take `⟨w, hw'⟩` from `hc.exists_hasEigenvector`. Establish `hgw : g w = c • w` using `Module.End.mem_eigenspace_iff.mp hw'.1`. Establish `hw0 : (w : M) ≠ 0` using `fun h => hw'.2 (Subtype.ext h)`.

Establish `hcw : cas s F (w : M) = c • (w : M)`. Use `congrArg Subtype.val hgw` as an intermediate fact. Simplify `this` using `[g]`. Establish `hc'` using `first c w w.2 hw0 hcw`. Use `⟨c.re, w, w.2, hw0, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcw]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp [hc'.1]`.
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
