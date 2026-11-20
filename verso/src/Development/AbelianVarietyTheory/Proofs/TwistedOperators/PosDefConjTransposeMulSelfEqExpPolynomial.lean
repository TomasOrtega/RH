import Mathlib
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace GlobalTheory

/- English proof (translation)
Introduce `n g hg`. Use `set h : Matrix (Fin n) (Fin n) ℂ := gᴴ * g with hh`. Establish `hpd : h.PosDef` using `Matrix.PosDef.conjTranspose_mul_self g (Matrix.mulVec_injective_iff_isUnit.mpr hg)`. Establish `hsp : IsStrictlyPositive h` using `hpd.isStrictlyPositive`. Establish `hsa : IsSelfAdjoint h` using `hpd.isHermitian`.

Establish `hfin : (spectrum ℝ h).Finite` using `Matrix.finite_real_spectrum`. Set `s : Finset ℝ` to `hfin.toFinset`. Set `q : Polynomial ℝ` to `Lagrange.interpolate s id Real.log`. Establish `hq : ∀ x ∈ spectrum ℝ h, q.eval x = Real.log x`. Introduce `x hx`.

Establish `hxs : x ∈ s` using `hfin.mem_toFinset.mpr hx`. Conclude with `Lagrange.eval_interpolate_at_node (r := Real.log) (Set.injOn_id _) hxs`. Use `⟨CFC.log h, q.map (algebraMap ℝ ℂ), ?_, CFC.exp_log h hsp, ?_⟩` and prove the remaining obligations. Establish `: IsSelfAdjoint (CFC.log h)`. Unfold `CFC.log`.

Conclude with `cfc_predicate _ _`. Conclude with `this`. Rewrite using `[Polynomial.aeval_map_algebraMap, ← cfc_polynomial q h]`. Unfold `CFC.log`. Conclude with `cfc_congr (fun x hx => (hq x hx).symm)`.
-/
theorem posDef_conjTranspose_mul_self_eq_exp_polynomial :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g →
      ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
        Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  intro n g hg
  set h : Matrix (Fin n) (Fin n) ℂ := gᴴ * g with hh
  have hpd : h.PosDef :=
    Matrix.PosDef.conjTranspose_mul_self g (Matrix.mulVec_injective_iff_isUnit.mpr hg)
  have hsp : IsStrictlyPositive h := hpd.isStrictlyPositive
  have hsa : IsSelfAdjoint h := hpd.isHermitian
  have hfin : (spectrum ℝ h).Finite := Matrix.finite_real_spectrum
  classical
  let s : Finset ℝ := hfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate s id Real.log
  have hq : ∀ x ∈ spectrum ℝ h, q.eval x = Real.log x := by
    intro x hx
    have hxs : x ∈ s := hfin.mem_toFinset.mpr hx
    exact Lagrange.eval_interpolate_at_node (r := Real.log) (Set.injOn_id _) hxs
  refine ⟨CFC.log h, q.map (algebraMap ℝ ℂ), ?_, CFC.exp_log h hsp, ?_⟩
  · have : IsSelfAdjoint (CFC.log h) := by
      unfold CFC.log; exact cfc_predicate _ _
    exact this
  · rw [Polynomial.aeval_map_algebraMap, ← cfc_polynomial q h]
    unfold CFC.log
    exact cfc_congr (fun x hx => (hq x hx).symm)

end GlobalTheory
