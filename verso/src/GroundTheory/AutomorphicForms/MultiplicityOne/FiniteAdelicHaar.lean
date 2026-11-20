import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalHaar
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicDistribution

open MeasureTheory Measure Topology Filter Set IsDedekindDomain NumberField

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `: Subsingleton (AdelicGLn.FiniteAdelicGL K 0)` using `⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim g 1]`. Simplify using `only [mul_one]`.

Conclude with `Measure.map_id`. Set `_ : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n)` to `_root_.borel _`. Establish `: BorelSpace (AdelicGLn.InfiniteAdelicGL K n)` using `⟨rfl⟩`. Use `set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar`. Use `set P := μi.prod μ`.

Use `set e := AdelicGLn.prodEquiv K n`. Use `set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar`. Establish `hν` using `GJGlobal.isMulRightInvariant_haar ν hn`. Establish `he : Measurable e` using `e.continuous.measurable`. Establish `: (ν.map e).IsHaarMeasure` using `MulEquiv.isHaarMeasure_map ν e.toMulEquiv e.continuous e.symm.continuous`.

Establish `hν' : ∀ p, (ν.map e).map (· * p) = ν.map e`. Introduce `p`. Establish `hcomp : (· * p) ∘ e = e ∘ (· * e.symm p)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]`.

Rewrite using `[Measure.map_map (measurable_mul_const p) he, hcomp, ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]`. Use `set c := haarScalarFactor (ν.map e) P`. Establish `hc : ν.map e = c • P` using `isMulLeftInvariant_eq_smul (ν.map e) P`. Establish `hc0 : c ≠ 0`. Introduce `h0`.

Rewrite `hc` using `[h0, zero_smul]`. Establish `hne` using `isOpen_univ.measure_ne_zero (ν.map e) univ_nonempty`. Rewrite `hne` using `[hc]`. Conclude with `hne rfl`. Establish `hP : ∀ p, P.map (· * p) = P`.

Introduce `p`. Establish `h1 : P = c⁻¹ • ν.map e` using `by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Rewrite using `[h1, Measure.map_smul, hν']`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `hprod : P.map (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = μi.prod (μ.map (· * g))`.

Establish `hf : (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = Prod.map id (· * g)`. Use function extensionality and compare the values at `p`. Conclude with `Prod.ext (mul_one p.1) rfl`. Rewrite using `[hf, ← Measure.map_prod_map μi μ measurable_id (measurable_mul_const g), Measure.map_id]`. Rewrite `hprod` using `[hP]`.

Take `⟨A, hAc, hA⟩` from `exists_compact_mem_nhds (1 : AdelicGLn.InfiniteAdelicGL K n)`. Establish `hA0 : μi A ≠ 0` using `(measure_pos_of_mem_nhds μi hA).ne'`. Establish `hAt : μi A ≠ ⊤` using `hAc.measure_lt_top.ne`. Use `Measure.ext fun B hB => ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun m : Measure _ => m (A ×ˢ B)) hprod`.

Simplify using `only [P, Measure.prod_prod] at h1`. Conclude with `((ENNReal.mul_right_inj hA0 hAt).1 h1).symm`.
-/
theorem isMulRightInvariant_finite (μ : Measure (AdelicGLn.FiniteAdelicGL K n)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.FiniteAdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨fun g => ?_⟩
    rw [Subsingleton.elim g 1]
    simp only [mul_one]
    exact Measure.map_id
  let _ : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _
  have : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  set P := μi.prod μ
  set e := AdelicGLn.prodEquiv K n
  set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar
  have hν := GJGlobal.isMulRightInvariant_haar ν hn
  have he : Measurable e := e.continuous.measurable
  have : (ν.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map ν e.toMulEquiv e.continuous e.symm.continuous
  have hν' : ∀ p, (ν.map e).map (· * p) = ν.map e := by
    intro p
    have hcomp : (· * p) ∘ e = e ∘ (· * e.symm p) := by
      funext x
      simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
    rw [Measure.map_map (measurable_mul_const p) he, hcomp,
      ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]

  set c := haarScalarFactor (ν.map e) P
  have hc : ν.map e = c • P := isMulLeftInvariant_eq_smul (ν.map e) P
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    have hne := isOpen_univ.measure_ne_zero (ν.map e) univ_nonempty
    rw [hc] at hne
    exact hne rfl
  have hP : ∀ p, P.map (· * p) = P := by
    intro p
    have h1 : P = c⁻¹ • ν.map e := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1, Measure.map_smul, hν']
  refine ⟨fun g => ?_⟩
  have hprod : P.map (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = μi.prod (μ.map (· * g)) := by
    have hf : (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = Prod.map id (· * g) := by
      funext p
      exact Prod.ext (mul_one p.1) rfl
    rw [hf, ← Measure.map_prod_map μi μ measurable_id (measurable_mul_const g), Measure.map_id]
  rw [hP] at hprod
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds (1 : AdelicGLn.InfiniteAdelicGL K n)
  have hA0 : μi A ≠ 0 := (measure_pos_of_mem_nhds μi hA).ne'
  have hAt : μi A ≠ ⊤ := hAc.measure_lt_top.ne
  refine Measure.ext fun B hB => ?_
  have h1 := congrArg (fun m : Measure _ => m (A ×ˢ B)) hprod
  simp only [P, Measure.prod_prod] at h1
  exact ((ENNReal.mul_right_inj hA0 hAt).1 h1).symm

end

end Whittaker

end GroundTheory.Automorphic
