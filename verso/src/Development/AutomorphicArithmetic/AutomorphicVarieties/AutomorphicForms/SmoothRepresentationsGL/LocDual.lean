import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Establish `h1 : ux⁻¹ ≤ g⁻¹` using `inv_anti₀ hg hgx`. Establish `h2 : ua * ux⁻¹ ≤ ua * g⁻¹` using `by gcongr`. Establish `h3 : 1 < p⁻¹` using `one_lt_inv₀ (zero_lt_iff.mpr hp0) |>.mpr hp`. Establish `h4 : 0 < ua * g⁻¹`. Apply `zero_lt_iff.mpr` to reduce the goal to its premises.

Conclude with `mul_ne_zero hua (inv_ne_zero hg.ne')`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one {G : Type} [LinearOrderedCommGroupWithZero G] (ua g ux p : G) (hua : ua ≠ 0)
    (hg : 0 < g) (hgx : g ≤ ux) (hp : p < 1) (hp0 : p ≠ 0) :
    ua * ux⁻¹ < ua * g⁻¹ * p⁻¹ := by
  have h1 : ux⁻¹ ≤ g⁻¹ := inv_anti₀ hg hgx
  have h2 : ua * ux⁻¹ ≤ ua * g⁻¹ := by gcongr
  have h3 : 1 < p⁻¹ := one_lt_inv₀ (zero_lt_iff.mpr hp0) |>.mpr hp
  have h4 : 0 < ua * g⁻¹ := by
    apply zero_lt_iff.mpr
    exact mul_ne_zero hua (inv_ne_zero hg.ne')
  calc ua * ux⁻¹ ≤ ua * g⁻¹ := h2
    _ = ua * g⁻¹ * 1 := (mul_one _).symm
    _ < ua * g⁻¹ * p⁻¹ := mul_lt_mul_of_pos_left h3 h4

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_lt_of_lt_mul_inv_of_lt {G : Type} [LinearOrderedCommGroupWithZero G] (q y r g1 : G) (hr : 0 < r)
    (hy : y < r) (hq : q < g1 * r⁻¹) : q * y < g1 := by
  calc q * y ≤ q * r := by gcongr
    _ < g1 * r⁻¹ * r := mul_lt_mul_of_pos_right hq hr
    _ = g1 := by rw [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

/- English proof (translation)
Introduce `E _ _ w ψ hψ V hV`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hψ (AddChar.ext _ _ fun x => by simpa using h x)`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at ha`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.mp hV`. Take `⟨C, hC, hC0⟩` from `exists_compact_mem_nhds (0 : HeightOneSpectrum.adicCompletion E w)`.

Take `⟨γ₁, hγ₁⟩` from `Valued.mem_nhds_zero.mp hC0`. Take `⟨π₀, hπ₀⟩` from `HeightOneSpectrum.valuation_exists_uniformizer E w`. Establish `hvπ : Valued.v (π₀ : HeightOneSpectrum.adicCompletion E w) = WithZero.exp (-1 : ℤ)`. Simplify using `[hπ₀]`. Establish `hπ0 : (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0`.

Introduce `h`. Rewrite `hvπ` using `[h, map_zero]`. Conclude with `WithZero.zero_ne_coe hvπ`. Establish `hπ1 : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) < 1`. Rewrite using `[Valuation.restrict_lt_one_iff, hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Evaluate the numerical expressions. Establish `hπn : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0`. Rewrite using `[Ne, Valuation.restrict_eq_zero_iff, hvπ]`. Conclude with `WithZero.exp_ne_zero`. Establish `hua : Valued.v.restrict a ≠ 0` using `by simp [ha0]`.

Use `set R := Units.mk0 (Valued.v.restrict a * (γ : _)⁻¹ * (Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w))⁻¹) (mul_ne_zero (mul_ne_zero hua γ⁻¹.ne_zero) (inv_ne_zero hπn)) with hR`. Take `⟨n, hn⟩` from `exists_pow_lt₀ hπ1 (γ₁ * R⁻¹)`. Use `⟨Valued.v.restrict.ltAddSubgroup R, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Valuation.coe_ltAddSubgroup]`. Conclude with `Valued.isOpen_ball _ _`.

Rewrite using `[Valuation.coe_ltAddSubgroup]`. Use `IsCompact.of_isClosed_subset (hC.image (continuous_const.mul continuous_id : Continuous fun z : HeightOneSpectrum.adicCompletion E w => ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n)⁻¹ * z)) (Valued.isClosed_ball _ _) ?_` and prove the remaining obligations. Introduce `y hy`. Use `⟨(π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y, hγ₁ ?_, ?_⟩` and prove the remaining obligations. Use `show Valued.v.restrict ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y) < γ₁`.

Rewrite using `[map_mul, map_pow]`. Use `mul_lt_of_lt_mul_inv_of_lt _ _ _ _ (zero_lt_iff.mpr R.ne_zero) hy ?_` and prove the remaining obligations. Simplify using `using hn`. Conclude with `inv_mul_cancel_left₀ (pow_ne_zero n hπ0) y`. Introduce `x hx`.

Assume the negation of the conclusion as `hxV`. Establish `hxg : (γ : _) ≤ Valued.v.restrict x`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hxV (hγ h)`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hxg` using `[map_zero]`. Conclude with `γ.ne_zero (le_antisymm hxg zero_le')`. Establish `hy : a * x⁻¹ ∈ Valued.v.restrict.ltAddSubgroup R`.

Rewrite using `[← SetLike.mem_coe, Valuation.coe_ltAddSubgroup]`. Use `show Valued.v.restrict (a * x⁻¹) < R`. Rewrite using `[map_mul, map_inv₀, hR, Units.val_mk0, Units.val_inv_eq_inv_val]`. Conclude with `mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one _ _ _ _ hua (zero_lt_iff.mpr γ.ne_zero) hxg hπ1 hπn`. Establish `h1` using `hx _ hy`.

Rewrite `h1` using `[mul_comm a, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]`. Conclude with `ha h1`.
-/
theorem UpperTheory.V.Af.Smo.locDual :
    UpperTheory.V.Af.Smo.LocDual := by
  intro E _ _ w ψ hψ V hV
  obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (AddChar.ext _ _ fun x => by simpa using h x)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : HeightOneSpectrum.adicCompletion E w)
  obtain ⟨γ₁, hγ₁⟩ := Valued.mem_nhds_zero.mp hC0
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  have hvπ : Valued.v (π₀ : HeightOneSpectrum.adicCompletion E w) = WithZero.exp (-1 : ℤ) := by
    simp [hπ₀]
  have hπ0 : (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvπ
    exact WithZero.zero_ne_coe hvπ
  have hπ1 : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) < 1 := by
    rw [Valuation.restrict_lt_one_iff, hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπn : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, hvπ]
    exact WithZero.exp_ne_zero
  have hua : Valued.v.restrict a ≠ 0 := by simp [ha0]
  set R := Units.mk0 (Valued.v.restrict a * (γ : _)⁻¹ *
    (Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w))⁻¹)
    (mul_ne_zero (mul_ne_zero hua γ⁻¹.ne_zero) (inv_ne_zero hπn)) with hR
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (γ₁ * R⁻¹)
  refine ⟨Valued.v.restrict.ltAddSubgroup R, ?_, ?_, ?_⟩
  · rw [Valuation.coe_ltAddSubgroup]
    exact Valued.isOpen_ball _ _
  · rw [Valuation.coe_ltAddSubgroup]
    refine IsCompact.of_isClosed_subset
      (hC.image (continuous_const.mul continuous_id :
        Continuous fun z : HeightOneSpectrum.adicCompletion E w =>
          ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n)⁻¹ * z))
      (Valued.isClosed_ball _ _) ?_
    intro y hy
    refine ⟨(π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y, hγ₁ ?_, ?_⟩
    · show Valued.v.restrict ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y) < γ₁
      rw [map_mul, map_pow]
      refine mul_lt_of_lt_mul_inv_of_lt _ _ _ _ (zero_lt_iff.mpr R.ne_zero) hy ?_
      simpa using hn
    · exact inv_mul_cancel_left₀ (pow_ne_zero n hπ0) y
  · intro x hx
    by_contra hxV
    have hxg : (γ : _) ≤ Valued.v.restrict x := by
      by_contra h
      push_neg at h
      exact hxV (hγ h)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hxg
      exact γ.ne_zero (le_antisymm hxg zero_le')
    have hy : a * x⁻¹ ∈ Valued.v.restrict.ltAddSubgroup R := by
      rw [← SetLike.mem_coe, Valuation.coe_ltAddSubgroup]
      show Valued.v.restrict (a * x⁻¹) < R
      rw [map_mul, map_inv₀, hR, Units.val_mk0, Units.val_inv_eq_inv_val]
      exact mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one _ _ _ _ hua (zero_lt_iff.mpr γ.ne_zero) hxg hπ1 hπn
    have h1 := hx _ hy
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    exact ha h1
