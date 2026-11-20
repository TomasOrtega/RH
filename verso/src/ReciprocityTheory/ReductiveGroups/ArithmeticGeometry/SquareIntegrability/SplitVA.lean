import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Module
open scoped nonZeroDivisors

noncomputable section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem exists_dual (φ : 𝓞 E →+ ℤ) :
    ∃ y : E, ∀ β : 𝓞 E, Algebra.trace ℚ E ((β : E) * y) = φ β := by
  classical
  let bZ := NumberField.RingOfIntegers.basis E
  let bQ := NumberField.integralBasis E
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  let dB := (Algebra.traceForm ℚ E).dualBasis hnd bQ
  refine ⟨∑ i, (φ (bZ i) : ℚ) • dB i, fun β => ?_⟩
  let f₁ : 𝓞 E →ₗ[ℤ] ℚ :=
    ((Algebra.trace ℚ E).restrictScalars ℤ).comp
      ((LinearMap.mulRight ℚ (∑ i, (φ (bZ i) : ℚ) • dB i)).restrictScalars ℤ ∘ₗ
        (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)
  let f₂ : 𝓞 E →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ.toIntLinearMap
  have hf : f₁ = f₂ := by
    refine bZ.ext fun j => ?_
    simp only [f₁, f₂, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.mulRight_apply, Algebra.linearMap_apply, AddMonoidHom.coe_toIntLinearMap,
      Int.coe_castAddHom]
    rw [Finset.mul_sum, map_sum]
    have hb : (algebraMap (𝓞 E) E) (bZ j) = bQ j := (NumberField.integralBasis_apply E j).symm
    rw [hb]
    simp_rw [mul_smul_comm, map_smul]
    have h : ∀ i, Algebra.trace ℚ E (bQ j * dB i) = if j = i then 1 else 0 := fun i => by
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left hnd bQ i j
    simp [h]
  have := congrArg (fun g => g β) hf
  simpa [f₁, f₂] using this

abbrev Dual1 (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mem_dual_of (y : E) (hy : ∀ β : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((β : E) * y) = k) :
    y ∈ Dual1 E := by
  rw [FractionalIdeal.mem_dual (I := (1 : FractionalIdeal (𝓞 E)⁰ E)) one_ne_zero]
  intro a ha
  obtain ⟨β, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
  obtain ⟨k, hk⟩ := hy β
  refine ⟨k, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm, hk]
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem one_le_norm_mul (l : E) (hl : l ≠ 0) (hmem : l ∈ Dual1 E * Dual1 E) :
    (1 : ℚ) ≤ |Algebra.norm ℚ l| * ((NumberField.discr E).natAbs : ℚ) ^ 2 := by
  classical
  have hD0 : Dual1 E ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  set dI : FractionalIdeal (𝓞 E)⁰ E :=
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hdI
  have hdD : dI * Dual1 E = 1 := by
    rw [hdI, coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
    exact inv_mul_cancel₀ hD0
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ l ≤ Dual1 E * Dual1 E :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hJ : dI * dI * FractionalIdeal.spanSingleton (𝓞 E)⁰ l ≤ 1 := by
    calc _ ≤ dI * dI * (Dual1 E * Dual1 E) := by first | exact mul_le_mul' le_rfl hle | gcongr
      _ = (dI * Dual1 E) * (dI * Dual1 E) := by ring
      _ = 1 := by rw [hdD, one_mul]
  obtain ⟨J, hJe⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hn := congrArg FractionalIdeal.absNorm hJe
  rw [map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, hdI, FractionalIdeal.coeIdeal_absNorm (K := E),
    FractionalIdeal.coeIdeal_absNorm (K := E), NumberField.absNorm_differentIdeal (K := E) (𝒪 := 𝓞 E)] at hn
  have hN0 : Algebra.norm ℚ l ≠ 0 := Algebra.norm_ne_zero_iff.mpr hl
  have hd0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have hpos : ((NumberField.discr E).natAbs : ℚ) * (NumberField.discr E).natAbs
      * |Algebra.norm ℚ l| ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hd0) (by exact_mod_cast hd0)) (abs_ne_zero.mpr hN0)
  have hJ1 : 1 ≤ Ideal.absNorm J := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm J) with h0 | h0
    · exfalso; rw [h0, Nat.cast_zero] at hn; exact hpos hn.symm
    · exact h0
  have h1 : (1 : ℚ) ≤ Ideal.absNorm J := by exact_mod_cast hJ1
  rw [hn] at h1
  calc (1 : ℚ) ≤ _ := h1
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2
