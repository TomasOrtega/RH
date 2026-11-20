import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

/- English proof (translation)
Introduce and unpack `⟨hPA, rP, hrP0, hrPi⟩ ⟨hQA, rQ, hrQ0, hrQi⟩`. Set `lift : ∀ φ : HahnSeries ℚ Ω, (∀ r, φ.coeff r ∈ A) → HahnSeries ℚ A` to `fun φ h => { coeff := fun r => ⟨φ.coeff r, h r⟩ isPWO_support' := φ.isPWO_support.mono (fun r hr h' => hr (Subtype.ext (by simpa using h'))) }`. Set `P'` to `lift P hPA`. Set `Q'` to `lift Q hQA`. Set `ι : A →ₙ+* Ω` to `(A.subtype : A →+* Ω)`.

Establish `hPm : P'.map ι = P` using `by ext r; rfl`. Establish `hQm : Q'.map ι = Q` using `by ext r; rfl`. Establish `hmul : (P' * Q').map ι = P * Q` using `by rw [HahnSeries.map_mul, hPm, hQm]`. Establish `hcoeff : ∀ r, (P * Q).coeff r = (((P' * Q').coeff r : A) : Ω)`. Introduce `r`.

Rewrite using `[← hmul]`. Both sides reduce to the same expression. Establish `hunit : ∀ (x : Ω) (hx : x ∈ A), x ≠ 0 → x⁻¹ ∈ A → IsUnit (⟨x, hx⟩ : A)`. Introduce `x hx h0 hi`. Establish `h : (⟨x, hx⟩ : A) * ⟨x⁻¹, hi⟩ = 1` using `Subtype.ext (by simp [mul_inv_cancel₀ h0])`.

Conclude with `(Units.mkOfMulEqOne _ _ h).isUnit`. Set `π : A →ₙ+* IsLocalRing.ResidueField A` to `(IsLocalRing.residue A : A →+* IsLocalRing.ResidueField A)`. Establish `hred : ∀ (φ : HahnSeries ℚ Ω) (h : ∀ r, φ.coeff r ∈ A) (r : ℚ), φ.coeff r ≠ 0 → (φ.coeff r)⁻¹ ∈ A → (lift φ h).map π ≠ 0`. Introduce `φ h r h0 hi hz`. Use `congrArg (fun ψ : HahnSeries ℚ (IsLocalRing.ResidueField A) => ψ.coeff r) hz` as an intermediate fact.

Simplify using `only [HahnSeries.coeff_zero] at this`. Establish `hu` using `hunit _ (h r) h0 hi`. Establish `hres : IsLocalRing.residue A (⟨φ.coeff r, h r⟩ : A) = 0` using `this`. Rewrite `hres` using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hres hu`.

Establish `hne : (P' * Q').map π ≠ 0`. Rewrite using `[HahnSeries.map_mul]`. Conclude with `mul_ne_zero (hred P hPA rP hrP0 hrPi) (hred Q hQA rQ hrQ0 hrQi)`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r, ((P' * Q').map π).coeff r ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne (HahnSeries.ext (funext h))`. Establish `hr' : IsLocalRing.residue A ((P' * Q').coeff r) ≠ 0` using `hr`. Rewrite `hr'` using `[Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Take `⟨u, hu⟩` from `hr'`.

Establish `h1 : (((P' * Q').coeff r : A) : Ω) * (((u⁻¹ : Aˣ) : A) : Ω) = 1`. Rewrite using `[← hu]`. Use `congrArg (fun a : A => (a : Ω)) u.mul_inv` as an intermediate fact. Simplify `this` using `only [MulMemClass.coe_mul, OneMemClass.coe_one]`. Use `⟨fun r => by rw [hcoeff r]; exact ((P' * Q').coeff r).2, r, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcoeff r]`. Conclude with `left_ne_zero_of_mul_eq_one h1`. Rewrite using `[hcoeff r, inv_eq_of_mul_eq_one_right h1]`. Conclude with `((u⁻¹ : Aˣ) : A).2`.
-/
theorem Prim.mul {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω) :
    Prim A P → Prim A Q → Prim A (P * Q) := by
  classical
  rintro ⟨hPA, rP, hrP0, hrPi⟩ ⟨hQA, rQ, hrQ0, hrQi⟩
  let lift : ∀ φ : HahnSeries ℚ Ω, (∀ r, φ.coeff r ∈ A) → HahnSeries ℚ A := fun φ h =>
    { coeff := fun r => ⟨φ.coeff r, h r⟩
      isPWO_support' := φ.isPWO_support.mono (fun r hr h' => hr (Subtype.ext (by simpa using h'))) }
  let P' := lift P hPA
  let Q' := lift Q hQA
  let ι : A →ₙ+* Ω := (A.subtype : A →+* Ω)
  have hPm : P'.map ι = P := by ext r; rfl
  have hQm : Q'.map ι = Q := by ext r; rfl
  have hmul : (P' * Q').map ι = P * Q := by rw [HahnSeries.map_mul, hPm, hQm]
  have hcoeff : ∀ r, (P * Q).coeff r = (((P' * Q').coeff r : A) : Ω) := by
    intro r; rw [← hmul]; rfl

  have hunit : ∀ (x : Ω) (hx : x ∈ A), x ≠ 0 → x⁻¹ ∈ A → IsUnit (⟨x, hx⟩ : A) := by
    intro x hx h0 hi
    have h : (⟨x, hx⟩ : A) * ⟨x⁻¹, hi⟩ = 1 := Subtype.ext (by simp [mul_inv_cancel₀ h0])
    exact (Units.mkOfMulEqOne _ _ h).isUnit
  let π : A →ₙ+* IsLocalRing.ResidueField A := (IsLocalRing.residue A : A →+* IsLocalRing.ResidueField A)
  have hred : ∀ (φ : HahnSeries ℚ Ω) (h : ∀ r, φ.coeff r ∈ A) (r : ℚ), φ.coeff r ≠ 0 → (φ.coeff r)⁻¹ ∈ A →
      (lift φ h).map π ≠ 0 := by
    intro φ h r h0 hi hz
    have := congrArg (fun ψ : HahnSeries ℚ (IsLocalRing.ResidueField A) => ψ.coeff r) hz
    simp only [HahnSeries.coeff_zero] at this
    have hu := hunit _ (h r) h0 hi
    have hres : IsLocalRing.residue A (⟨φ.coeff r, h r⟩ : A) = 0 := this
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres hu
  have hne : (P' * Q').map π ≠ 0 := by
    rw [HahnSeries.map_mul]
    exact mul_ne_zero (hred P hPA rP hrP0 hrPi) (hred Q hQA rQ hrQ0 hrQi)
  obtain ⟨r, hr⟩ : ∃ r, ((P' * Q').map π).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (HahnSeries.ext (funext h))
  have hr' : IsLocalRing.residue A ((P' * Q').coeff r) ≠ 0 := hr
  rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr'
  obtain ⟨u, hu⟩ := hr'
  have h1 : (((P' * Q').coeff r : A) : Ω) * (((u⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hu]
    have := congrArg (fun a : A => (a : Ω)) u.mul_inv
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
  refine ⟨fun r => by rw [hcoeff r]; exact ((P' * Q').coeff r).2, r, ?_, ?_⟩
  · rw [hcoeff r]; exact left_ne_zero_of_mul_eq_one h1
  · rw [hcoeff r, inv_eq_of_mul_eq_one_right h1]; exact ((u⁻¹ : Aˣ) : A).2

end GlobalTheory.Glue
