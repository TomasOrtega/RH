import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic

open Complex GlobalTheory.Glob.IntegralWittCoefficients

def IsPeriodLattice (Λ : AddSubgroup ℂ) (ω₁ τ : ℂ) : Prop :=
  ∀ x : ℂ, x ∈ Λ ↔ ∃ m n : ℤ, x = ω₁ * ((m : ℂ) + (n : ℂ) * τ)

def thetaChar (a b : Fin 2) (z τ : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4 +
      (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * (z + ((b : ℕ) : ℂ) / 2)) *
    jacobiTheta₂ (z + (((a : ℕ) : ℂ) * τ + ((b : ℕ) : ℂ)) / 2) τ

def IsEvenChar (a b : Fin 2) : Prop := (a : ℕ) * (b : ℕ) = 0

def NormTheta0 : Prop :=
  ∀ (Λ : AddSubgroup ℂ) (ω₁ τ t₀ : ℂ), ω₁ ≠ 0 → 0 < τ.im → IsPeriodLattice Λ ω₁ τ →
    2 * t₀ ∈ Λ → t₀ ∉ Λ →
    (∃! c : Fin 2 × Fin 2, IsEvenChar c.1 c.2 ∧ thetaChar c.1 c.2 (t₀ / ω₁) τ = 0) ∧
    0 < normSq1 Λ (th0 Λ t₀) ∧
    ∀ a b : Fin 2, IsEvenChar a b → thetaChar a b (t₀ / ω₁) τ = 0 →
      (normSq1 Λ (th0 Λ t₀))⁻¹ = Real.sqrt (2 * τ.im) * ‖thetaChar a b 0 τ‖ ^ 2

/- English proof (translation)
Unfold `thetaChar jacobiTheta₂ jacobiTheta₂_term`. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[← Complex.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaChar_eq_tsum (a b : Fin 2) (z τ : ℂ) :
    thetaChar a b z τ = ∑' n : ℤ, cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (z + ((b : ℕ) : ℂ) / 2)) := by
  unfold thetaChar jacobiTheta₂ jacobiTheta₂_term
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Simplify using `[thetaChar]`.
-/
theorem thetaChar_zero_zero (z τ : ℂ) : thetaChar 0 0 z τ = jacobiTheta₂ z τ := by
  simp [thetaChar]

/- English proof (translation)
Unfold `thetaChar`. Rewrite using `[← mul_assoc, ← Complex.exp_add, zero_add, zero_add]`. Establish `: -((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4) - (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * ((b : ℕ) : ℂ) / 2 + ((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4 + (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * (((b : ℕ) : ℂ) / 2)) = 0` using `by ring`. Rewrite using `[this, Complex.exp_zero, one_mul]`.
-/
theorem jacobiTheta₂_half (a b : Fin 2) (τ : ℂ) :
    jacobiTheta₂ ((((a : ℕ) : ℂ) * τ + ((b : ℕ) : ℂ)) / 2) τ =
      cexp (-((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4) -
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * ((b : ℕ) : ℂ) / 2) * thetaChar a b 0 τ := by
  unfold thetaChar
  rw [← mul_assoc, ← Complex.exp_add, zero_add, zero_add]
  have : -((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4) -
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * ((b : ℕ) : ℂ) / 2 +
      ((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4 +
        (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * (((b : ℕ) : ℂ) / 2)) = 0 := by ring
  rw [this, Complex.exp_zero, one_mul]

/- English proof (translation)
Establish `h : IsPeriodLattice (AddSubgroup.closure {1, I}) 1 I`. Introduce `x`. Rewrite using `[AddSubgroup.mem_closure_pair]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`.

Conclude with `⟨m, n, by simp⟩`. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨m, n, by simp⟩`. Use `⟨_, 1, I, 1 / 2, one_ne_zero, by simp, h, (h _).2 ⟨1, 0, by norm_num⟩, fun hx => ?_⟩` and prove the remaining obligations. Take `⟨m, n, hmn⟩` from `(h _).1 hx`.

Establish `h1` using `congrArg Complex.re hmn`. Simplify using `at h1`. Establish `h2 : (2 * m : ℝ) = 1` using `by rw [← h1]; norm_num`. Establish `h3 : (2 * m : ℤ) = 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
example : ∃ (Λ : AddSubgroup ℂ) (ω₁ τ t₀ : ℂ), ω₁ ≠ 0 ∧ 0 < τ.im ∧ IsPeriodLattice Λ ω₁ τ ∧
    2 * t₀ ∈ Λ ∧ t₀ ∉ Λ := by
  have h : IsPeriodLattice (AddSubgroup.closure {1, I}) 1 I := by
    intro x
    rw [AddSubgroup.mem_closure_pair]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by simp⟩
  refine ⟨_, 1, I, 1 / 2, one_ne_zero, by simp, h, (h _).2 ⟨1, 0, by norm_num⟩, fun hx => ?_⟩
  obtain ⟨m, n, hmn⟩ := (h _).1 hx
  have h1 := congrArg Complex.re hmn
  simp at h1
  have h2 : (2 * m : ℝ) = 1 := by rw [← h1]; norm_num
  have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
  omega

end GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic
