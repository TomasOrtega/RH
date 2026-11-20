import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

noncomputable section

variable {κ ι : Type}

def rep (R : ℕ) (n : κ → ι → Fin (R * R)) : Matrix κ ι ℚ :=
  Matrix.of fun k i => ((n k i : ℕ) : ℚ) / R

def zm (m : κ → ι → ℤ) : Matrix κ ι ℚ := Matrix.of fun k i => (m k i : ℚ)

def zv (m : ι → ℤ) : ι → ℚ := fun i => (m i : ℚ)

def ech (t : ℚ) : ℂ := cexp (2 * π * I * (t : ℂ))

def gs [Fintype ι] (τ : Matrix ι ι ℂ) (ζ : ι → ℂ) (v : ι → ℚ) : ℂ :=
  cexp (π * I * (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)))

/- English proof (translation)
Unfold `ech`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ech_add (s t : ℚ) : ech (s + t) = ech s * ech t := by
  unfold ech
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Simplify using `[ech]`.
-/
theorem ech_zero : ech 0 = 1 := by
  simp [ech]

/- English proof (translation)
Unfold `ech`. Rewrite using `[show (2 : ℂ) * π * I * ((m : ℚ) : ℂ) = (m : ℂ) * (2 * π * I) by push_cast; ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I m`.
-/
theorem ech_int (m : ℤ) : ech (m : ℚ) = 1 := by
  unfold ech
  rw [show (2 : ℂ) * π * I * ((m : ℚ) : ℂ) = (m : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/- English proof (translation)
Unfold `ech`. Rewrite using `[Complex.exp_eq_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `h : (t : ℂ) = ((n : ℚ) : ℂ)`. Apply `mul_left_cancel₀ Complex.two_pi_I_ne_zero` to reduce the goal to its premises. Rewrite using `[hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h` after adjusting the coercions. Introduce and unpack `⟨m, rfl⟩`. Conclude with `⟨m, by push_cast; ring⟩`.
-/
theorem ech_eq_one_iff (t : ℚ) : ech t = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ech
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (t : ℂ) = ((n : ℚ) : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]
      push_cast
      ring
    exact_mod_cast h
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/- English proof (translation)
Unfold `ech`. Rewrite using `[show (2 : ℂ) * π * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem norm_ech (t : ℚ) : ‖ech t‖ = 1 := by
  unfold ech
  rw [show (2 : ℂ) * π * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/- English proof (translation)
Unfold `ech`. Rewrite using `[← Complex.exp_conj]`. Use `congr 1`. Simplify using `only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_ratCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_ech (t : ℚ) : conj (ech t) = ech (-t) := by
  unfold ech
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
  push_cast
  ring

/- English proof (translation)
Unfold `ech`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`.
-/
theorem ech_sum {α : Type} (s : Finset α) (f : α → ℚ) : ech (∑ a ∈ s, f a) = ∏ a ∈ s, ech (f a) := by
  unfold ech
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h choose m hm using fun k i => (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp (h k i)`. Use `⟨m, Matrix.ext fun k i => ?_⟩` and prove the remaining obligations. Rewrite using `[← hm k i]`. Simplify using `[zm]`.

Introduce and unpack `⟨m, rfl⟩ k i`. Simplify `(isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℚ (m k i)))` using `[zm]`.
-/
theorem intM_iff [Fintype κ] [Fintype ι] (x : Matrix κ ι ℚ) : IntM x ↔ ∃ m : κ → ι → ℤ, x = zm m := by
  constructor
  · intro h
    choose m hm using fun k i => (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp (h k i)
    refine ⟨m, Matrix.ext fun k i => ?_⟩
    rw [← hm k i]
    simp [zm]
  · rintro ⟨m, rfl⟩ k i
    simpa [zm] using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℚ (m k i)))

end

end GlobalTheory.SW.FourierJ
