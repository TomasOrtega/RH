import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMulCoeffCharpolyRev

set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

/- English proof (translation)
Unfold `TrSpan at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f h`. Take `⟨l, hl, hw, rfl⟩` from `h`. Use `Submodule.subset_span ⟨(τ, j) :: l, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Break down `List.mem_cons.1 hx with rfl | hx` into its components or cases. Conclude with `hj`. Conclude with `hl x hx`. Simplify using `[hw]`.

Use function extensionality and compare the values at `A`. Simplify using `[trProd]`. Consider the case `zero`. Establish `: (fun A : Mat m S => ((A τ) ^ j).trace * (0 : Mat m S → S) A) = 0`. Use function extensionality and compare the values at `A`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add f g _ _ hf hg`. Establish `: (fun A : Mat m S => ((A τ) ^ j).trace * (f + g) A) = (fun A : Mat m S => ((A τ) ^ j).trace * f A) + (fun A : Mat m S => ((A τ) ^ j).trace * g A)`.

Use function extensionality and compare the values at `A`. Simplify using `[mul_add]`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hf hg`. Consider the case `smul c f _ hf`.

Establish `: (fun A : Mat m S => ((A τ) ^ j).trace * (c • f) A) = c • (fun A : Mat m S => ((A τ) ^ j).trace * f A)`. Use function extensionality and compare the values at `A`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ c hf`.
-/
theorem trace_pow_mul_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι)
    (j w : ℕ) (hj : 1 ≤ j) (f : Mat m S → S) (hf : f ∈ TrSpan m w S) :
    (fun A : Mat m S => ((A τ) ^ j).trace * f A) ∈ TrSpan m (j + w) S := by
  unfold TrSpan at hf
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨l, hl, hw, rfl⟩ := h
    refine Submodule.subset_span ⟨(τ, j) :: l, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hj
      · exact hl x hx
    · simp [hw]
    · funext A
      simp [trProd]
  | zero =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (0 : Mat m S → S) A) = 0 := by
      funext A; simp
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (f + g) A) =
        (fun A : Mat m S => ((A τ) ^ j).trace * f A) + (fun A : Mat m S => ((A τ) ^ j).trace * g A) := by
      funext A; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (c • f) A) =
        c • (fun A : Mat m S => ((A τ) ^ j).trace * f A) := by
      funext A; simp
    rw [this]; exact Submodule.smul_mem _ c hf

/- English proof (translation)
Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Use `Submodule.subset_span ⟨[], by simp, by simp, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `A`.

Simplify using `[trProd, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]`. Establish `hk' : (k : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Establish `key : (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) = (-(k : ℝ)⁻¹) • ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ (i + 1)) • (fun A : Mat m S => ((A τ) ^ (i + 1)).trace * (Matrix.charpolyRev (-(A τ))).coeff (k - 1 - i))`. Use function extensionality and compare the values at `A`. Establish `h` using `GlobalTheory.natCast_mul_coeff_charpolyRev (-(A τ)) k`.

Establish `e : ∀ i : ℕ, ((-(A τ)) ^ (i + 1)).trace = ((-1 : ℝ) ^ (i + 1)) • ((A τ) ^ (i + 1)).trace`. Introduce `i`. Rewrite using `[← neg_one_smul ℝ (A τ), smul_pow, Matrix.trace_smul]`. Simplify using `only [e, smul_mul_assoc] at h`. Simplify using `only [Pi.smul_apply, Finset.sum_apply]`.

Rewrite using `[neg_smul, ← smul_neg, ← h, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hk', one_smul]`. Rewrite using `[key]`. Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Establish `hi'` using `Finset.mem_range.1 hi`. Establish `h` using `trace_pow_mul_mem_trSpan m S τ (i + 1) (k - 1 - i) (by omega) _ (ih (k - 1 - i) (by omega))`.

Rewrite `h` using `[show i + 1 + (k - 1 - i) = k by omega]`. Then use the resulting hypothesis.
-/
theorem coeff_charpolyRev_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (τ : ι) (k : ℕ) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine Submodule.subset_span ⟨[], by simp, by simp, ?_⟩
      funext A
      simp [trProd, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have key : (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) =
          (-(k : ℝ)⁻¹) • ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ (i + 1)) •
            (fun A : Mat m S => ((A τ) ^ (i + 1)).trace *
              (Matrix.charpolyRev (-(A τ))).coeff (k - 1 - i)) := by
        funext A
        have h := GlobalTheory.natCast_mul_coeff_charpolyRev (-(A τ)) k
        have e : ∀ i : ℕ, ((-(A τ)) ^ (i + 1)).trace = ((-1 : ℝ) ^ (i + 1)) • ((A τ) ^ (i + 1)).trace := by
          intro i
          rw [← neg_one_smul ℝ (A τ), smul_pow, Matrix.trace_smul]
        simp only [e, smul_mul_assoc] at h
        simp only [Pi.smul_apply, Finset.sum_apply]
        rw [neg_smul, ← smul_neg, ← h, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          inv_mul_cancel₀ hk', one_smul]
      rw [key]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
      have hi' := Finset.mem_range.1 hi
      have h := trace_pow_mul_mem_trSpan m S τ (i + 1) (k - 1 - i) (by omega) _ (ih (k - 1 - i) (by omega))
      rwa [show i + 1 + (k - 1 - i) = k by omega] at h

end GlobalTheory.GoodMetric.ChernSpan
