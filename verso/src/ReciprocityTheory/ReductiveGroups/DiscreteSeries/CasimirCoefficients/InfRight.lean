import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LowMinusUpExpand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRightA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

/- English proof (translation)
Establish `h'` using `congrArg (fun w => c⁻¹ • w) h`. Simplify `h'` using `[smul_smul, inv_mul_cancel₀ hc]`.
-/
private lemma smul_cancel_lemma {E : Type*} [AddCommGroup E] [Module ℂ E] {c : ℂ} (hc : c ≠ 0)
    {u v : E} (h : c • u = c • v) : u = v := by
  have h' := congrArg (fun w => c⁻¹ • w) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using h'

/- English proof (translation)
Take `⟨hAs, hAb⟩` from `(inK_iff ε A).1 hA`. Establish `hH : IsBlock ε (Complex.I • A)`. Introduce `i j hij`. Rewrite using `[Matrix.smul_apply, hAb i j hij, smul_zero]`. Establish `hI : star Complex.I = -Complex.I` using `Complex.conj_I`.

Establish `hHh : (Complex.I • A)ᴴ = Complex.I • A`. Rewrite using `[Matrix.conjTranspose_smul, hAs, hI, neg_smul_neg]`. Establish `h1` using `psM_inf_herm T μ hμ hx hH hHh`. Establish `e1 : Complex.I • A * x + x * (Complex.I • A) = Complex.I • (A * x + x * A)`. Rewrite using `[smul_mul_assoc, mul_smul_comm, smul_add]`.

Rewrite `h1` using `[e1]`. Establish `hs : fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A) = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A)`. Apply `smul_cancel_lemma Complex.I_ne_zero` to reduce the goal to its premises. Simplify `h1` using `only [map_smul, map_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_neg]`. Establish `hd : fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x) = psM T μ x * T.dτ A - T.dτ A * psM T μ x`.

Rewrite using `[← map_sub]`. Conclude with `infR_conj T μ hx hA`. Prove the components needed by the constructor for the conclusion. Apply `smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)` to reduce the goal to its premises. Rewrite using `[two_smul, two_smul]`.

Combine the equalities or inequalities in the displayed calculation. Apply `smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)` to reduce the goal to its premises. Rewrite using `[two_smul, two_smul]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma infR_skew (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    fderiv ℂ (psM T μ) x (x * A) = -(T.dτ A * psM T μ x) ∧
      fderiv ℂ (psM T μ) x (A * x) = -(psM T μ x * T.dτ A) := by
  obtain ⟨hAs, hAb⟩ := (inK_iff ε A).1 hA
  have hH : IsBlock ε (Complex.I • A) := by
    intro i j hij
    rw [Matrix.smul_apply, hAb i j hij, smul_zero]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hHh : (Complex.I • A)ᴴ = Complex.I • A := by
    rw [Matrix.conjTranspose_smul, hAs, hI, neg_smul_neg]
  have h1 := psM_inf_herm T μ hμ hx hH hHh
  have e1 : Complex.I • A * x + x * (Complex.I • A) = Complex.I • (A * x + x * A) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_add]
  rw [e1] at h1

  have hs : fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A) =
      -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) := by
    apply smul_cancel_lemma Complex.I_ne_zero
    simpa only [map_smul, map_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_neg] using h1

  have hd : fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x) =
      psM T μ x * T.dτ A - T.dτ A * psM T μ x := by
    rw [← map_sub]
    exact infR_conj T μ hx hA
  constructor
  · apply smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)
    rw [two_smul, two_smul]
    calc fderiv ℂ (psM T μ) x (x * A) + fderiv ℂ (psM T μ) x (x * A)
        = (fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A)) +
          (fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x)) := by abel
      _ = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) +
          (psM T μ x * T.dτ A - T.dτ A * psM T μ x) := by rw [hs, hd]
      _ = -(T.dτ A * psM T μ x) + -(T.dτ A * psM T μ x) := by abel
  · apply smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)
    rw [two_smul, two_smul]
    calc fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (A * x)
        = (fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A)) -
          (fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x)) := by abel
      _ = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) -
          (psM T μ x * T.dτ A - T.dτ A * psM T μ x) := by rw [hs, hd]
      _ = -(psM T μ x * T.dτ A) + -(psM T μ x * T.dτ A) := by abel

/- English proof (translation)
Take `⟨A, B, hA, hB, rfl, -⟩` from `block_decomp hY`. Establish `hA'` using `infR_skew T μ hμ hx hA`. Establish `hB'` using `infR_skew T μ hμ hx hB`. Prove the components needed by the constructor for the conclusion. Simplify using `only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_smul, hA'.1, hB'.1, neg_add, smul_neg]`.

Simplify using `only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_smul, hA'.2, hB'.2, neg_add, smul_neg]`.
-/
theorem psM_inf_right (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsBlock ε Y) :
    fderiv ℂ (psM T μ) x (x * Y) = -(T.dτ Y * psM T μ x) ∧
      fderiv ℂ (psM T μ) x (Y * x) = -(psM T μ x * T.dτ Y) := by

  obtain ⟨A, B, hA, hB, rfl, -⟩ := block_decomp hY
  have hA' := infR_skew T μ hμ hx hA
  have hB' := infR_skew T μ hμ hx hB
  constructor
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_smul, hA'.1, hB'.1,
      neg_add, smul_neg]
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_smul, hA'.2, hB'.2,
      neg_add, smul_neg]

end ReciprocityTheory.ChartRestriction.DS.S7
