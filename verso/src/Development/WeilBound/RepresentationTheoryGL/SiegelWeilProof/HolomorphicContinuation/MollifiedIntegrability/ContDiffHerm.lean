import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.RatBound

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Establish `hc : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => ((x a b : ℝ) : ℂ))` using `fun a b => Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin n → ℝ) a))`. Simplify using `only [herm]`. Use `push_cast`. Conclude with `(((hc i j).add (hc j i)).div_const 2).add ((contDiff_const.mul ((hc i j).sub (hc j i))).div_const 2)`.
-/
theorem contDiff_herm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (herm (n := n)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have hc : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => ((x a b : ℝ) : ℂ)) := fun a b =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin n → ℝ) a))
  simp only [herm]
  push_cast
  exact (((hc i j).add (hc j i)).div_const 2).add ((contDiff_const.mul ((hc i j).sub (hc j i))).div_const 2)

/- English proof (translation)
Introduce `n s hs p q N R`. Take `⟨hUo, hFc, -⟩` from `hB n s hs p q R`. Establish `hH : ContDiff ℝ (⊤ : ℕ∞) (cls s 0 p q R)`. Rewrite using `[cls_zero]`. Rewrite using `[contDiff_iff_contDiffAt]`.

Introduce `y`. Establish `h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Fr s p q R) (herm y)` using `((hFc.restrict_scalars ℝ).contDiffAt (hUo.mem_nhds (herm_mem_Ugood s hs y)))`. Conclude with `h1.comp y (contDiff_herm n).contDiffAt`. Take `⟨G, hGc, hG⟩` from `hT n (cls s 0 p q R) hH N`. Establish `hcls : ∀ z : ℂ, cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y`.

Introduce `z`. Use function extensionality and compare the values at `y`. Simplify using `only [cls, neg_zero, Complex.cpow_zero, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `set D := n * N with hD`.

Establish `hrat : ∀ i : ℕ, ∃ C : ℝ, ∀ y : E n, ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖ ≤ C * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2)` using `fun i => ratBound hC hI hB hL s hs (p + i) (q + i) N R`. Use `choose Ci hCi using hrat`. Take `⟨CL, hCL⟩` from `hLg D`. Use `set Cm : ℝ := ∑ i ∈ Finset.range (D + 1), |Ci i| with hCm`. Use `⟨D + 1, fun j => Polynomial.X ^ (j : ℕ), fun j => G j, fun j => (hGc j).continuous, ⟨CL * Cm, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `j y`. Establish `hdp` using `dP_pos y`. Establish `hval : ∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y‖ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2)`. Introduce `i hi`. Establish `e1` using `hG (i : ℂ) y`.

Rewrite `e1` using `[← hcls, cls_nat s hs i p q R]`. Establish `hne : (((dP y : ℝ) : ℂ)) ^ (-(i : ℂ)) ≠ 0`. Rewrite using `[Complex.cpow_neg, Complex.cpow_natCast]; exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hdp.ne'))`. Establish `e2 : ∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y = (((dP y : ℝ) : ℂ)) ^ i * (Delta^[N] (cls s 0 (p + i) (q + i) R)) y`. Rewrite using `[e1, Complex.cpow_neg, Complex.cpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hdp.ne')), one_mul]`.

Rewrite using `[e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdp.le]`. Establish `hb` using `hCi i y`. Establish `hCi_le : |Ci i| ≤ Cm`. Rewrite using `[hCm]`. Conclude with `Finset.single_le_sum (f := fun i => |Ci i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hdp]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCi_le) (Real.rpow_nonneg hdp.le _)`. Use `hCL (fun j => G j y) _ hval j (Nat.lt_succ_iff.1 j.2)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce `z y`. Rewrite using `[hcls z, hG z y]`.

Use `congr 1`. Rewrite using `[Finset.sum_range (fun j => z ^ j * G j y)]`. Simplify using `[Polynomial.eval_pow, Polynomial.eval_X]`.
-/
theorem clsGainB_of (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (hT : Twist) (hLg : Lagr) : ClsGain := by
  intro n s hs p q N R
  obtain ⟨hUo, hFc, -⟩ := hB n s hs p q R
  have hH : ContDiff ℝ (⊤ : ℕ∞) (cls s 0 p q R) := by
    rw [cls_zero]
    rw [contDiff_iff_contDiffAt]
    intro y
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Fr s p q R) (herm y) :=
      ((hFc.restrict_scalars ℝ).contDiffAt (hUo.mem_nhds (herm_mem_Ugood s hs y)))
    exact h1.comp y (contDiff_herm n).contDiffAt
  obtain ⟨G, hGc, hG⟩ := hT n (cls s 0 p q R) hH N
  have hcls : ∀ z : ℂ, cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y := by
    intro z; funext y; simp only [cls, neg_zero, Complex.cpow_zero, one_mul]; ring
  set D := n * N with hD
  have hrat : ∀ i : ℕ, ∃ C : ℝ, ∀ y : E n,
      ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖ ≤ C * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2) :=
    fun i => ratBound hC hI hB hL s hs (p + i) (q + i) N R
  choose Ci hCi using hrat
  obtain ⟨CL, hCL⟩ := hLg D
  set Cm : ℝ := ∑ i ∈ Finset.range (D + 1), |Ci i| with hCm
  refine ⟨D + 1, fun j => Polynomial.X ^ (j : ℕ), fun j => G j, fun j => (hGc j).continuous, ⟨CL * Cm, ?_⟩, ?_⟩
  · intro j y
    have hdp := dP_pos y
    have hval : ∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y‖ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
      intro i hi
      have e1 := hG (i : ℂ) y
      rw [← hcls, cls_nat s hs i p q R] at e1
      have hne : (((dP y : ℝ) : ℂ)) ^ (-(i : ℂ)) ≠ 0 := by
        rw [Complex.cpow_neg, Complex.cpow_natCast]; exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hdp.ne'))
      have e2 : ∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y =
          (((dP y : ℝ) : ℂ)) ^ i * (Delta^[N] (cls s 0 (p + i) (q + i) R)) y := by
        rw [e1, Complex.cpow_neg, Complex.cpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hdp.ne')), one_mul]
      rw [e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdp.le]
      have hb := hCi i y
      have hCi_le : |Ci i| ≤ Cm := by
        rw [hCm]
        exact Finset.single_le_sum (f := fun i => |Ci i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      calc dP y ^ i * ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖
          ≤ dP y ^ i * (Ci i * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg hdp.le _)
        _ = Ci i * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
            rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hdp]
            congr 2; push_cast; ring
        _ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCi_le) (Real.rpow_nonneg hdp.le _)
    have := hCL (fun j => G j y) _ hval j (Nat.lt_succ_iff.1 j.2)
    simpa [mul_assoc] using this
  · intro z y
    rw [hcls z, hG z y]
    congr 1
    rw [Finset.sum_range (fun j => z ^ j * G j y)]
    simp [Polynomial.eval_pow, Polynomial.eval_X]

end PositivityTheory.Rg.Sw.WR.K.GB
