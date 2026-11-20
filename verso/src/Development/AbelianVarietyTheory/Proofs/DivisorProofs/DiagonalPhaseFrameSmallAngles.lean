import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.RiemConst

/- English proof (translation)
Establish `h` using `Complex.norm_mul_exp_arg_mul_I (Complex.exp (Complex.I * (t : ℂ)))`. Establish `h1 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1`. Rewrite using `[mul_comm]`. Conclude with `Complex.norm_exp_ofReal_mul_I t`. Rewrite `h` using `[h1]`.

Simplify `h` using `[mul_comm]`.
-/
lemma exp_I_arg_exp_I (t : ℝ) :
    Complex.exp (Complex.I * ((Complex.exp (Complex.I * (t : ℂ))).arg : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) := by
  have h := Complex.norm_mul_exp_arg_mul_I (Complex.exp (Complex.I * (t : ℂ)))
  have h1 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I t
  rw [h1] at h
  simpa [mul_comm] using h

/- English proof (translation)
Use `push_cast`. Rewrite using `[mul_neg, Complex.exp_neg, Finset.mul_sum, Complex.exp_sum]`.
-/
lemma exp_I_neg_sum {n : ℕ} (f : Fin n → ℝ) :
    Complex.exp (Complex.I * ((-∑ k, f k : ℝ) : ℂ)) =
      (∏ k, Complex.exp (Complex.I * (f k : ℂ)))⁻¹ := by
  push_cast
  rw [mul_neg, Complex.exp_neg, Finset.mul_sum, Complex.exp_sum]

/- English proof (translation)
Introduce `E _ Ψ r δ hδ`. Take `⟨η, hη, hcont⟩` from `Metric.continuousAt_iff.mp (Complex.continuousAt_arg (Complex.one_mem_slitPlane)) δ hδ`. Use `⟨η, hη, fun θ hθ => ?_⟩` and prove the remaining obligations. Use `⟨fun τ k => (Complex.exp (Complex.I * (θ τ k : ℂ))).arg, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pi_norm_lt_iff hδ]`.

Introduce `τ`. Rewrite using `[pi_norm_lt_iff hδ]`. Introduce `k`. Establish `hk` using `hθ τ (Fin.castLE (Nat.sub_le r 1) k)`. Apply the tactic sequence `have hentry : phaseFrame θ τ (Fin.castLE (Nat.sub_le r 1) k) (Fin.castLE (Nat.sub_le r 1) k) = Complex.exp (Complex.I * (θ τ k : ℂ)) := by`.

Simplify using `only [phaseFrame, Matrix.diagonal_apply_eq, angles, Fin.coe_castLE, k.isLt, dif_pos]`. Rewrite `hk` using `[hentry]`. Use `hcont (x := Complex.exp (Complex.I * (θ τ k : ℂ))) (by rwa [dist_eq_norm])` as an intermediate fact. Rewrite `this` using `[Complex.arg_one, Real.dist_eq, sub_zero]`. Simplify `this` using `[Real.norm_eq_abs]`.

Use function extensionality and compare the values at `τ`. Simplify using `only [phaseFrame]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Unfold `angles`.

Use `split_ifs with h`. Conclude with `exp_I_arg_exp_I _`. Rewrite using `[exp_I_neg_sum, exp_I_neg_sum]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun k _ => exp_I_arg_exp_I _`.
-/
theorem phaseFrame_small_angles : ∀ (E : Type) [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (δ : ℝ), 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ θ : Ψ → Fin (r - 1) → ℝ, (∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η) → ∃ θ' : Ψ → Fin (r - 1) → ℝ, ‖θ'‖ < δ ∧ phaseFrame θ' = phaseFrame θ := by
  intro E _ Ψ r δ hδ
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (Complex.continuousAt_arg (Complex.one_mem_slitPlane)) δ hδ
  refine ⟨η, hη, fun θ hθ => ?_⟩
  refine ⟨fun τ k => (Complex.exp (Complex.I * (θ τ k : ℂ))).arg, ?_, ?_⟩
  · rw [pi_norm_lt_iff hδ]
    intro τ
    rw [pi_norm_lt_iff hδ]
    intro k
    have hk := hθ τ (Fin.castLE (Nat.sub_le r 1) k)
    have hentry : phaseFrame θ τ (Fin.castLE (Nat.sub_le r 1) k) (Fin.castLE (Nat.sub_le r 1) k)
        = Complex.exp (Complex.I * (θ τ k : ℂ)) := by
      simp only [phaseFrame, Matrix.diagonal_apply_eq, angles, Fin.coe_castLE, k.isLt, dif_pos]
    rw [hentry] at hk
    have := hcont (x := Complex.exp (Complex.I * (θ τ k : ℂ))) (by rwa [dist_eq_norm])
    rw [Complex.arg_one, Real.dist_eq, sub_zero] at this
    simpa [Real.norm_eq_abs] using this
  · funext τ
    simp only [phaseFrame]
    congr 1
    funext a
    unfold angles
    split_ifs with h
    · exact exp_I_arg_exp_I _
    · rw [exp_I_neg_sum, exp_I_neg_sum]
      congr 1
      exact Finset.prod_congr rfl fun k _ => exp_I_arg_exp_I _

end GlobalTheory.RiemConst
