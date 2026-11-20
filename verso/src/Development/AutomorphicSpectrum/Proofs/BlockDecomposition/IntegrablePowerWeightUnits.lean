import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightRealStatement

open MeasureTheory

namespace GlobalTheory.CompanionTheory.RealTateConv

/- English proof (translation)
Introduce `q N hq hN`. Establish `h` using `GlobalTheory.T.integrable_power_weight_real (q - 1) N (by linarith) (by linarith)`. Set `g : ℝ → ℂ` to `fun x => ((|x| ^ q * (1 + |x|) ^ (-N) : ℝ) : ℂ)`. Establish `key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume`. Establish `hc : Integrable (fun x : ℝ => ((|x| ^ (q - 1) * (1 + |x|) ^ (-N) : ℝ) : ℂ)) volume` using `h.ofReal`.

Use `hc.congr ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx`. Establish `hpos : 0 < |x|` using `abs_pos.2 hx`. Simplify using `only [g]`. Rewrite using `[Real.rpow_sub_one hpos.ne', Complex.real_smul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `((integrable_mulR_iff g).2 key).re`. Simplify `h2` using `[g]`.
-/
theorem integrable_mulR_abs_rpow_mul_one_add_rpow_neg :
    ∀ (q N : ℝ), 0 < q → q < N →
      MeasureTheory.Integrable (fun a : ℝˣ => |(a : ℝ)| ^ q * (1 + |(a : ℝ)|) ^ (-N)) Ad3.mulR := by
  intro q N hq hN
  have h := GlobalTheory.T.integrable_power_weight_real (q - 1) N (by linarith) (by linarith)
  let g : ℝ → ℂ := fun x => ((|x| ^ q * (1 + |x|) ^ (-N) : ℝ) : ℂ)
  have key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
    have hc : Integrable (fun x : ℝ => ((|x| ^ (q - 1) * (1 + |x|) ^ (-N) : ℝ) : ℂ)) volume :=
      h.ofReal
    refine hc.congr ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
    have hpos : 0 < |x| := abs_pos.2 hx
    simp only [g]
    rw [Real.rpow_sub_one hpos.ne', Complex.real_smul]
    push_cast
    ring
  have h2 := ((integrable_mulR_iff g).2 key).re
  simpa [g] using h2

end GlobalTheory.CompanionTheory.RealTateConv
