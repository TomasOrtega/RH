import Formalism.HermitianCurvature.HermitianCurvatureProofs.MrelConjTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [Glev, B2.UWb, Fin.val_last]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, fun a => h2 a a.isLt⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, fun a _ => h2 a⟩`.
-/
theorem glev_last_eq (r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  simp only [Glev, B2.UWb, Fin.val_last]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => h2 a a.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a _ => h2 a⟩

/- English proof (translation)
Rewrite using `[glev_last_eq, glev_last_eq, Formalism.FourierDecayAlt.P.LongWeylElement.uWbRec k ρ]`.
-/
theorem image_glev : ιLev k 1 ρ '' Glev k ρ (Fin.last ρ) = Glev k (1 + ρ) (Fin.last (1 + ρ)) := by
  rw [glev_last_eq, glev_last_eq, Formalism.FourierDecayAlt.P.LongWeylElement.uWbRec k ρ]

/- English proof (translation)
Rewrite `hμs`, `hμ` using `[glev_last_eq]`. Establish `hU` using `Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k ρ`. Take `⟨_, hν⟩` from `Formalism.FourierDecayAlt.P.levi_haar_measure_exists k ρ _ μs hU hμs`. Establish `e : ιLev k 1 ρ '' B2.UWb k ρ = B2.UWb k (1 + ρ)`. Rewrite using `[← glev_last_eq, ← glev_last_eq, image_glev]`.

Rewrite `hν` using `[e]`. Conclude with `Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (1 + ρ) _ μ _ (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k (1 + ρ)) hμ hν.conc hν.left hν.finite_compact`.
-/
theorem map_levM_smul {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs) :
    ∃ c : NNReal, μs.map (B2.levM k ρ) = c • μ := by
  rw [glev_last_eq] at hμs hμ
  have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k ρ
  obtain ⟨_, hν⟩ := Formalism.FourierDecayAlt.P.levi_haar_measure_exists k ρ _ μs hU hμs
  have e : ιLev k 1 ρ '' B2.UWb k ρ = B2.UWb k (1 + ρ) := by
    rw [← glev_last_eq, ← glev_last_eq, image_glev]
  rw [e] at hν
  exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (1 + ρ) _ μ _ (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k (1 + ρ)) hμ hν.conc
    hν.left hν.finite_compact

/- English proof (translation)
Establish `hf : ∀ (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ), fvec k r v (Fin.last r) = v` using `fun r v => by`. Simplify using `[fvec]`. Express the relevant statement in the definitionally equal form `herm (Hpk k (1 + ρ)) (ιLev k 1 ρ (Matrix.of x) *ᵥ fvec k (1 + ρ) (liftVec k 1 ρ z') (Fin.last (1 + ρ))) (fvec k (1 + ρ) (liftVec k 1 ρ z) (Fin.last (1 + ρ))) = herm (Hpk k ρ) (Matrix.of x *ᵥ fvec k ρ z' (Fin.last ρ)) (fvec k ρ z (Fin.last ρ))`. Rewrite using `[hf, hf, hf, hf, Formalism.FourierDecayAlt.P.B2x5.lev_lift, Formalism.FourierDecayAlt.P.B2x4.herm_lift]`.
-/
theorem zeta_levM (z z' : Fin (2 * ρ + k + 1) → ℂ) (x : Mt k ρ) :
    zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of (B2.levM k ρ x)) =
      zetaL k ρ z z' (Fin.last ρ) (Matrix.of x) := by
  have hf : ∀ (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ), fvec k r v (Fin.last r) = v := fun r v => by
    simp [fvec]
  change herm (Hpk k (1 + ρ)) (ιLev k 1 ρ (Matrix.of x) *ᵥ fvec k (1 + ρ) (liftVec k 1 ρ z') (Fin.last (1 + ρ)))
      (fvec k (1 + ρ) (liftVec k 1 ρ z) (Fin.last (1 + ρ))) =
    herm (Hpk k ρ) (Matrix.of x *ᵥ fvec k ρ z' (Fin.last ρ)) (fvec k ρ z (Fin.last ρ))
  rw [hf, hf, hf, hf, Formalism.FourierDecayAlt.P.B2x5.lev_lift, Formalism.FourierDecayAlt.P.B2x4.herm_lift]

/- English proof (translation)
Conclude with `(Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ).measurable`.
-/
theorem measurable_levM : Measurable (B2.levM k ρ) := by
  exact (Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ).measurable

/- English proof (translation)
Conclude with `(LinearMap.continuous_of_finiteDimensional (Formalism.FourierDecayAlt.P.Qx5.zetaLin k r z z' (Fin.last r))).comp continuous_id`.
-/
theorem continuous_zetaL (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => zetaL k r z z' (Fin.last r) (Matrix.of x) := by
  exact (LinearMap.continuous_of_finiteDimensional (Formalism.FourierDecayAlt.P.Qx5.zetaLin k r z z' (Fin.last r))).comp continuous_id

/- English proof (translation)
Take `⟨c, hc⟩` from `map_levM_smul hμ hμs`. Establish `key : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → c • ∫⁻ ζ, wt ζ * ψ ζ = ∫⁻ ζ, wt ζ * ψ ζ`. Introduce `ψ hψ`. Establish `hm : Measurable fun y : Mt k (1 + ρ) => ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of y))` using `hψ.comp (continuous_zetaL (1 + ρ) _ _).measurable`. Rewrite using `[← hlaw ψ hψ, ← lintegral_smul_measure, ← hc, lintegral_map hm measurable_levM]`.

Repeatedly rewrite using `[zeta_levM]`. Rewrite using `[hlaws ψ hψ, hlaw ψ hψ]`. Distinguish the cases in `hR : ∃ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ ≠ 0`. Take `⟨R, hR⟩` from `hR`. Establish `hψ : Measurable ((Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞))` using `measurable_one.indicator Metric.isClosed_closedBall.measurableSet`.

Establish `h1` using `key _ hψ`. Establish `e : ∫⁻ ζ, wt ζ * (Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) ζ = ∫⁻ ζ in Metric.closedBall 0 R, wt ζ`. Rewrite using `[← lintegral_indicator Metric.isClosed_closedBall.measurableSet]`. Use `congr 1`. Use function extensionality and compare the values at `ζ`.

Apply the tactic sequence `by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R <;> simp [hζ]`. Rewrite `h1` using `[e, ENNReal.smul_def]`. Establish `h2 : (c : ℝ≥0∞) * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ = 1 * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ`. Rewrite using `[one_mul]`. Conclude with `h1`.

Establish `hc1 : (c : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj hR (hfin R).ne).mp h2`. Rewrite using `[hc, ENNReal.coe_eq_one.mp hc1, one_smul]`. Use `push_neg at hR`. Establish `h0 : ∫⁻ ζ, wt ζ = 0`. Rewrite using `[← setLIntegral_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ)]`.

Use `le_antisymm ((lintegral_iUnion_le _ _).trans ?_) zero_le'` and prove the remaining obligations. Simplify using `[hR]`. Establish `hμ0 : μ = 0`. Establish `h3` using `hlaw (fun _ => 1) measurable_const`. Simplify using `only [mul_one, h0, lintegral_const, one_mul] at h3`.

Conclude with `Measure.measure_univ_eq_zero.mp h3`. Establish `hμs0 : μs = 0`. Establish `h3` using `hlaws (fun _ => 1) measurable_const`. Simplify using `only [mul_one, h0, lintegral_const, one_mul] at h3`. Conclude with `Measure.measure_univ_eq_zero.mp h3`.

Rewrite using `[hμ0, hμs0, Measure.map_zero]`.
-/
theorem map_levM_eq {z z' : Fin (2 * ρ + k + 1) → ℂ} {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (wt : ℂ → ℝ≥0∞) (hfin : ∀ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ < (⊤ : ℝ≥0∞))
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, wt ζ * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ z z' (Fin.last ρ) (Matrix.of x)) ∂μs = ∫⁻ ζ, wt ζ * ψ ζ) :
    μs.map (B2.levM k ρ) = μ := by
  obtain ⟨c, hc⟩ := map_levM_smul hμ hμs
  have key : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → c • ∫⁻ ζ, wt ζ * ψ ζ = ∫⁻ ζ, wt ζ * ψ ζ := by
    intro ψ hψ
    have hm : Measurable fun y : Mt k (1 + ρ) =>
        ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of y)) :=
      hψ.comp (continuous_zetaL (1 + ρ) _ _).measurable
    rw [← hlaw ψ hψ, ← lintegral_smul_measure, ← hc, lintegral_map hm measurable_levM]
    simp_rw [zeta_levM]
    rw [hlaws ψ hψ, hlaw ψ hψ]
  by_cases hR : ∃ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ ≠ 0
  · obtain ⟨R, hR⟩ := hR
    have hψ : Measurable ((Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞)) :=
      measurable_one.indicator Metric.isClosed_closedBall.measurableSet
    have h1 := key _ hψ
    have e : ∫⁻ ζ, wt ζ * (Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) ζ =
        ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
      congr 1
      funext ζ
      by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R <;> simp [hζ]
    rw [e, ENNReal.smul_def] at h1
    have h2 : (c : ℝ≥0∞) * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ = 1 * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [one_mul]
      exact h1
    have hc1 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hR (hfin R).ne).mp h2
    rw [hc, ENNReal.coe_eq_one.mp hc1, one_smul]
  · push_neg at hR
    have h0 : ∫⁻ ζ, wt ζ = 0 := by
      rw [← setLIntegral_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ)]
      refine le_antisymm ((lintegral_iUnion_le _ _).trans ?_) zero_le'
      simp [hR]
    have hμ0 : μ = 0 := by
      have h3 := hlaw (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    have hμs0 : μs = 0 := by
      have h3 := hlaws (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    rw [hμ0, hμs0, Measure.map_zero]

end Formalism.FourierDecayAlt.P.PBH
