import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.SUVol

/- English proof (translation)
Introduce `E _ _ _ r X x σ hx hσ0 hσc η hη`. Set `One : X.Ψ → Fin r → Fin r → ℂ` to `fun _ a b => (1 : Matrix (Fin r) (Fin r) ℂ) a b`. Set `F : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) → (X.Ψ → Fin r → Fin r → ℂ)` to `fun PQ τ => (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ`. Establish `hFc : Continuous F`. Use `continuous_pi fun τ => ?_` and prove the remaining obligations.

Establish `h1 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) => Matrix.of (PQ.1 τ)` using `(continuous_apply τ).comp continuous_fst`. Establish `h2 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) => Matrix.of (PQ.2 τ)` using `(continuous_apply τ).comp continuous_snd`. Use `show Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) => (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ`. Conclude with `(continuous_const.matrix_mul (h1.matrix_mul h2)).matrix_mul continuous_const`. Establish `hF1 : F (One, One) = One`.

Use function extensionality and compare the values at `τ`. Establish `hu : IsUnit (mat x τ).det` using `isUnit_iff_ne_zero.mpr (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ)`. Establish `h1 : Matrix.of (One τ) = 1` using `rfl`. Use `show (mat x τ)⁻¹ * (Matrix.of (One τ) * Matrix.of (One τ)) * mat x τ = Matrix.of (One τ)`. Rewrite using `[h1, Matrix.mul_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]`.

Take `⟨δ, hδ, hδF⟩` from `Metric.continuousAt_iff.1 hFc.continuousAt (ε := η) hη`. Rewrite `hδF` using `[hF1]`. Set `A : V (nd X) → (X.Ψ → Fin r → Fin r → ℂ)` to `fun z τ => ((((σ z)⁻¹ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)`. Establish `hAc : ContinuousAt A 0`. Use `continuousAt_pi.2 fun τ => ?_` and prove the remaining obligations.

Establish `: ContinuousAt (fun z => (σ z)⁻¹) 0` using `ContinuousAt.comp (f := σ) continuous_inv.continuousAt hσc`. Conclude with `(Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).continuousAt.comp this`. Establish `hA0 : A 0 = One`. Use function extensionality and compare the values at `τ`. Simplify using `only [A, One, hσ0, inv_one]`.

Both sides reduce to the same expression. Take `⟨κ, hκ, hκA⟩` from `Metric.continuousAt_iff.1 hAc (ε := δ) hδ`. Rewrite `hκA` using `[hA0]`. Use `⟨δ, hδ, κ, hκ, fun z hz g hg τ a b => ?_⟩` and prove the remaining obligations. Set `B : X.Ψ → Fin r → Fin r → ℂ` to `fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)`.

Establish `hzA : dist (A z) One < δ` using `hκA (by simpa [dist_zero_right] using hz)`. Establish `hgB : dist B One < δ`. Use `(dist_pi_lt_iff hδ).2 fun τ => (dist_pi_lt_iff hδ).2 fun a => (dist_pi_lt_iff hδ).2 fun b => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm]`. Conclude with `hg τ a b`.

Establish `hPQ : dist (A z, B) (One, One) < δ`. Rewrite using `[Prod.dist_eq]`. Conclude with `max_lt hzA hgB`. Establish `hout` using `hδF hPQ`. Establish `hent : dist (F (A z, B) τ a b) (One τ a b) < η` using `lt_of_le_of_lt ((dist_le_pi_dist _ _ b).trans ((dist_le_pi_dist _ _ a).trans (dist_le_pi_dist _ _ τ))) hout`.

Rewrite `hent` using `[dist_eq_norm]`. Use `hent using 3` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals rfl`.
-/
theorem conj_inv_section_mul_entries_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm), IsOrth X x → σ 0 = 1 → ContinuousAt σ 0 → ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ z : V (nd X), ‖z‖ < κ → ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∀ τ a b, ‖((mat x τ)⁻¹ * (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < η := by
  intro E _ _ _ r X x σ hx hσ0 hσc η hη
  classical
  let One : X.Ψ → Fin r → Fin r → ℂ := fun _ a b => (1 : Matrix (Fin r) (Fin r) ℂ) a b
  let F : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) → (X.Ψ → Fin r → Fin r → ℂ) :=
    fun PQ τ => (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ
  have hFc : Continuous F := by
    refine continuous_pi fun τ => ?_
    have h1 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
        Matrix.of (PQ.1 τ) :=
      (continuous_apply τ).comp continuous_fst
    have h2 : Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
        Matrix.of (PQ.2 τ) :=
      (continuous_apply τ).comp continuous_snd
    show Continuous fun PQ : (X.Ψ → Fin r → Fin r → ℂ) × (X.Ψ → Fin r → Fin r → ℂ) =>
      (mat x τ)⁻¹ * (Matrix.of (PQ.1 τ) * Matrix.of (PQ.2 τ)) * mat x τ
    exact (continuous_const.matrix_mul (h1.matrix_mul h2)).matrix_mul continuous_const
  have hF1 : F (One, One) = One := by
    funext τ
    have hu : IsUnit (mat x τ).det :=
      isUnit_iff_ne_zero.mpr (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ)
    have h1 : Matrix.of (One τ) = 1 := rfl
    show (mat x τ)⁻¹ * (Matrix.of (One τ) * Matrix.of (One τ)) * mat x τ = Matrix.of (One τ)
    rw [h1, Matrix.mul_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hFc.continuousAt (ε := η) hη
  rw [hF1] at hδF
  let A : V (nd X) → (X.Ψ → Fin r → Fin r → ℂ) := fun z τ =>
    ((((σ z)⁻¹ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)
  have hAc : ContinuousAt A 0 := by
    refine continuousAt_pi.2 fun τ => ?_
    have : ContinuousAt (fun z => (σ z)⁻¹) 0 := ContinuousAt.comp (f := σ) continuous_inv.continuousAt hσc
    exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).continuousAt.comp this
  have hA0 : A 0 = One := by
    funext τ
    simp only [A, One, hσ0, inv_one]
    rfl
  obtain ⟨κ, hκ, hκA⟩ := Metric.continuousAt_iff.1 hAc (ε := δ) hδ
  rw [hA0] at hκA
  refine ⟨δ, hδ, κ, hκ, fun z hz g hg τ a b => ?_⟩
  let B : X.Ψ → Fin r → Fin r → ℂ := fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)
  have hzA : dist (A z) One < δ := hκA (by simpa [dist_zero_right] using hz)
  have hgB : dist B One < δ := by
    refine (dist_pi_lt_iff hδ).2 fun τ => (dist_pi_lt_iff hδ).2 fun a => (dist_pi_lt_iff hδ).2 fun b => ?_
    rw [dist_eq_norm]
    exact hg τ a b
  have hPQ : dist (A z, B) (One, One) < δ := by
    rw [Prod.dist_eq]; exact max_lt hzA hgB
  have hout := hδF hPQ
  have hent : dist (F (A z, B) τ a b) (One τ a b) < η :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ b).trans ((dist_le_pi_dist _ _ a).trans (dist_le_pi_dist _ _ τ))) hout
  rw [dist_eq_norm] at hent
  convert hent using 3
  all_goals rfl

end GlobalTheory.SUVol
