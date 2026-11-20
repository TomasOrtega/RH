import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulNearOneLuSplitSmallChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPhaseFrameSmallAnglesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvSectionMulEntriesNearOneStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ r X x σ t ρ hx hρ hσ0 hσc hσB ht _ _ hstab δ hδ`. Take `⟨η, hη, hB⟩` from `GlobalTheory.T.diagonalPhaseFrame_small_angles E X.Ψ r δ hδ`. Establish `hσa : ContinuousAt σ 0` using `hσc.continuousAt (Metric.ball_mem_nhds 0 hρ)`. Take `⟨ε1, hε1, κ, hκ, hC⟩` from `GlobalTheory.T.exists_conj_inv_section_mul_entries_near_one E r X x σ hx hσ0 hσa η hη`. Take `⟨ε2, hε2, hA⟩` from `GlobalTheory.T.leftMul_near_one_lu_split_small_chart E r X x hx (min (min δ ρ) κ) (lt_min (lt_min hδ hρ) hκ)`.

Use `⟨min ε1 ε2, lt_min hε1 hε2, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hg1 : g ∈ grpBall (realSU X.Ψ X.Gm) ε1` using `fun τ a b => lt_of_lt_of_le (hg τ a b) (min_le_left _ _)`. Take `⟨z, hz, b, hb, hgx⟩` from `hA (fun τ => (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) (fun τ a c => lt_of_lt_of_le (hg τ a c) (min_le_right _ _))`. Establish `hz1 : ‖z‖ < δ` using `lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))`. Establish `hz2 : z ∈ Metric.ball (0 : V (nd X)) ρ`.

Rewrite using `[Metric.mem_ball, dist_zero_right]`. Conclude with `lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))`. Establish `hz3 : ‖z‖ < κ` using `lt_of_lt_of_le hz (min_le_right _ _)`. Take `⟨b', hb', hσx⟩` from `hσB z hz2`. Establish `hxu : ∀ τ, IsUnit (mat x τ)` using `fun τ => (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ))`.

Establish `hstep : ∃ b'' ∈ Bor X.Ψ r, X.lmulC (fun τ => (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b''`. Use `⟨fun τ => ((mat b' τ)⁻¹ * mat b τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_, ?_⟩` and prove the remaining obligations. Establish `hb'u : IsUnit (mat b' τ).det` using `isUnit_iff_ne_zero.2 (hb' τ).1`. Use `⟨?_, fun a c hca => ?_⟩` and prove the remaining obligations. Use `show ((mat b' τ)⁻¹ * mat b τ).det ≠ 0`.

Rewrite using `[Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `mul_ne_zero (inv_ne_zero (hb' τ).1) (hb τ).1`. Use `show ((mat b' τ)⁻¹ * mat b τ) a c = 0`. Use `letI := Matrix.invertibleOfIsUnitDet _ hb'u`. Establish `h1 : (mat b' τ)⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => (hb' τ).2 a c h)`.

Establish `h2 : (mat b τ).BlockTriangular id` using `fun a c h => (hb τ).2 a c h`. Conclude with `(h1.mul h2) hca`. Use function extensionality and compare the values at `τ`. Establish `hb'u : IsUnit (mat b' τ).det` using `isUnit_iff_ne_zero.2 (hb' τ).1`. Use `set S : GL (Fin r) ℂ := ((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hS`.

Use `set G : GL (Fin r) ℂ := ((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hG`. Establish `eM : ((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ) = S⁻¹ * G` using `rfl`. Establish `e1 : (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b' τ` using `congrFun hσx τ`. Establish `e2 : (G : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b τ` using `congrFun hgx τ`. Establish `e3 : mat x τ * mat (nmat X z) τ = (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ * (mat b' τ)⁻¹`.

Rewrite using `[e1, Matrix.mul_assoc (mat x τ * mat (nmat X z) τ), Matrix.mul_nonsing_inv _ hb'u, Matrix.mul_one]`. Use `show (((S⁻¹ * G : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) = mat x τ * ((mat b' τ)⁻¹ * mat b τ)`. Rewrite using `[Units.val_mul, Matrix.mul_assoc, e2, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc]`. Take `⟨θ, hθ⟩` from `hstab _ hstep`. Establish `hP : ∀ θ₀, ∀ τ, (mat x τ)⁻¹ * ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat (phaseFrame θ₀) τ`.

Introduce `θ₀ τ`. Establish `h1 : ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (phaseFrame θ₀) τ` using `congrFun (ht θ₀) τ`. Rewrite using `[Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hxu τ)), Matrix.one_mul]`. Establish `hph : ∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η`. Introduce `τ a`.

Establish `h` using `hC z hz3 g hg1 τ a a`. Rewrite `h` using `[hθ, hP θ τ]`. Simplify `h` using `[mat]`. Take `⟨θ', hθ', hPP⟩` from `hB θ hph`. Establish `htt : t θ' = t θ`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`. Apply `Units.ext` to reduce the goal to its premises. Establish `h1` using `congrFun ((ht θ').trans ((congrArg (rmul x) hPP).trans (ht θ).symm)) τ`. Conclude with `(hxu τ).mul_left_injective h1`.

Use `⟨(z, θ'), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Prod.norm_def]`. Conclude with `max_lt hz1 hθ'`. Use `show σ z * t θ' = g`. Rewrite using `[htt, ← hθ, mul_inv_cancel_left]`.
-/
theorem eq_chart_mul_of_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), IsOrth X x → 0 < ρ → σ 0 = 1 → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∃ w : ChartSp X, ‖w‖ < δ ∧ σ w.1 * t w.2 = g := by
  intro E _ _ _ r X x σ t ρ hx hρ hσ0 hσc hσB ht _ _ hstab δ hδ
  obtain ⟨η, hη, hB⟩ := GlobalTheory.T.diagonalPhaseFrame_small_angles E X.Ψ r δ hδ
  have hσa : ContinuousAt σ 0 := hσc.continuousAt (Metric.ball_mem_nhds 0 hρ)
  obtain ⟨ε1, hε1, κ, hκ, hC⟩ := GlobalTheory.T.exists_conj_inv_section_mul_entries_near_one E r X x σ hx hσ0 hσa η hη
  obtain ⟨ε2, hε2, hA⟩ := GlobalTheory.T.leftMul_near_one_lu_split_small_chart E r X x hx (min (min δ ρ) κ) (lt_min (lt_min hδ hρ) hκ)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun g hg => ?_⟩
  have hg1 : g ∈ grpBall (realSU X.Ψ X.Gm) ε1 := fun τ a b => lt_of_lt_of_le (hg τ a b) (min_le_left _ _)
  obtain ⟨z, hz, b, hb, hgx⟩ := hA (fun τ => (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
    (fun τ a c => lt_of_lt_of_le (hg τ a c) (min_le_right _ _))
  have hz1 : ‖z‖ < δ := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
  have hz2 : z ∈ Metric.ball (0 : V (nd X)) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
  have hz3 : ‖z‖ < κ := lt_of_lt_of_le hz (min_le_right _ _)
  obtain ⟨b', hb', hσx⟩ := hσB z hz2
  have hxu : ∀ τ, IsUnit (mat x τ) := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ))

  have hstep : ∃ b'' ∈ Bor X.Ψ r, X.lmulC (fun τ => (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b'' := by
    refine ⟨fun τ => ((mat b' τ)⁻¹ * mat b τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_, ?_⟩
    · have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      refine ⟨?_, fun a c hca => ?_⟩
      · show ((mat b' τ)⁻¹ * mat b τ).det ≠ 0
        rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
        exact mul_ne_zero (inv_ne_zero (hb' τ).1) (hb τ).1
      · show ((mat b' τ)⁻¹ * mat b τ) a c = 0
        letI := Matrix.invertibleOfIsUnitDet _ hb'u
        have h1 : (mat b' τ)⁻¹.BlockTriangular id :=
          Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => (hb' τ).2 a c h)
        have h2 : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
        exact (h1.mul h2) hca
    · funext τ
      have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      set S : GL (Fin r) ℂ := ((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hS
      set G : GL (Fin r) ℂ := ((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hG
      have eM : ((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ) = S⁻¹ * G := rfl
      have e1 : (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b' τ := congrFun hσx τ
      have e2 : (G : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b τ := congrFun hgx τ
      have e3 : mat x τ * mat (nmat X z) τ = (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ * (mat b' τ)⁻¹ := by
        rw [e1, Matrix.mul_assoc (mat x τ * mat (nmat X z) τ), Matrix.mul_nonsing_inv _ hb'u, Matrix.mul_one]
      show (((S⁻¹ * G : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) =
        mat x τ * ((mat b' τ)⁻¹ * mat b τ)
      rw [Units.val_mul, Matrix.mul_assoc, e2, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc]
  obtain ⟨θ, hθ⟩ := hstab _ hstep
  have hP : ∀ θ₀, ∀ τ, (mat x τ)⁻¹ * ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat (phaseFrame θ₀) τ := by
    intro θ₀ τ
    have h1 : ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (phaseFrame θ₀) τ := congrFun (ht θ₀) τ
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hxu τ)), Matrix.one_mul]
  have hph : ∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η := by
    intro τ a
    have h := hC z hz3 g hg1 τ a a
    rw [hθ, hP θ τ] at h
    simpa [mat] using h
  obtain ⟨θ', hθ', hPP⟩ := hB θ hph
  have htt : t θ' = t θ := by
    apply Subtype.ext; funext τ; apply Units.ext
    have h1 := congrFun ((ht θ').trans ((congrArg (rmul x) hPP).trans (ht θ).symm)) τ
    exact (hxu τ).mul_left_injective h1
  refine ⟨(z, θ'), ?_, ?_⟩
  · rw [Prod.norm_def]; exact max_lt hz1 hθ'
  · show σ z * t θ' = g
    rw [htt, ← hθ, mul_inv_cancel_left]

end GlobalTheory
