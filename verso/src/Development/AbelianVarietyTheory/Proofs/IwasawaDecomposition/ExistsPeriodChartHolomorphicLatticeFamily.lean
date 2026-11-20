import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodFrameOfHolomorphicLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixBoundaryExtensionMonodromyPosSemidefStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIntKernelPsdBlockNotPosDefStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodChartRescaleBallToUnitPolydiscStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor`. Take `⟨rk, d, ρ, P, τ, B, Δ, hρ, hρ1, hd, hrk, hP, hPdet, hτd, hτs, hτm, hB, hPH, hΔc, hΔp, hτΔ, hcl⟩` from `GlobalTheory.T.exists_periodFrame_of_holomorphicLatticeFamily n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor`. Take `⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩` from `GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha ρ τ B hρ hρ1 hτd hτs hτm`. Establish `hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 ρ)` using `fun j l => (hτ₀d j l).continuousOn`. Establish `hmv : ∀ (k : Fin a) (v : Fin g → ℤ), ((B k).map (Int.cast : ℤ → ℂ)).mulVec (fun j => (v j : ℂ)) = fun i => (((B k).mulVec v i : ℤ) : ℂ)`.

Introduce `k v`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct]`. Establish `htoric : (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef`. Assume the negation of the conclusion as `hnot`.

Take `⟨v, hv0, hvs, hBv⟩` from `GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef a g rk B hpsd hB hnot`. Use `hcl v hv0 hvs (fun z => (τ₀ z).mulVec (fun j => (v j : ℂ))) ?_ ?_` and prove the remaining obligations. Use `continuousOn_pi.2 fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `continuousOn_finset_sum _ fun l _ => (hcont j l).mul continuousOn_const`.

Introduce `s hs hz`. Rewrite using `[hτ₀e s hs hz, Matrix.add_mulVec]`. Establish `h0 : (∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)).mulVec (fun j => (v j : ℂ)) = 0`. Rewrite using `[Matrix.sum_mulVec]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.smul_mulVec, hmv, hBv k]`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[h0, add_zero]`. Establish `hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val = Δ (logExp a s)`.

Introduce `s hs hz`. Rewrite using `[← hτΔ s hs hz, hτ₀e s hs hz]`. Use extensionality with `⟨j, hj⟩ ⟨l, hl⟩`. Simplify using `[Matrix.sum_apply, hB _ j l (Or.inl hj)]`. Establish `heq` using `GlobalTheory.T.eqOn_ball_of_eqOn_punctPolydiscCoveringExp_image n a ρ _ (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val) Δ hρ1 (continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1) hΔc hagree`.

Establish `habel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef`. Introduce `z hz`. Establish `h1` using `hΔp z hz`. Rewrite `h1` using `[← heq z hz]`. Conclude with `h1`.

Take `⟨hPC, hY⟩` from `GlobalTheory.T.periodChart_rescale_ball_to_unitPolydisc n a g rk ha ρ τ₀ B hρ hρ1 hrk hτ₀d hτ₀s hpsd hB htoric habel`. Use `⟨rk, _, B, P, ρ, d, hρ, hρ1, hd, hPC, hP, hPdet, ?_⟩` and prove the remaining obligations. Introduce `s hs hz Hm hHm`. Establish `hnz : ∀ i : Fin a, logExp a s (Fin.castLE ha i) ≠ 0`. Introduce `i`.

Simplify using `only [logExp, Fin.coe_castLE, i.isLt, if_true]`. Conclude with `Complex.exp_ne_zero _`. Rewrite using `[hPH s hs hz Hm hHm, hY _ hnz]`. Use `congr 2`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram`.

Use `congr 1`. Rewrite using `[← GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period ha τ₀ B (logExp a s) (fun k => s (Fin.castLE ha k)) ?_]`. Rewrite using `[hτ₀e s hs hz]`. Both sides reduce to the same expression. Introduce `i`.

Simplify using `only [logExp, Fin.coe_castLE, i.isLt, if_true]`.
-/
theorem GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ d : ℝ), 0 < ρ ∧ ρ ≤ 1 ∧ 0 < d ∧ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ρ⁻¹ • logExp a s))⁻¹ := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨rk, d, ρ, P, τ, B, Δ, hρ, hρ1, hd, hrk, hP, hPdet, hτd, hτs, hτm, hB, hPH, hΔc, hΔp, hτΔ, hcl⟩ :=
    GlobalTheory.T.exists_periodFrame_of_holomorphicLatticeFamily n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ := GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha ρ τ B hρ hρ1 hτd hτs hτm
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 ρ) := fun j l => (hτ₀d j l).continuousOn
  have hmv : ∀ (k : Fin a) (v : Fin g → ℤ), ((B k).map (Int.cast : ℤ → ℂ)).mulVec (fun j => (v j : ℂ)) =
      fun i => (((B k).mulVec v i : ℤ) : ℂ) := by
    intro k v; ext i; simp [Matrix.mulVec, dotProduct]
  have htoric : (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix
      (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef := by
    by_contra hnot
    obtain ⟨v, hv0, hvs, hBv⟩ := GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef a g rk B hpsd hB hnot
    refine hcl v hv0 hvs (fun z => (τ₀ z).mulVec (fun j => (v j : ℂ))) ?_ ?_
    · refine continuousOn_pi.2 fun j => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact continuousOn_finset_sum _ fun l _ => (hcont j l).mul continuousOn_const
    · intro s hs hz
      rw [hτ₀e s hs hz, Matrix.add_mulVec]
      have h0 : (∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)).mulVec
          (fun j => (v j : ℂ)) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Matrix.smul_mulVec, hmv, hBv k]
        ext i; simp
      rw [h0, add_zero]
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val = Δ (logExp a s) := by
    intro s hs hz
    rw [← hτΔ s hs hz, hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hB _ j l (Or.inl hj)]
  have heq := GlobalTheory.T.eqOn_ball_of_eqOn_punctPolydiscCoveringExp_image n a ρ _
    (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val) Δ hρ1
    (continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1) hΔc hagree
  have habel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef := by
    intro z hz
    have h1 := hΔp z hz
    rw [← heq z hz] at h1
    exact h1
  obtain ⟨hPC, hY⟩ := GlobalTheory.T.periodChart_rescale_ball_to_unitPolydisc n a g rk ha ρ τ₀ B hρ hρ1 hrk hτ₀d hτ₀s hpsd hB htoric habel
  refine ⟨rk, _, B, P, ρ, d, hρ, hρ1, hd, hPC, hP, hPdet, ?_⟩
  intro s hs hz Hm hHm
  have hnz : ∀ i : Fin a, logExp a s (Fin.castLE ha i) ≠ 0 := by
    intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
    exact Complex.exp_ne_zero _
  rw [hPH s hs hz Hm hHm, hY _ hnz]
  congr 2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram
  congr 1
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period ha τ₀ B (logExp a s) (fun k => s (Fin.castLE ha k)) ?_]
  · rw [hτ₀e s hs hz]; rfl
  · intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
