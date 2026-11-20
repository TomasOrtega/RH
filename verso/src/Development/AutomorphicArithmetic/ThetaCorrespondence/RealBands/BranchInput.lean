import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealInputOfBranching
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchSmooth
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchVol

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

/- English proof (translation)
Unfold `big`. Establish `hn : (1 : ℝ) ≤ (n : ℝ) + 1`. Use `Nat.cast_nonneg (α := ℝ) n` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h8 : (2 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B` using `by nlinarith`.

Establish `hlog : Real.log 2 ≤ Real.log (8 * ((n : ℝ) + 1) * B)` using `Real.log_le_log (by norm_num) h8`. Establish `hlog0 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B)` using `le_trans (Real.log_nonneg (by norm_num)) hlog`. Establish `hp : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 4` using `one_le_pow₀ hn`. Establish `hx : Real.log 2 ≤ 1 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B)`. Rewrite using `[one_mul]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem two_le_big_one (n : ℕ) {B : ℝ} (hB : 1 ≤ B) : 2 ≤ big 1 n B := by
  unfold big
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h8 : (2 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  have hlog : Real.log 2 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_le_log (by norm_num) h8
  have hlog0 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := le_trans (Real.log_nonneg (by norm_num)) hlog
  have hp : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 4 := one_le_pow₀ hn
  have hx : Real.log 2 ≤ 1 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B) := by
    rw [one_mul]
    nlinarith
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ _ := Real.exp_le_exp.2 hx

/- English proof (translation)
Establish `hc0 : 0 ≤ c` using `le_trans (by positivity) hc`. Establish `hr2 : 1 ≤ (b₂ * r) ^ 2` using `one_le_pow₀ hr`. Combine the equalities or inequalities in the displayed calculation. Apply `div_le_div_of_nonneg_right _ hd.le` to reduce the goal to its premises. Conclude with `le_mul_of_one_le_right hb₁.le hr2`.

Use `_ = b₁ * b₂ * b₂ * 2 * (r ^ 2 / (2 * d)) := by`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ b₁ * b₂ * b₂ * b₃ * c := by`. Apply `mul_le_mul (mul_le_mul_of_nonneg_left hb₃ (by positivity)) hc (by positivity)` to reduce the goal to its premises. Establish `: (0 : ℝ) ≤ b₃` using `by linarith`.

Check the signs of the components of the expression.
-/
private theorem vol_arith {V d r c b₁ b₂ b₃ : ℝ} (hd : 0 < d) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 2 ≤ b₃)
    (hV : V ≤ b₁ / d) (hr : 1 ≤ b₂ * r) (hc : r ^ 2 / (2 * d) ≤ c) : V ≤ b₁ * b₂ * b₂ * b₃ * c := by
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  have hr2 : 1 ≤ (b₂ * r) ^ 2 := one_le_pow₀ hr
  calc V ≤ b₁ / d := hV
    _ ≤ b₁ * (b₂ * r) ^ 2 / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact le_mul_of_one_le_right hb₁.le hr2
    _ = b₁ * b₂ * b₂ * 2 * (r ^ 2 / (2 * d)) := by
        field_simp
    _ ≤ b₁ * b₂ * b₂ * b₃ * c := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hb₃ (by positivity)) hc (by positivity)
        have : (0 : ℝ) ≤ b₃ := by linarith
        positivity

open GlobalTheory.SepReal.RealAsm in
/- English proof (translation)
Introduce `hPL hEM`. Unfold `ProjLarge at hPL`. Unfold `EigMap at hEM`. Take `⟨C1, hC1, hIB⟩` from `GlobalTheory.T.translateCoefficientIntegralBounds_of_unitary_laws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws (GlobalTheory.T.boostDecompositionNormBound_of_embeddingLaws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws) (GlobalTheory.T.negativeNormPowerIntegrable_ …`. Take `⟨C3, hC3, hDB⟩` from `GlobalTheory.T.translateCoefficientDerivativeIntegralBounds_of_laws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound) GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay Gl …`.

Take `⟨C2, hC2, hVD⟩` from `volDeg`. Establish `hDR` using `GlobalTheory.T.formalDegree_loweringWeight_ratio_le`. Establish `hMS` using `mapSmooth`. Establish `hLBall` using `GlobalTheory.T.lowestKType_lieWord_normBound`. Unfold `ForPair at hPL hEM hIB hDB hVD hMS hDR`.

Unfold `DegRatio at hDR`. Unfold `MapSmooth at hMS`. Unfold `LieBound ForDS at hLBall`. Unfold `RealInputE ForPair`. Use `⟨C1 + C3 + C2 + 201, by linarith, ?_⟩` and prove the remaining obligations.

Introduce `n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ`. Establish `hB : 1 ≤ B` using `one_le_B hpar`. Take `⟨⟨v₀, hv₀⟩, -, -⟩` from `GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree (n + 1) ε lam H π hπ`. Take `⟨j, P, hjP, g₀, hg₀, hg₀n, hbig⟩` from `hPL n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀`. Take `⟨d', hd'⟩` from `(hDR n e ε lam ε' mu B hpar H H' π σ hπ hσ).1`.

Take `⟨⟨w₀, hw₀⟩, -, -⟩` from `GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree n ε' mu H' σ hσ`. Establish `hnn : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3`. Establish `h0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hgap' : GapAtLeast ε' mu (1000 * (n : ℝ) ^ 3)` using `gap_mono (by linarith) hpar.gap'`. Establish `hw₀int` using `integrable_low_coef GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound) ε' mu B hpar.three_le hpar.hmu hgap' hpar.bound.2 σ hσ w₀ hw₀`. Establish `hIBv` using `hIB n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n`. Establish `hvint : Integrable (fun h => ⟪π g₀ v₀, π (embH e (umat h)) (π g₀ v₀)⟫_ℂ) (muG ε')`. Establish `hi` using `(hIBv.1 1 (one_mem ε)).1`.

Simplify using `using hi`. Establish `hPv : P (π g₀ v₀) ≠ 0`. Introduce `h0`. Rewrite `hbig` using `[h0, norm_zero, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨w, c, T, hw0, hcP, hcoef, hT, hTv⟩` from `hEM n e ε lam ε' mu B hpar H H' π σ hπ hσ d' hd' w₀ hw₀.1 hw₀int j P hjP (π g₀ v₀) hvint hPv`. Establish `hd'pos : 0 < d'` using `hd'.1`. Establish `hPvpos : 0 < ‖P (π g₀ v₀)‖` using `norm_pos_iff.2 hPv`. Establish `hcpos : 0 < c` using `lt_of_lt_of_le (by positivity) hcP`. Establish `hLB` using `hLBall (n + 1) ε lam B (by have := hpar.three_le; omega) hpar.hlam (by push_cast; exact hpar.gap) hpar.bound.1 H π hπ v₀ hv₀`.

Establish `hsmv : SmV (GlobalTheory.Ell.lieOf (Jm ε)) π (π g₀ v₀)` using `smV_translate hπ hg₀ hLB.1`. Establish `hsmw : SmV (GlobalTheory.Ell.lieOf (Jm ε')) σ w`. Rewrite using `[← hTv]`. Conclude with `hMS n e ε lam ε' mu B hpar H H' π σ hπ hσ T hT (π g₀ v₀) hsmv`. Establish `hwn : 0 < ‖w‖` using `norm_pos_iff.2 hw0`.

Establish `hw'n : ‖((‖w‖ : ℂ)⁻¹) • w‖ = 1`. Rewrite using `[norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hwn.le, inv_mul_cancel₀ hwn.ne']`. Establish `hw'w' : ⟪((‖w‖ : ℂ)⁻¹) • w, ((‖w‖ : ℂ)⁻¹) • w⟫_ℂ = 1`. Rewrite using `[inner_self_eq_norm_sq_to_K, hw'n]`. Simplify using the standard rewrite rules.

Establish `hVb : ((muG ε') (nbh ε' (1 / 4))).toReal ≤ c * big (C2 + 100 + 100 + 1) n B`. Establish `h1` using `hVD n e ε lam ε' mu B hpar H H' π σ hπ hσ d' hd'`. Establish `h2` using `vol_arith hd'pos (big_pos C2 n B) (big_pos 100 n B) (two_le_big_one n hB) h1 hbig hcP`. Rewrite `h2` using `[big_mul, big_mul, big_mul, mul_comm]`. Conclude with `h2`.

Use `⟨v₀, π g₀ v₀, g₀, ((‖w‖ : ℂ)⁻¹) • w, c, hv₀, hg₀, rfl, hsmv, smV_const_smul _ hsmw, hw'n, hcpos, ?_, ?_, ?_, hIBv.2⟩` and prove the remaining obligations. Introduce `b`. Establish `hin : ∀ h : ↥(UJ ε'), ⟪b, σ (umat h) (((‖w‖ : ℂ)⁻¹) • w)⟫_ℂ = (‖w‖ : ℂ)⁻¹ * ⟪b, σ (umat h) w⟫_ℂ`. Introduce `h`. Rewrite using `[map_smul, inner_smul_right]`.

Repeatedly rewrite using `[hin, mul_left_comm _ ((‖w‖ : ℂ)⁻¹)]`. Rewrite using `[integral_const_mul, hcoef b, hw'w', inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree. Introduce `g hg`. Take `⟨hint, hle⟩` from `hIBv.1 g hg`.

Use `⟨hint, hle.trans ?_⟩` and prove the remaining obligations. Establish `hcl : 0 ≤ colLen e g`. Unfold `colLen`. Check the signs of the components of the expression. Establish `hX : 0 ≤ colLen e g ^ (-(2 * (n : ℝ) + 7))` using `by first`.

Consider the case `exact Real.rpow_nonneg hcl _`. Consider the case `exact zpow_nonneg hcl _`. Consider the case `positivity`. Apply `mul_le_mul_of_nonneg_right _ hX` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Introduce `X hX hXn`. Take `⟨hint, hle⟩` from `hDB n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n X hX hXn`. Use `⟨hint, hle.trans ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Lit.Branch.realInputE :
    ProjLarge → EigMap → RealInputE := by
  intro hPL hEM
  unfold ProjLarge at hPL
  unfold EigMap at hEM
  obtain ⟨C1, hC1, hIB⟩ := GlobalTheory.T.translateCoefficientIntegralBounds_of_unitary_laws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws (GlobalTheory.T.boostDecompositionNormBound_of_embeddingLaws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws)
    (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound) GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay 10 (by norm_num)
  obtain ⟨C3, hC3, hDB⟩ := GlobalTheory.T.translateCoefficientDerivativeIntegralBounds_of_laws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound)
    GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay GlobalTheory.T.lowestKType_lieWord_normBound 10 (by norm_num)
  obtain ⟨C2, hC2, hVD⟩ := volDeg
  have hDR := GlobalTheory.T.formalDegree_loweringWeight_ratio_le
  have hMS := mapSmooth
  have hLBall := GlobalTheory.T.lowestKType_lieWord_normBound
  unfold ForPair at hPL hEM hIB hDB hVD hMS hDR
  unfold DegRatio at hDR
  unfold MapSmooth at hMS
  unfold LieBound ForDS at hLBall
  unfold RealInputE ForPair
  refine ⟨C1 + C3 + C2 + 201, by linarith, ?_⟩
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ
  have hB : 1 ≤ B := one_le_B hpar
  obtain ⟨⟨v₀, hv₀⟩, -, -⟩ := GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree (n + 1) ε lam H π hπ
  obtain ⟨j, P, hjP, g₀, hg₀, hg₀n, hbig⟩ := hPL n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀
  obtain ⟨d', hd'⟩ := (hDR n e ε lam ε' mu B hpar H H' π σ hπ hσ).1
  obtain ⟨⟨w₀, hw₀⟩, -, -⟩ := GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree n ε' mu H' σ hσ
  have hnn : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    gcongr
    linarith
  have hgap' : GapAtLeast ε' mu (1000 * (n : ℝ) ^ 3) := gap_mono (by linarith) hpar.gap'
  have hw₀int := integrable_low_coef GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound) ε' mu B hpar.three_le
    hpar.hmu hgap' hpar.bound.2 σ hσ w₀ hw₀
  have hIBv := hIB n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n
  have hvint : Integrable (fun h => ⟪π g₀ v₀, π (embH e (umat h)) (π g₀ v₀)⟫_ℂ) (muG ε') := by
    have hi := (hIBv.1 1 (one_mem ε)).1
    simpa using hi
  have hPv : P (π g₀ v₀) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hbig
    linarith
  obtain ⟨w, c, T, hw0, hcP, hcoef, hT, hTv⟩ :=
    hEM n e ε lam ε' mu B hpar H H' π σ hπ hσ d' hd' w₀ hw₀.1 hw₀int j P hjP (π g₀ v₀) hvint hPv
  have hd'pos : 0 < d' := hd'.1
  have hPvpos : 0 < ‖P (π g₀ v₀)‖ := norm_pos_iff.2 hPv
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hcP
  have hLB := hLBall (n + 1) ε lam B (by have := hpar.three_le; omega) hpar.hlam
    (by push_cast; exact hpar.gap) hpar.bound.1 H π hπ v₀ hv₀
  have hsmv : SmV (GlobalTheory.Ell.lieOf (Jm ε)) π (π g₀ v₀) := smV_translate hπ hg₀ hLB.1
  have hsmw : SmV (GlobalTheory.Ell.lieOf (Jm ε')) σ w := by
    rw [← hTv]
    exact hMS n e ε lam ε' mu B hpar H H' π σ hπ hσ T hT (π g₀ v₀) hsmv
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hw'n : ‖((‖w‖ : ℂ)⁻¹) • w‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hwn.le, inv_mul_cancel₀ hwn.ne']
  have hw'w' : ⟪((‖w‖ : ℂ)⁻¹) • w, ((‖w‖ : ℂ)⁻¹) • w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw'n]
    simp
  have hVb : ((muG ε') (nbh ε' (1 / 4))).toReal ≤ c * big (C2 + 100 + 100 + 1) n B := by
    have h1 := hVD n e ε lam ε' mu B hpar H H' π σ hπ hσ d' hd'
    have h2 := vol_arith hd'pos (big_pos C2 n B) (big_pos 100 n B) (two_le_big_one n hB) h1 hbig hcP
    rw [big_mul, big_mul, big_mul, mul_comm] at h2
    exact h2
  refine ⟨v₀, π g₀ v₀, g₀, ((‖w‖ : ℂ)⁻¹) • w, c, hv₀, hg₀, rfl, hsmv, smV_const_smul _ hsmw, hw'n, hcpos,
    ?_, ?_, ?_, hIBv.2⟩
  · intro b
    have hin : ∀ h : ↥(UJ ε'), ⟪b, σ (umat h) (((‖w‖ : ℂ)⁻¹) • w)⟫_ℂ = (‖w‖ : ℂ)⁻¹ * ⟪b, σ (umat h) w⟫_ℂ := by
      intro h
      rw [map_smul, inner_smul_right]
    simp_rw [hin, mul_left_comm _ ((‖w‖ : ℂ)⁻¹)]
    rw [integral_const_mul, hcoef b, hw'w', inner_smul_right]
    ring
  · intro g hg
    obtain ⟨hint, hle⟩ := hIBv.1 g hg
    refine ⟨hint, hle.trans ?_⟩
    have hcl : 0 ≤ colLen e g := by
      unfold colLen
      positivity
    have hX : 0 ≤ colLen e g ^ (-(2 * (n : ℝ) + 7)) := by
      first
        | exact Real.rpow_nonneg hcl _
        | exact zpow_nonneg hcl _
        | positivity
    apply mul_le_mul_of_nonneg_right _ hX
    calc ((muG ε') (nbh ε' (1 / 4))).toReal * big C1 n B
        ≤ c * big (C2 + 100 + 100 + 1) n B * big C1 n B :=
          mul_le_mul_of_nonneg_right hVb (big_pos _ _ _).le
      _ = c * big (C2 + 100 + 100 + 1 + C1) n B := by rw [mul_assoc, big_mul]
      _ ≤ c * big (C1 + C3 + C2 + 201) n B :=
          mul_le_mul_of_nonneg_left (big_mono (by linarith) n hB) hcpos.le
  · intro X hX hXn
    obtain ⟨hint, hle⟩ := hDB n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n X hX hXn
    refine ⟨hint, hle.trans ?_⟩
    calc ((muG ε') (nbh ε' (1 / 4))).toReal * big C3 n B
        ≤ c * big (C2 + 100 + 100 + 1) n B * big C3 n B :=
          mul_le_mul_of_nonneg_right hVb (big_pos _ _ _).le
      _ = c * big (C2 + 100 + 100 + 1 + C3) n B := by rw [mul_assoc, big_mul]
      _ ≤ c * big (C1 + C3 + C2 + 201) n B :=
          mul_le_mul_of_nonneg_left (big_mono (by linarith) n hB) hcpos.le
