import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.QuantumDeterminants
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuDec

namespace BM

section Core

variable {k r : ℕ}

/- English proof (translation)
Take `⟨B, hB, hWB⟩` from `hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ W hc1 he1 hr1 hl1 hl1'`. Take `⟨B0, hB0, hW0B⟩` from `hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ W0 hc2 he2 hr2 hl2 hl2'`. Rewrite `hB`, `hB0` using `[Formalism.L2.SG.LitS.psi_eq_psiGen]`. Take `⟨a, b, hab, hlin'⟩` from `hM1 k r ε lam h H σ z (fun _ => c) u Vp π hok.1 hg hok.2.1 hl hds hz hT (fun _ => hc) hπ B B0 ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B).1 hB) ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B0).1 hB0)`. Establish `hlin : ∀ v ∈ smoothVecs (k` using `k) (r := r) σ, a • B v + b • B0 v = 0 := fun v hv => hlin' v hv`.

Establish `hsm : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ x w ∈ smoothVecs (k` using `k) (r := r) σ := fun x hx => Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hws hx`. Distinguish the cases in `ha : a = 0`. It suffices to derive a contradiction. Establish `hb : b ≠ 0` using `hab.resolve_left (not_not.2 ha)`. Take `⟨x0, hx0U, hx0W⟩` from `hx0`.

Establish `h1` using `hlin (σ x0 w) (hsm x0 hx0U)`. Rewrite `h1` using `[ha, zero_smul, zero_add]`. Establish `h2 : B0 (σ x0 w) = 0` using `(smul_eq_zero.1 h1).resolve_left hb`. Conclude with `hx0W (by rw [hW0B x0 hx0U, h2])`. Use `⟨-(b / a), fun x hx => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hlin (σ x w) (hsm x hx)`. Rewrite using `[hWB x hx, hW0B x hx]`. Establish `: a • B (σ x w) = -(b • B0 (σ x w))` using `eq_neg_of_add_eq_zero_left h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]`.
-/
theorem besselUniq_core (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {lam : Fin (2 * r + k + 1) → ℝ}
    {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat k r → (H →L[ℂ] H)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hds : IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    (hπ : IsHCTypeW k r z u π) {w : H} (hw : IsLowUnitH k r ε lam σ w) (hws : w ∈ smoothVecs (k := k) (r := r) σ)
    {μG μW μN ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (hW : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hQ : IsQuotMeas μG (Formalism.MainNotions.S.muS μW μN) ν)
    {W W0 : Mat k r → Vp}
    (hc1 : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he1 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    (hr1 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x)
    (hl1 : l2SG ν W ≠ 0) (hl1' : l2SG ν W < ⊤)
    (hc2 : ContinuousOn W0 (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he2 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W0)
    (hr2 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W0 (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W0 x = W0 x)
    (hl2 : l2SG ν W0 ≠ 0) (hl2' : l2SG ν W0 < ⊤)
    (hx0 : ∃ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W0 x0 ≠ 0) :
    ∃ a : ℂ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = a • W0 x := by
  obtain ⟨B, hB, hWB⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W hc1 he1 hr1 hl1 hl1'
  obtain ⟨B0, hB0, hW0B⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W0 hc2 he2 hr2 hl2 hl2'
  rw [Formalism.L2.SG.LitS.psi_eq_psiGen] at hB hB0
  obtain ⟨a, b, hab, hlin'⟩ := hM1 k r ε lam h H σ z (fun _ => c) u Vp π hok.1 hg hok.2.1 hl hds hz hT (fun _ => hc) hπ
    B B0 ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B).1 hB) ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B0).1 hB0)
  have hlin : ∀ v ∈ smoothVecs (k := k) (r := r) σ, a • B v + b • B0 v = 0 := fun v hv => hlin' v hv
  have hsm : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ x w ∈ smoothVecs (k := k) (r := r) σ :=
    fun x hx => Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hws hx
  by_cases ha : a = 0
  · exfalso
    have hb : b ≠ 0 := hab.resolve_left (not_not.2 ha)
    obtain ⟨x0, hx0U, hx0W⟩ := hx0
    have h1 := hlin (σ x0 w) (hsm x0 hx0U)
    rw [ha, zero_smul, zero_add] at h1
    have h2 : B0 (σ x0 w) = 0 := (smul_eq_zero.1 h1).resolve_left hb
    exact hx0W (by rw [hW0B x0 hx0U, h2])
  · refine ⟨-(b / a), fun x hx => ?_⟩
    have h1 := hlin (σ x w) (hsm x hx)
    rw [hWB x hx, hW0B x hx]
    have : a • B (σ x w) = -(b • B0 (σ x w)) := eq_neg_of_add_eq_zero_left h1
    calc B (σ x w) = a⁻¹ • (a • B (σ x w)) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = -(b / a) • B0 (σ x w) := by
          rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Core

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

section Main

variable {k r : ℕ}

/- English proof (translation)
Take `⟨P0, hP0⟩` from `Formalism.MainNotions.S.Inh.exists_isCayleyU_eps48 k r hk`. Establish `hCP : CayPair (eps48 k r) P0 (Hpk k r * P0ᴴ * Formalism.REAL.Jm (eps48 k r))` using `⟨hP0.1.2, rfl⟩`. Generalize the expression as in `hB0 : Hpk k r * P0ᴴ * Formalism.REAL.Jm (eps48 k r) = B0 at hCP`. Establish `hinv : P0⁻¹ = B0` using `Matrix.inv_eq_left_inv hCP.BP`. Establish `hσB1 : (fun g => (fun M => σ (P0 * M * B0)) (P0⁻¹ * g * P0)) = σ`.

Use function extensionality and compare the values at `g`. Simplify using `only [hinv]`. Use `congr 1`. Simplify using `only [← Matrix.mul_assoc, hCP.PB, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, hCP.PB, Matrix.mul_one]`.

Establish `hDSB : IsDSHpk k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0))` using `⟨P0, hP0, by rw [hσB1]; exact hDS⟩`. Establish `hwB : IsLowUnitH k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) w` using `⟨P0, hP0, by rw [hσB1]; exact hw⟩`. Establish `hcc0 : ((4 * Real.pi / gg : ℝ) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < 4 * Real.pi / gg` using `by positivity`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hTz : 0 < Tz k r (zBv k r T)` using `by rw [Tz_zB hT.le]; exact hT`. Establish `hS48 : RealPlaceNumericalSetting k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b` using `⟨hk, hke, inWb_zB T, hTz, fun _ => hcc0, hu, hl, hI, hH, hGap⟩`. Establish `hπB` using `hcTypeW_piB hF hT.le hπ`. Establish `hG` using `isHaarOn_G hCP`. Establish `hSB` using `isHaarOn_S hF hS`.

Establish `hQB` using `isQuotMeas_B hF hCP hQ`. Take `⟨μW, μN, hW, hN, hWfin, hNc⟩` from `WlocSk.haar_measure_unipotent_nilradical k r (zBv k r T) (inWb_zB T) hTz`. Take `⟨cS, hcS0, hcSt, hP⟩` from `WlocSk.product_decomposition_holds k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b H (fun M => σ (P0 * M * B0)) Vl (piB (eps48 k r) e f wf (z0v T z) πl) w _ _ _ μW μN ⟨hS48, hDSB, hπB, hwB, hG, hSB, hQB, hW, hN, hWfin, hNc⟩`. Establish `hmuS : Formalism.MainNotions.S.muS μW μN = cS • (μS.map (cM (Qi (eps48 k r) e f wf (z0v T z)) (Qm e f wf (z0v T z))))` using `hP`. Establish `hQ' : IsQuotMeas ((Formalism.REAL.muG (eps48 k r)).map (cM B0 P0)) (Formalism.MainNotions.S.muS μW μN) (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0))`.

Introduce `g hg`. Rewrite using `[hQB g hg, hmuS]`. Simplify using `only [lintegral_smul_measure, smul_eq_mul]`. Rewrite using `[lintegral_const_mul' _ _ hcSt, ← mul_assoc, ENNReal.inv_mul_cancel hcS0 hcSt, one_mul]`. Establish `hS' : IsHaarOn (Sset k r (zBv k r T)) (Formalism.MainNotions.S.muS μW μN)`.

Rewrite using `[hmuS]`. Conclude with `isHaarOn_smul hSB hcS0 hcSt`. Take `⟨W0, hc0, he0, hr0, -, hL20, hwt0, α, Ω, a, hΩc, h1Ω, hΩU, hαm, hαs, hαb, hαr⟩` from `hWl hB hCW k r (zBv k r T) _ u v b hS48 H _ hDSB Vl (piB (eps48 k r) e f wf (z0v T z) πl) hπB w hwB _ _ _ hG hS' hQ'`. Establish `hpsi : Formalism.QuantumDeterminants.psi k r (zBv k r T) ((4 * Real.pi / gg : ℝ) : ℂ) = psiGen k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ))` using `Formalism.L2.SG.LitS.psi_eq_psiGen _ _ _ _`. Establish `he0' : IsSPsiEquiv (zBv k r T) (Formalism.QuantumDeterminants.psi k r (zBv k r T) ((4 * Real.pi / gg : ℝ) : ℂ)) (piB (eps48 k r) e f wf (z0v T z) πl) W0` using `by rw [hpsi]; exact he0`.

Establish `embX` using `cM_measEmb (ε := eps48 k r) (A := Qi (eps48 k r) e f wf (z0v T z)) (B := P0) (A' := Qm e f wf (z0v T z)) (B' := B0) (Qm_mul_Qi hF) hCP.PB`. Establish `embG` using `cM_measEmb (ε := eps48 k r) (A := B0) (B := P0) (A' := P0) (B' := B0) hCP.PB hCP.PB`. Establish `hXU : ∀ x : Formalism.REAL.UJ (eps48 k r), (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) ∈ UH (Hpk k r)` using `cX_mem_UH hF hCP`. Establish `hl2eq : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) = cS⁻¹ * ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν`. Unfold `l2SG`.

Rewrite using `[lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]`. Use `congr 1`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Use `show (‖WB hF hCP W (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖₊ : ℝ≥0∞) ^ 2 = ‖W x‖ₑ ^ 2`. Rewrite using `[WB_cM]`.

Both sides reduce to the same expression. Establish `hcSi0 : cS⁻¹ ≠ 0` using `ENNReal.inv_ne_zero.2 hcSt`. Establish `hcSit : cS⁻¹ ≠ ⊤` using `ENNReal.inv_ne_top.2 hcS0`. Establish `hl2ne : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) ≠ 0`. Rewrite using `[hl2eq]`.

Conclude with `mul_ne_zero hcSi0 hL0`. Establish `hl2lt : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) < ⊤`. Rewrite using `[hl2eq]`. Conclude with `ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcSit) (lt_top_iff_ne_top.2 hLt)`. Establish `hx0 : ∃ x0 ∈ UH (Hpk k r), W0 x0 ≠ 0`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `: l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) W0 = 0`. Unfold `l2SG`. Rewrite using `[lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]`.

Establish `hz0 : ∀ x : Formalism.REAL.UJ (eps48 k r), (‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖₊ : ℝ≥0∞) ^ 2 = 0`. Introduce `x`. Rewrite using `[hcon _ (hXU x)]`. Simplify using the standard rewrite rules. Simplify using `only [hz0, lintegral_zero, mul_zero]`.

Rewrite `this` using `[hL20]`. Conclude with `one_ne_zero this`. Take `⟨a', hprop⟩` from `besselUniq_core hBW hM1 hl hDSB hga hok (inWb_zB T) hTz hcc0 hπB hwB (lowSmoothSK hDSB hwB) hG hW hN hQ' (WB_continuousOn hF hCP hWc) (WB_equiv hF hCP (Qm_zB hT z) hgg hWe) (WB_reprod hF hCP σ w hWr) hl2ne hl2lt hc0 he0' hr0 (by rw [hL20]; exact one_ne_zero) (by rw [hL20]; exact …`. Establish `hWeq : ∀ x : Formalism.REAL.UJ (eps48 k r), W x = a' • W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))`. Introduce `x`.

Rewrite using `[← hprop _ (hXU x), WB_cM]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hc : 0 ≤ opn (Qm e f wf (z0v T z)) * opn B0` using `mul_nonneg (Formalism.L2.SG.WuDecayPf.opn_nonneg _) (Formalism.L2.SG.WuDecayPf.opn_nonneg _)`. Establish `hN : 0 ≤ N1H k r` using `by unfold N1H; positivity`. Use `set K : ℝ≥0∞ := ‖a'‖ₑ * ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) with hKdef`.

Establish `hpt : ∀ x, ‖W x‖ₑ * ENNReal.ofReal (nuLoc (e` using `e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ≤ K * (‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ * ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r)) := by`. Introduce `x`. Establish `h0 : 0 ≤ nuLoc (e` using `e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x := Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _`. Establish `h0' : 0 ≤ nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))` using `Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _`. Establish `hle` using `nuLoc_le hF hCP (zBv k r T) x`.

Rewrite using `[hWeq x, enorm_smul, hKdef]`. Establish `h2 : ENNReal.ofReal (nuLoc (e` using `e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ≤ ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) * ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) := by`. Rewrite using `[← ENNReal.ofReal_mul (Real.rpow_nonneg hc _), ← Real.mul_rpow hc h0']`. Conclude with `ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 hle hN)`. Combine the equalities or inequalities in the displayed calculation.

Use `lt_of_le_of_lt (lintegral_mono hpt) ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]`. Use `ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)) ?_` and prove the remaining obligations. Establish `h3` using `hwt0`. Rewrite `h3` using `[lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]`.

Establish `h4 : ∫⁻ x, ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ * ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) ∂ν = cS * (cS⁻¹ * ∫⁻ x, ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ * ENNReal.ofReal …`. Rewrite using `[← mul_assoc, ENNReal.mul_inv_cancel hcS0 hcSt, one_mul]`. Rewrite using `[h4]`. Conclude with `ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcSt) h3`. Use `⟨fun g => α (cM B0 P0 g), cM B0 P0 ⁻¹' Ω, a, (cM_closedEmb hCP.PB hCP.PB).isCompact_preimage hΩc, ?_, hαm.comp embG.measurable, fun y hy => hαs _ hy, fun y => hαb _, ?_⟩` and prove the remaining obligations.

Use `show Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ (eps48 k r))) ∈ Ω`. Establish `: Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ (eps48 k r))) = (1 : Mat k r)` using `by show B0 * uMat 1 * P0 = 1; rw [uMat_one', Matrix.mul_one, hCP.BP]`. Rewrite using `[this]`. Conclude with `h1Ω`. Introduce `x`.

Take `⟨hint, hval⟩` from `hαr _ (hXU x)`. Establish `hint2` using `embG.integrable_map_iff.mp hint`. Establish `hprod : ∀ g : Formalism.REAL.UJ (eps48 k r), (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) * Matrix.of (cM B0 P0 g) = Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 (x * g))` using `fun g => cMprod hCP _ x g`. Establish `hpt : ∀ g : Formalism.REAL.UJ (eps48 k r), α (cM B0 P0 g) • W (x * g) = a' • (α (Matrix.of (cM B0 P0 g)) • W0 ((Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) * Matrix.of (cM B0 P0 g)))`. Introduce `g`.

Rewrite using `[hprod, hWeq, smul_comm]`. Both sides reduce to the same expression. Use `⟨(hint2.smul a').congr (ae_of_all _ fun g => (hpt g).symm), ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae (ae_of_all _ hpt), integral_smul]`. Establish `h5 : ∫ g, α (Matrix.of (cM B0 P0 g)) • W0 ((Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) * Matrix.of (cM B0 P0 g)) ∂(Formalism.REAL.muG (eps48 k r)) = W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))`.

Rewrite using `[← hval]`. Unfold `rconv`. Rewrite using `[embG.integral_map]`. Rewrite using `[h5, ← hWeq]`.
-/
theorem locUniq_gen (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists)
    (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hgg : 0 < gg)
    {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z : Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameJ (eps48 k r) e f wf (z0v T z))
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {h : ℝ} (hga : Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) (lam48 k r v b) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hDS : IsDS (eps48 k r) (lam48 k r v b) σ)
    {w : H} (hw : IsLowUnit (eps48 k r) (lam48 k r v b) σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    {πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)} (hπ : IsHCTypeU k u πl)
    {μS ν : Measure (Formalism.REAL.UJ (eps48 k r))} (hS : IsLocHaar (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) μS)
    (hQ : IsLocQuot μS ν)
    {W : Formalism.REAL.UJ (eps48 k r) → Vl} (hWc : Continuous W)
    (hWe : ∀ s x : Formalism.REAL.UJ (eps48 k r), ∀ h ∈ UWset k r (zBv k r T), ∀ m ∈ Nset k r,
      Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h * m →
      W (s * x) = psiR (eps48 k r) gg e f z (uMat s) • piB (eps48 k r) e f wf (z0v T z) πl h (W x))
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG (eps48 k r)) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG (eps48 k r)) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG (eps48 k r)) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG (eps48 k r)) = W x)
    (hL0 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ 0) (hLt : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ ⊤) :
    (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ∂ν
      < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ (eps48 k r) → ℂ) (Ω : Set (Formalism.REAL.UJ (eps48 k r))) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG (eps48 k r)) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG (eps48 k r)) = W x := by
  obtain ⟨P0, hP0⟩ := Formalism.MainNotions.S.Inh.exists_isCayleyU_eps48 k r hk
  have hCP : CayPair (eps48 k r) P0 (Hpk k r * P0ᴴ * Formalism.REAL.Jm (eps48 k r)) := ⟨hP0.1.2, rfl⟩
  generalize hB0 : Hpk k r * P0ᴴ * Formalism.REAL.Jm (eps48 k r) = B0 at hCP
  have hinv : P0⁻¹ = B0 := Matrix.inv_eq_left_inv hCP.BP
  have hσB1 : (fun g => (fun M => σ (P0 * M * B0)) (P0⁻¹ * g * P0)) = σ := by
    funext g
    simp only [hinv]
    congr 1
    simp only [← Matrix.mul_assoc, hCP.PB, Matrix.one_mul]
    rw [Matrix.mul_assoc, hCP.PB, Matrix.mul_one]
  have hDSB : IsDSHpk k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) := ⟨P0, hP0, by rw [hσB1]; exact hDS⟩
  have hwB : IsLowUnitH k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) w := ⟨P0, hP0, by rw [hσB1]; exact hw⟩
  have hcc0 : ((4 * Real.pi / gg : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 4 * Real.pi / gg := by positivity
    exact_mod_cast this.ne'
  have hTz : 0 < Tz k r (zBv k r T) := by rw [Tz_zB hT.le]; exact hT
  have hS48 : RealPlaceNumericalSetting k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b :=
    ⟨hk, hke, inWb_zB T, hTz, fun _ => hcc0, hu, hl, hI, hH, hGap⟩
  have hπB := hcTypeW_piB hF hT.le hπ
  have hG := isHaarOn_G hCP
  have hSB := isHaarOn_S hF hS
  have hQB := isQuotMeas_B hF hCP hQ
  obtain ⟨μW, μN, hW, hN, hWfin, hNc⟩ := WlocSk.haar_measure_unipotent_nilradical k r (zBv k r T) (inWb_zB T) hTz
  obtain ⟨cS, hcS0, hcSt, hP⟩ := WlocSk.product_decomposition_holds k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b H
    (fun M => σ (P0 * M * B0)) Vl (piB (eps48 k r) e f wf (z0v T z) πl) w _ _ _ μW μN
    ⟨hS48, hDSB, hπB, hwB, hG, hSB, hQB, hW, hN, hWfin, hNc⟩
  have hmuS : Formalism.MainNotions.S.muS μW μN =
      cS • (μS.map (cM (Qi (eps48 k r) e f wf (z0v T z)) (Qm e f wf (z0v T z)))) := hP
  have hQ' : IsQuotMeas ((Formalism.REAL.muG (eps48 k r)).map (cM B0 P0)) (Formalism.MainNotions.S.muS μW μN)
      (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) := by
    intro g hg
    rw [hQB g hg, hmuS]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hcSt, ← mul_assoc, ENNReal.inv_mul_cancel hcS0 hcSt, one_mul]
  have hS' : IsHaarOn (Sset k r (zBv k r T)) (Formalism.MainNotions.S.muS μW μN) := by
    rw [hmuS]; exact isHaarOn_smul hSB hcS0 hcSt
  obtain ⟨W0, hc0, he0, hr0, -, hL20, hwt0, α, Ω, a, hΩc, h1Ω, hΩU, hαm, hαs, hαb, hαr⟩ :=
    hWl hB hCW k r (zBv k r T) _ u v b hS48 H _ hDSB Vl (piB (eps48 k r) e f wf (z0v T z) πl) hπB w hwB _ _ _
      hG hS' hQ'
  have hpsi : Formalism.QuantumDeterminants.psi k r (zBv k r T) ((4 * Real.pi / gg : ℝ) : ℂ) =
      psiGen k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) := Formalism.L2.SG.LitS.psi_eq_psiGen _ _ _ _
  have he0' : IsSPsiEquiv (zBv k r T) (Formalism.QuantumDeterminants.psi k r (zBv k r T) ((4 * Real.pi / gg : ℝ) : ℂ))
      (piB (eps48 k r) e f wf (z0v T z) πl) W0 := by rw [hpsi]; exact he0
  have embX := cM_measEmb (ε := eps48 k r) (A := Qi (eps48 k r) e f wf (z0v T z)) (B := P0)
    (A' := Qm e f wf (z0v T z)) (B' := B0) (Qm_mul_Qi hF) hCP.PB
  have embG := cM_measEmb (ε := eps48 k r) (A := B0) (B := P0) (A' := P0) (B' := B0) hCP.PB hCP.PB
  have hXU : ∀ x : Formalism.REAL.UJ (eps48 k r),
      (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) ∈ UH (Hpk k r) := cX_mem_UH hF hCP

  have hl2eq : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) =
      cS⁻¹ * ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν := by
    unfold l2SG
    rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]
    congr 1
    refine lintegral_congr fun x => ?_
    show (‖WB hF hCP W (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖₊ : ℝ≥0∞) ^ 2 = ‖W x‖ₑ ^ 2
    rw [WB_cM]; rfl
  have hcSi0 : cS⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hcSt
  have hcSit : cS⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hcS0
  have hl2ne : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) ≠ 0 := by
    rw [hl2eq]; exact mul_ne_zero hcSi0 hL0
  have hl2lt : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) < ⊤ := by
    rw [hl2eq]; exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcSit) (lt_top_iff_ne_top.2 hLt)

  have hx0 : ∃ x0 ∈ UH (Hpk k r), W0 x0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) W0 = 0 := by
      unfold l2SG
      rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]
      have hz0 : ∀ x : Formalism.REAL.UJ (eps48 k r),
          (‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖₊ : ℝ≥0∞) ^ 2 = 0 := by
        intro x; rw [hcon _ (hXU x)]; simp
      simp only [hz0, lintegral_zero, mul_zero]
    rw [hL20] at this
    exact one_ne_zero this
  obtain ⟨a', hprop⟩ := besselUniq_core hBW hM1 hl hDSB hga hok (inWb_zB T) hTz hcc0 hπB hwB (lowSmoothSK hDSB hwB)
    hG hW hN hQ' (WB_continuousOn hF hCP hWc) (WB_equiv hF hCP (Qm_zB hT z) hgg hWe) (WB_reprod hF hCP σ w hWr)
    hl2ne hl2lt hc0 he0' hr0 (by rw [hL20]; exact one_ne_zero) (by rw [hL20]; exact ENNReal.one_lt_top) hx0
  have hWeq : ∀ x : Formalism.REAL.UJ (eps48 k r),
      W x = a' • W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) := by
    intro x; rw [← hprop _ (hXU x), WB_cM]
  refine ⟨?_, ?_⟩
  ·
    have hc : 0 ≤ opn (Qm e f wf (z0v T z)) * opn B0 :=
      mul_nonneg (Formalism.L2.SG.WuDecayPf.opn_nonneg _) (Formalism.L2.SG.WuDecayPf.opn_nonneg _)
    have hN : 0 ≤ N1H k r := by unfold N1H; positivity
    set K : ℝ≥0∞ := ‖a'‖ₑ * ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) with hKdef
    have hpt : ∀ x, ‖W x‖ₑ *
        ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ≤
        K * (‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
          ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r)) := by
      intro x
      have h0 : 0 ≤ nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x :=
        Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _
      have h0' : 0 ≤ nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) :=
        Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _
      have hle := nuLoc_le hF hCP (zBv k r T) x
      rw [hWeq x, enorm_smul, hKdef]
      have h2 : ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ≤
          ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) *
            ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc _), ← Real.mul_rpow hc h0']
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 hle hN)
      calc ‖a'‖ₑ * ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
            ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r)
          ≤ ‖a'‖ₑ * ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
            (ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) *
            ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r)) := by
            gcongr
        _ = _ := by ring
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)) ?_
    have h3 := hwt0
    rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map] at h3
    have h4 : ∫⁻ x, ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
        ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) ∂ν =
        cS * (cS⁻¹ * ∫⁻ x, ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
        ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) ∂ν) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hcS0 hcSt, one_mul]
    rw [h4]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcSt) h3
  ·
    refine ⟨fun g => α (cM B0 P0 g), cM B0 P0 ⁻¹' Ω, a, (cM_closedEmb hCP.PB hCP.PB).isCompact_preimage hΩc, ?_,
      hαm.comp embG.measurable, fun y hy => hαs _ hy, fun y => hαb _, ?_⟩
    · show Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ (eps48 k r))) ∈ Ω
      have : Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ (eps48 k r))) = (1 : Mat k r) := by
        show B0 * uMat 1 * P0 = 1; rw [uMat_one', Matrix.mul_one, hCP.BP]
      rw [this]; exact h1Ω
    · intro x
      obtain ⟨hint, hval⟩ := hαr _ (hXU x)
      have hint2 := embG.integrable_map_iff.mp hint
      have hprod : ∀ g : Formalism.REAL.UJ (eps48 k r), (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) *
          Matrix.of (cM B0 P0 g) = Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 (x * g)) :=
        fun g => cMprod hCP _ x g
      have hpt : ∀ g : Formalism.REAL.UJ (eps48 k r), α (cM B0 P0 g) • W (x * g) =
          a' • (α (Matrix.of (cM B0 P0 g)) • W0 ((Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) *
            Matrix.of (cM B0 P0 g))) := by
        intro g
        rw [hprod, hWeq, smul_comm]
        rfl
      refine ⟨(hint2.smul a').congr (ae_of_all _ fun g => (hpt g).symm), ?_⟩
      rw [integral_congr_ae (ae_of_all _ hpt), integral_smul]
      have h5 : ∫ g, α (Matrix.of (cM B0 P0 g)) • W0 ((Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) :
          Matrix _ _ ℂ) * Matrix.of (cM B0 P0 g)) ∂(Formalism.REAL.muG (eps48 k r)) =
          W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) := by
        rw [← hval]
        unfold rconv
        rw [embG.integral_map]
      rw [h5, ← hWeq]

end Main

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hε' : ε = eps48 k r` using `funext fun i => by rw [hε i]; rfl`. Substitute `hε'` using the available equality. Establish `hlam' : lam = lam48 k r v b` using `funext fun i => by rw [hlam i]; rfl`. Substitute `hlam'` using the available equality.

Establish `hF` using `isFrameJ_of (ε := eps48 k r) e f z wf hT hee hff hef hez hfz hzz hww hew hfw hzw`. Establish `hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) ≠ 0`. Establish `: (Real.sqrt T)⁻¹ ≠ 0` using `inv_ne_zero (Real.sqrt_pos.mpr hT).ne'`. Conclude with `this` after adjusting the coercions. Establish `hP` using `hHN k r (eps48 k r) e f wf (z0v T z) z _ hF hc rfl`.

Establish `heq : HNset (eps48 k r) e f wf (z0v T z) (zBv k r T) = {s | ∃ m ∈ {g : Formalism.REAL.UJ (eps48 k r) | InN (eps48 k r) e z (uMat g)}, ∃ h ∈ {g : Formalism.REAL.UJ (eps48 k r) | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z}, s = m * h}` using `Set.ext fun s => HNset_eq_NH hHN hT hF s`. Establish `hS' : IsLocHaar (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) μS`. Take `⟨h1, h2, h3, h4⟩` from `hS`. Conclude with `⟨h1, h2, by rw [heq]; exact h3, fun s hs => h4 s (heq ▸ hs)⟩`. Establish `hz : (Qm e f wf (z0v T z)) *ᵥ (zBv k r T) = z` using `Qm_zB hT z`.

Establish `hzB0` using `inWb_zB (k := k) (r := r) T`. Establish `hWe' : ∀ s x : Formalism.REAL.UJ (eps48 k r), ∀ h' ∈ UWset k r (zBv k r T), ∀ m' ∈ Nset k r, Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h' * m' → W (s * x) = psiR (eps48 k r) gg e f z (uMat s) • piB (eps48 k r) e f wf (z0v T z) πl h' (W x)`. Introduce `s x h' hh' m' hm' hsm`. Use `set sh : Formalism.REAL.UJ (eps48 k r) := toUJ (Qm e f wf (z0v T z) * h' * Qi (eps48 k r) e f wf (z0v T z)) (conjQ_UJ hF hh'.1) with hsh`. Use `set sm : Formalism.REAL.UJ (eps48 k r) := toUJ (Qm e f wf (z0v T z) * m' * Qi (eps48 k r) e f wf (z0v T z)) (conjQ_UJ hF hm'.1) with hsm'`.

Establish `hush : uMat sh = Qm e f wf (z0v T z) * h' * Qi (eps48 k r) e f wf (z0v T z)` using `uMat_toUJ _ _`. Establish `husm : uMat sm = Qm e f wf (z0v T z) * m' * Qi (eps48 k r) e f wf (z0v T z)` using `uMat_toUJ _ _`. Establish `hfix : (∀ a, uMat sh *ᵥ e a = e a) ∧ (∀ a, uMat sh *ᵥ f a = f a) ∧ uMat sh *ᵥ z = z`. Rewrite using `[hush]`. Conclude with `rev_UW hF hz hh'`.

Establish `hNm : InN (eps48 k r) e z (uMat sm)` using `by rw [husm]; exact rev_N hF hz hzB0 hm'`. Establish `hs_eq : s = sh * sm`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show uMat s = uMat sh * uMat sm`.

Rewrite using `[hush, husm]`. Establish `e1 : uMat s = Qm e f wf (z0v T z) * (Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z)) * Qi (eps48 k r) e f wf (z0v T z)`. Simplify using `only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]`. Rewrite using `[e1, hsm]`.

Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc (Qm e f wf (z0v T z) * h') (Qi (eps48 k r) e f wf (z0v T z)) (Qm e f wf (z0v T z)), Qi_mul_Qm hF, Matrix.mul_one]`. Establish `hnn : InN (eps48 k r) e z (uMat (sh * sm * sh⁻¹))` using `hP.2.2.2 sh hfix sm hNm`. Establish `hs2 : s = sh * sm * sh⁻¹ * sh` using `by rw [hs_eq]; group`. Rewrite using `[hs2, hWe _ hnn sh hfix x, ← hs2]`.

Unfold `piB`. Rewrite using `[hush]`. Take `⟨hwt, α, Ω, a, hΩc, h1Ω, hαm, hαs, hαb, hαr⟩` from `locUniq_gen hBW hM1 hB hCW hWl hk hke hT hgg hF hu hl hI hH hGap hga hok hDS hw hπ hS' hQ hWc hWe' hWr hL0 hLt`. Use `⟨?_, α, Ω, a, hΩc, h1Ω, hαm, hαs, hαb, hαr⟩` and prove the remaining obligations. Establish `hn0 : 0 < 2 * r + k + 1` using `by omega`.

Establish `hne1 : Nonempty {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)}` using `⟨⟨1, inS_one⟩⟩`. Establish `hne2 : Nonempty (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T))`. Use `⟨⟨1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[heq]`. Conclude with `⟨1, hP.2.2.1.1, 1, fix_one, (one_mul 1).symm⟩`.

Establish `hge1 : ∀ x, 1 ≤ ⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))` using `fun x => le_ciInf fun t => Formalism.L2.SG.WuDecayPf.one_le_opn hn0 _`. Establish `hle : ∀ x, (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ≤ nuLoc (e` using `e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x := by`. Introduce `x`. Use `le_ciInf fun t => ?_` and prove the remaining obligations. Establish `ht : InS e z (uMat (t : Formalism.REAL.UJ (eps48 k r)))` using `inS_of_HNset hF hz hzB0 ⟨_, rfl⟩ t.2`.

Conclude with `ciInf_le (f := fun t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)} => opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ⟨0, by rintro _ ⟨i, rfl⟩; exact Formalism.L2.SG.WuDecayPf.opn_nonneg _⟩ ⟨t, ht⟩`. Establish `hN1 : 0 ≤ N1H k r` using `by unfold N1H; positivity`. Use `lt_of_le_of_lt (lintegral_mono fun x => ?_) hwt` and prove the remaining obligations. Use `gcongr ‖W x‖ₑ * ?_`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem locUniq_n (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists) (hHN : LocHNProps)
    {k r n : ℕ} (hn : n = 2 * r + k + 1) (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hgg : 0 < gg)
    (ε : Fin n → Bool) (hε : ∀ i, ε i = eps48 k r (Fin.cast hn i))
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (wf : Fin k → Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z (wf a) = 0)
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {h : ℝ} (hga : Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) (lam48 k r v b) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (lam : Fin n → ℝ) (hlam : ∀ i, lam i = lam48 k r v b (Fin.cast hn i))
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    (πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)) (hπ : IsHCTypeU k u πl)
    (μS ν : Measure (Formalism.REAL.UJ ε))
    (hS : SigmaFinite μS ∧ μS ≠ 0 ∧
      μS {s | ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h}ᶜ = 0 ∧
      ∀ s ∈ {s | ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h}, μS.map (fun x => s * x) = μS)
    (hQ : ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ x, (∫⁻ s, F (s * x) ∂μS) ∂ν)
    (W : Formalism.REAL.UJ ε → Vl) (hWc : Continuous W)
    (hWe : ∀ m : Formalism.REAL.UJ ε, InN ε e z (uMat m) → ∀ h : Formalism.REAL.UJ ε,
      ((∀ a, uMat h *ᵥ e a = e a) ∧ (∀ a, uMat h *ᵥ f a = f a) ∧ uMat h *ᵥ z = z) → ∀ x,
      W (m * h * x) = psiR ε gg e f z (uMat (m * h)) • πl (fun a b => hJ ε (wf a) (uMat h *ᵥ wf b)) (W x))
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG ε) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG ε) = W x)
    (hL0 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ 0) (hLt : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ ⊤) (N : ℝ) (hN : N ≤ N1H k r) :
    (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal
        ((⨅ t : {s : Formalism.REAL.UJ ε | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ ε) * x))) ^ N) ∂ν < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ ε → ℂ) (Ω : Set (Formalism.REAL.UJ ε)) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG ε) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG ε) = W x := by
  subst hn
  have hε' : ε = eps48 k r := funext fun i => by rw [hε i]; rfl
  subst hε'
  have hlam' : lam = lam48 k r v b := funext fun i => by rw [hlam i]; rfl
  subst hlam'
  have hF := isFrameJ_of (ε := eps48 k r) e f z wf hT hee hff hef hez hfz hzz hww hew hfw hzw
  have hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (Real.sqrt T)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hT).ne'
    exact_mod_cast this
  have hP := hHN k r (eps48 k r) e f wf (z0v T z) z _ hF hc rfl
  have heq : HNset (eps48 k r) e f wf (z0v T z) (zBv k r T) =
      {s | ∃ m ∈ {g : Formalism.REAL.UJ (eps48 k r) | InN (eps48 k r) e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ (eps48 k r) | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧
          uMat g *ᵥ z = z}, s = m * h} := Set.ext fun s => HNset_eq_NH hHN hT hF s
  have hS' : IsLocHaar (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) μS := by
    obtain ⟨h1, h2, h3, h4⟩ := hS
    exact ⟨h1, h2, by rw [heq]; exact h3, fun s hs => h4 s (heq ▸ hs)⟩
  have hz : (Qm e f wf (z0v T z)) *ᵥ (zBv k r T) = z := Qm_zB hT z
  have hzB0 := inWb_zB (k := k) (r := r) T
  have hWe' : ∀ s x : Formalism.REAL.UJ (eps48 k r), ∀ h' ∈ UWset k r (zBv k r T), ∀ m' ∈ Nset k r,
      Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h' * m' →
      W (s * x) = psiR (eps48 k r) gg e f z (uMat s) • piB (eps48 k r) e f wf (z0v T z) πl h' (W x) := by
    intro s x h' hh' m' hm' hsm
    set sh : Formalism.REAL.UJ (eps48 k r) := toUJ (Qm e f wf (z0v T z) * h' * Qi (eps48 k r) e f wf (z0v T z))
      (conjQ_UJ hF hh'.1) with hsh
    set sm : Formalism.REAL.UJ (eps48 k r) := toUJ (Qm e f wf (z0v T z) * m' * Qi (eps48 k r) e f wf (z0v T z))
      (conjQ_UJ hF hm'.1) with hsm'
    have hush : uMat sh = Qm e f wf (z0v T z) * h' * Qi (eps48 k r) e f wf (z0v T z) := uMat_toUJ _ _
    have husm : uMat sm = Qm e f wf (z0v T z) * m' * Qi (eps48 k r) e f wf (z0v T z) := uMat_toUJ _ _
    have hfix : (∀ a, uMat sh *ᵥ e a = e a) ∧ (∀ a, uMat sh *ᵥ f a = f a) ∧ uMat sh *ᵥ z = z := by
      rw [hush]; exact rev_UW hF hz hh'
    have hNm : InN (eps48 k r) e z (uMat sm) := by rw [husm]; exact rev_N hF hz hzB0 hm'
    have hs_eq : s = sh * sm := by
      apply Subtype.ext; apply Units.ext
      show uMat s = uMat sh * uMat sm
      rw [hush, husm]
      have e1 : uMat s = Qm e f wf (z0v T z) * (Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z)) *
          Qi (eps48 k r) e f wf (z0v T z) := by
        simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
        rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
      rw [e1, hsm]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (Qm e f wf (z0v T z) * h') (Qi (eps48 k r) e f wf (z0v T z)) (Qm e f wf (z0v T z)),
        Qi_mul_Qm hF, Matrix.mul_one]
    have hnn : InN (eps48 k r) e z (uMat (sh * sm * sh⁻¹)) := hP.2.2.2 sh hfix sm hNm
    have hs2 : s = sh * sm * sh⁻¹ * sh := by rw [hs_eq]; group
    rw [hs2, hWe _ hnn sh hfix x, ← hs2]
    unfold piB
    rw [hush]
  obtain ⟨hwt, α, Ω, a, hΩc, h1Ω, hαm, hαs, hαb, hαr⟩ := locUniq_gen hBW hM1 hB hCW hWl hk hke hT hgg hF hu hl hI
    hH hGap hga hok hDS hw hπ hS' hQ hWc hWe' hWr hL0 hLt
  refine ⟨?_, α, Ω, a, hΩc, h1Ω, hαm, hαs, hαb, hαr⟩
  have hn0 : 0 < 2 * r + k + 1 := by omega
  have hne1 : Nonempty {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)} := ⟨⟨1, inS_one⟩⟩
  have hne2 : Nonempty (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) := by
    refine ⟨⟨1, ?_⟩⟩
    rw [heq]
    exact ⟨1, hP.2.2.1.1, 1, fix_one, (one_mul 1).symm⟩
  have hge1 : ∀ x, 1 ≤ ⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x)) := fun x =>
    le_ciInf fun t => Formalism.L2.SG.WuDecayPf.one_le_opn hn0 _
  have hle : ∀ x, (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ≤
      nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x := by
    intro x
    refine le_ciInf fun t => ?_
    have ht : InS e z (uMat (t : Formalism.REAL.UJ (eps48 k r))) := inS_of_HNset hF hz hzB0 ⟨_, rfl⟩ t.2
    exact ciInf_le (f := fun t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)} =>
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x)))
      ⟨0, by rintro _ ⟨i, rfl⟩; exact Formalism.L2.SG.WuDecayPf.opn_nonneg _⟩ ⟨t, ht⟩
  have hN1 : 0 ≤ N1H k r := by unfold N1H; positivity
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hwt
  gcongr ‖W x‖ₑ * ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ^ N
      ≤ (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
          opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ^ N1H k r :=
        Real.rpow_le_rpow_of_exponent_le (hge1 x) hN
    _ ≤ nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r :=
        Real.rpow_le_rpow (by linarith [hge1 x]) (hle x) hN1

def LocUniqStep : Prop :=
  BesselNVGap → CoefWeightedLoc → WlocExists → Formalism.L2.SG.LocWSOf.BesselOfW → CompanionTheory.Lime.BM.UniqGap →
    ∀ (D : Formalism.BasicNotions.D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u : D.what₂.Word)
      (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞), QuotWit X u μS νl C →
      ∀ v (W : Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v), Continuous W → LocEquivW X u v W → LocReprodW X u v W →
        ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(νl v) ≠ 0 → ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(νl v) ≠ ⊤ → LocConcl X u v (νl v) W

/- English proof (translation)
Introduce `hB hCW hWl hBW hM1 D hG X u μS νl C hQW v W hWc hWe hWr hL0 hLt`. Take `⟨-, -, hloc, -⟩` from `hQW`. Take `⟨hSv, hQv⟩` from `hloc v`. Establish `hk : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hN1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1` using `by rw [dimS D]; exact hG.1`.

Establish `hT : (0 : ℝ) < ((D.mem u).A.T : ℝ)` using `by exact_mod_cast (D.mem u).A.T_prime.pos`. Establish `hgg : 0 < X.B.g`. Rewrite using `[X.g_eq]`. Conclude with `Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos`. Establish `R` using `fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q`.

Establish `hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0` using `fun a b => by`. Use `R (X.eX a) (X.eX b)` as an intermediate fact. Rewrite `this` using `[X.ee, map_zero]`. Conclude with `this`. Establish `hff : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0` using `fun a b => by`.

Use `R (X.fY a) (X.fY b)` as an intermediate fact. Rewrite `this` using `[X.ff, map_zero]`. Conclude with `this`. Establish `hef : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0` using `fun a b => by`. Apply the tactic sequence `have := R (X.eX a) (X.fY b); rw [X.ef] at this; rw [show X.eR a = X.crd (X.eX a) from rfl, show X.fR b = X.crd (X.fY b) from rfl, this]; split_ifs <;> simp`.

Establish `hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0` using `fun a => by`. Use `R (X.eX a) (X.zu u)` as an intermediate fact. Rewrite `this` using `[(X.zu_orth u a).1, map_zero]`. Conclude with `this`. Establish `hfz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0` using `fun a => by`.

Use `R (X.fY a) (X.zu u)` as an intermediate fact. Rewrite `this` using `[(X.zu_orth u a).2, map_zero]`. Conclude with `this`. Establish `hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(((D.mem u).A.T : ℝ) : ℂ)`. Use `R (X.zu u) (X.zu u)` as an intermediate fact.

Rewrite `this` using `[X.zu_norm, map_neg, map_natCast]`. Rewrite using `[show X.zR u = X.crd (X.zu u) from rfl, this]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hw1` using `X.wfr_on u v`.

Establish `hew : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr u v a) = 0` using `fun c a => ((X.wfr_perp u v a).1 c).1`. Establish `hfw : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr u v a) = 0` using `fun c a => ((X.wfr_perp u v a).1 c).2`. Establish `hzw : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0` using `fun a => (X.wfr_perp u v a).2`. Establish `hu` using `Formalism.MainNotions.uS_hc D u (X.pl v)`. Establish `hl : Formalism.QuantumDeterminants.IsHCParam (lam48 D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v)))`.

Rewrite using `[Formalism.MainNotions.lambda_highest_weight_eq]`. Conclude with `Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc (X.pl v))`. Establish `hm` using `Formalism.MainNotions.two_rS_add_two D`. Establish `hI : InterlacingCondition D.R.k D.R.rS (Formalism.MainNotions.S.uS D u (X.pl v)) (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v))`. Use `⟨fun i => ?_, fun h => ?_⟩` and prove the remaining obligations.

Establish `h1` using `(D.hcW u (X.pl v)).u_gt_v i`. Establish `h2` using `(D.hcW u (X.pl v)).v_gt_u i`. Rewrite `h1`, `h2` using `[D.hcW_v u (X.pl v)]`. Simplify using `only [Formalism.MainNotions.v48, Formalism.MainNotions.S.uS]`. Conclude with `⟨by exact_mod_cast h1, by exact_mod_cast h2⟩`.

Establish `h1` using `(D.hcW u (X.pl v)).u_last_gt h (by omega)`. Rewrite `h1` using `[D.hcW_b u (X.pl v)]`. Simplify using `only [Formalism.MainNotions.b48, Formalism.MainNotions.S.uS]`. Establish `e : (Fin.cast hm ⟨0, by omega⟩ : Fin D.R.m) = ⟨0, by omega⟩` using `rfl`. Rewrite using `[e]`.

Conclude with `h1` after adjusting the coercions. Establish `hH` using `Formalism.MainNotions.LeviCoordinates.halfInt_of_integrality _ _ _ _ _ hu hl`. Establish `hGap` using `gapBig_of_gapHyp D hG (X.pl v)`. Establish `hga` using `Formalism.MainNotions.gap_at_least_of_low_gap D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v)) _ hk hl.1 (lowGap_of_gapHyp D hG (X.pl v))`. Establish `hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (16 * (D.R.r : ℝ) ^ 19)`.

Use `gapOK_of_big D.R.k D.R.rS hk hN1801` as an intermediate fact. Rewrite `this` using `[dimS D]`. Then use the resulting hypothesis. Establish `hNH : NHloc X u v = {s | ∃ m ∈ {g : Formalism.REAL.UJ (X.B.I.ε v) | InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat g)}, ∃ h ∈ {g : Formalism.REAL.UJ (X.B.I.ε v) | (∀ a, uMat g *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧ (∀ a, uMat g *ᵥ rv X.B.I v ( …`. Unfold `NHloc`. Rewrite using `[Hloc_eq]`.

Both sides reduce to the same expression. Take `⟨h1, h2, h3, h4⟩` from `hSv`. Rewrite `h3`, `h4` using `[hNH]`. Establish `hWe' : ∀ m : Formalism.REAL.UJ (X.B.I.ε v), InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat m) → ∀ h : Formalism.REAL.UJ (X.B.I.ε v), ((∀ a, uMat h *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧ (∀ a, uMat h *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a) …`. Introduce `m hm h hh x`.

Establish `hh' : h ∈ Hloc X u v` using `by rw [Hloc_eq]; exact hh`. Establish `hmat : matW X.B.I (X.wfr u v) v (single X v h) = fun a b => hJ (X.B.I.ε v) (X.wfr u v a) (uMat h *ᵥ X.wfr u v b)`. Use function extensionality and compare the values at `a b`. Simplify using `[matW, single]`. Rewrite using `[hWe m hm h hh' x, hmat]`.

Both sides reduce to the same expression. Establish `key` using `locUniq_n hBW hM1 hB hCW hWl Formalism.L2.SG.Pf.WFL.locHNProps_holds (hdim X) hk D.R.k_even hT hgg (X.B.I.ε v) (eps_cast X v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v) hee hff hef hez hfz hzz hw1 hew hfw hzw hu hl hI hH hGap h …`. Conclude with `key`.
-/
theorem local_uniqueness_reduction : LocUniqStep := by
  intro hB hCW hWl hBW hM1 D hG X u μS νl C hQW v W hWc hWe hWr hL0 hLt
  obtain ⟨-, -, hloc, -⟩ := hQW
  obtain ⟨hSv, hQv⟩ := hloc v
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hN1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by rw [dimS D]; exact hG.1
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hgg : 0 < X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have R := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    have := R (X.eX a) (X.eX b); rw [X.ee, map_zero] at this; exact this
  have hff : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b => by
    have := R (X.fY a) (X.fY b); rw [X.ff, map_zero] at this; exact this
  have hef : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
    fun a b => by
      have := R (X.eX a) (X.fY b); rw [X.ef] at this; rw [show X.eR a = X.crd (X.eX a) from rfl,
        show X.fR b = X.crd (X.fY b) from rfl, this]; split_ifs <;> simp
  have hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.eX a) (X.zu u); rw [(X.zu_orth u a).1, map_zero] at this; exact this
  have hfz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.fY a) (X.zu u); rw [(X.zu_orth u a).2, map_zero] at this; exact this
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(((D.mem u).A.T : ℝ) : ℂ) := by
    have := R (X.zu u) (X.zu u); rw [X.zu_norm, map_neg, map_natCast] at this
    rw [show X.zR u = X.crd (X.zu u) from rfl, this]; push_cast; rfl
  have hw1 := X.wfr_on u v
  have hew : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).1
  have hfw : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).2
  have hzw : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := fun a => (X.wfr_perp u v a).2

  have hu := Formalism.MainNotions.uS_hc D u (X.pl v)
  have hl : Formalism.QuantumDeterminants.IsHCParam (lam48 D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v))) := by
    rw [Formalism.MainNotions.lambda_highest_weight_eq]; exact Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc (X.pl v))
  have hm := Formalism.MainNotions.two_rS_add_two D
  have hI : InterlacingCondition D.R.k D.R.rS (Formalism.MainNotions.S.uS D u (X.pl v)) (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v)) := by
    refine ⟨fun i => ?_, fun h => ?_⟩
    · have h1 := (D.hcW u (X.pl v)).u_gt_v i
      have h2 := (D.hcW u (X.pl v)).v_gt_u i
      rw [D.hcW_v u (X.pl v)] at h1 h2
      simp only [Formalism.MainNotions.v48, Formalism.MainNotions.S.uS]
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · have h1 := (D.hcW u (X.pl v)).u_last_gt h (by omega)
      rw [D.hcW_b u (X.pl v)] at h1
      simp only [Formalism.MainNotions.b48, Formalism.MainNotions.S.uS]
      have e : (Fin.cast hm ⟨0, by omega⟩ : Fin D.R.m) = ⟨0, by omega⟩ := rfl
      rw [e]
      exact_mod_cast h1
  have hH := Formalism.MainNotions.LeviCoordinates.halfInt_of_integrality _ _ _ _ _ hu hl
  have hGap := gapBig_of_gapHyp D hG (X.pl v)
  have hga := Formalism.MainNotions.gap_at_least_of_low_gap D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v)) _ hk hl.1
    (lowGap_of_gapHyp D hG (X.pl v))
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (16 * (D.R.r : ℝ) ^ 19) := by
    have := gapOK_of_big D.R.k D.R.rS hk hN1801
    rwa [dimS D] at this

  have hNH : NHloc X u v = {s | ∃ m ∈ {g : Formalism.REAL.UJ (X.B.I.ε v) | InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (rv X.B.I v (X.zR u)) (uMat g)}, ∃ h ∈ {g : Formalism.REAL.UJ (X.B.I.ε v) |
        (∀ a, uMat g *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
        (∀ a, uMat g *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧
        uMat g *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)}, s = m * h} := by
    unfold NHloc; rw [Hloc_eq]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := hSv
  rw [hNH] at h3 h4

  have hWe' : ∀ m : Formalism.REAL.UJ (X.B.I.ε v), InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (uMat m) → ∀ h : Formalism.REAL.UJ (X.B.I.ε v),
      ((∀ a, uMat h *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
        (∀ a, uMat h *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧
        uMat h *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) → ∀ x,
      W (m * h * x) = psiR (X.B.I.ε v) X.B.g (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
        (rv X.B.I v (X.zR u)) (uMat (m * h)) •
        X.piLoc u v (fun a b => hJ (X.B.I.ε v) (X.wfr u v a) (uMat h *ᵥ X.wfr u v b)) (W x) := by
    intro m hm h hh x
    have hh' : h ∈ Hloc X u v := by rw [Hloc_eq]; exact hh
    have hmat : matW X.B.I (X.wfr u v) v (single X v h) =
        fun a b => hJ (X.B.I.ε v) (X.wfr u v a) (uMat h *ᵥ X.wfr u v b) := by
      funext a b; simp [matW, single]
    rw [hWe m hm h hh' x, hmat]
    rfl
  have key := locUniq_n hBW hM1 hB hCW hWl Formalism.L2.SG.Pf.WFL.locHNProps_holds (hdim X) hk D.R.k_even hT hgg
    (X.B.I.ε v) (eps_cast X v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u)) (X.wfr u v) hee hff hef hez hfz hzz hw1 hew hfw hzw hu hl hI hH hGap hga hok
    (X.B.lam v) (lam_cast X v) (X.B.σ v) (X.ds v) (X.B.w v) (X.low v) (X.piLoc u v) (X.piLoc_type u v)
    (μS v) (νl v) ⟨h1, h2, h3, h4⟩ hQv W hWc hWe' hWr hL0 hLt (N1 X) (first_count_le_log X)
  exact key

/- English proof (translation)
Introduce `D hG X u μS νl C hQ v`. Conclude with `hU hB hC hW hBW hM1 D hG X u μS νl C hQ v (X.Wloc u v) (X.Wloc_cont u v) (fun m hm h hh x => locEquiv X u v m hm h hh x) (hR D hG X u μS νl C hQ v) (localRepresentationL2 X u hQ v).1 (localRepresentationL2 X u hQ v).2`.
-/
theorem locDecayStep_of (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hR : LocReprodStep) (hU : LocUniqStep) : LocDecayStep := by
  intro D hG X u μS νl C hQ v
  exact hU hB hC hW hBW hM1 D hG X u μS νl C hQ v (X.Wloc u v) (X.Wloc_cont u v)
    (fun m hm h hh x => locEquiv X u v m hm h hh x) (hR D hG X u μS νl C hQ v)
    (localRepresentationL2 X u hQ v).1 (localRepresentationL2 X u hQ v).2

/- English proof (translation)
The claim follows from `wuDecayOfGap_of_steps hC (quotAll_of hQK locHNProps_holds hNU) (locDecayStep_of hB hC hW (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_gap hM1) hM1 (locReprodStep_of hS) local_uniqueness_reduction)`.
-/
theorem wuDecay_gap (hM1 : CompanionTheory.Lime.BM.UniqGap) (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hQK : QuotProdK) (hNU : NUnimodLoc) (hS : LocScalarStep) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  wuDecayOfGap_of_steps hC (quotAll_of hQK locHNProps_holds hNU)
    (locDecayStep_of hB hC hW (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_gap hM1) hM1 (locReprodStep_of hS) local_uniqueness_reduction)

end BM

end Formalism.L2.SG.Pf.WuDec
