import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXGauge
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCW

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

/- English proof (translation)
Introduce `φ hφ`. Rewrite using `[hD φ hφ]`. Use `setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun c hc => ?_)` and prove the remaining obligations. Take `⟨s₁, hs₁, s₁', hs₁', hg⟩` from `Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds n r k ε e z z' T T' sc hF c hc (h0 c) (h c) (hh0 c hc) (hh c hc)`. Rewrite using `[hg, JL.inner_dc μS μS' s₁ s₁' (h0 c) (hR s₁ hs₁) (hR' s₁' hs₁') φ]`.
-/
theorem disint_switch {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' sc C : ℝ}
    (hF : FrameLoc ε k e z z' T T') {μS μS' : Measure (Formalism.REAL.UJ ε)}
    (hR : ∀ s ∈ SLoc ε e z, μS.map (fun x => x * s) = μS) (hR' : ∀ s ∈ SLoc ε e z', μS'.map (fun x => x * s) = μS')
    {h0 h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} (hh0 : IsSecLoc ε sc e z z' T T' h0)
    (hh : IsSecLoc ε sc e z z' T T' h) (hD : DisintLoc ε k T T' μS μS' h0 C) : DisintLoc ε k T T' μS μS' h C := by
  intro φ hφ
  rw [hD φ hφ]
  refine setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun c hc => ?_)
  obtain ⟨s₁, hs₁, s₁', hs₁', hg⟩ :=
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds n r k ε e z z' T T' sc hF c hc (h0 c) (h c) (hh0 c hc) (hh c hc)
  rw [hg, JL.inner_dc μS μS' s₁ s₁' (h0 c) (hR s₁ hs₁) (hR' s₁' hs₁') φ]

/- English proof (translation)
Introduce `k r ε e f wf z0 zB zB' hF hk hz hz' hT hT' hG μH μH' hH hH' a a' ha ha' hma hma' κ hκ h hh`. Establish `emb` using `embQ hF`. Establish `hFL` using `frameX_of hF hk hz hz' hT hT'`. Establish `hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0` using `Matrix.inv_eq_left_inv (Qi_mul_Qm hF)`. Establish `hdet : IsUnit (Qm e f wf z0).det` using `Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)`.

Establish `hpsi : JL.psiP (ε` using `ε) (Qm e f wf z0) = cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) := by`. Use function extensionality and compare the values at `u`. Use `show (fun i j => ((Qm e f wf z0)⁻¹ * uMat u * Qm e f wf z0) i j) = (Qi ε e f wf z0 * uMat u * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`. Rewrite using `[hQinv]`. Take `⟨μsec, hμ⟩` from `JL.secWb_holds k r zB zB' hk hz hz' hT hT'`.

Set `μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ` to `fun ζ => if Tz k r zB * Tz k r zB' < Complex.normSq ζ then μsec ζ else 1`. Establish `hμs : IsSection k r zB zB' μs`. Use `⟨fun i j => (hμ.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩` and prove the remaining obligations. Establish `hζ' : Tz k r zB * Tz k r zB' < Complex.normSq ζ` using `hζ`. Simplify using `only [μs, if_pos hζ']`.

Simplify using `only [μs, if_pos hζ]`. Conclude with `hμ.2 ζ hζ`. Establish `hU : ∀ ζ, (μs ζ)ᴴ * Hb k * μs ζ = Hb k`. Introduce `ζ`. Distinguish the cases in `hζ : Tz k r zB * Tz k r zB' < Complex.normSq ζ`.

Simplify using `only [μs, if_pos hζ]`. Conclude with `(hμ.2 ζ hζ).1`. Simplify using `only [μs, if_neg hζ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hMuj : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) → Formalism.REAL.inUJ ε (Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹)` using `fun q hq => JL.inUJ_conj (gramQ hF) hdet (JL.bigMem_holds k r q.1 (μs q.2) hq (hU q.2))`. Set `h0 : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε` to `fun c => if hc : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 then JL.ujOf _ (hMuj (JL.qOf r 1 c) hc) else 1`.

Establish `hh0q : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) → uMat (h0 (JL.coordSc r 1 q)) = Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹`. Introduce `q hq`. Establish `hq' : ∀ a, (JL.qOf r 1 (JL.coordSc r 1 q)).1 a ≠ 0` using `by rw [JL.qOf_coordSc r one_pos]; exact hq`. Simplify using `only [h0, dif_pos hq', JL.uMat_ujOf, JL.qOf_coordSc r one_pos]`. Establish `hh0 : IsSecLoc ε 1 e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') h0`.

Introduce `c hc`. Establish `hq1 : ∀ a, (JL.qOf r 1 c).1 a ≠ 0` using `fun a => mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ one_ne_zero)) (hc.1 _)`. Establish `hζ : Tz k r zB * Tz k r zB' < Complex.normSq (JL.qOf r 1 c).2`. Establish `h2` using `hc.2`. Rewrite `h2` using `[JL.gv_diag_eq]`.

Break down `pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨_, h3⟩ | ⟨h3, _⟩` into its components or cases. Use `show Tz k r zB * Tz k r zB' < Complex.normSq (c (Fin.last r))`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h3 (not_lt.2 (sq_nonneg _))`. Establish `he0` using `hh0q (JL.qOf r 1 c) hq1`.

Rewrite `he0` using `[JL.coordSc_qOf r one_pos]`. Use `show Zhat ε (famSc 1 e (Qm e f wf z0 *ᵥ zB)) (famSc 1 e (Qm e f wf z0 *ᵥ zB')) (uMat (h0 c)) = Matrix.diagonal c`. Rewrite using `[he0, (JL.zBig r k ε e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') zB zB' (Qm e f wf z0) 1 (gramQ hF) hdet (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz hz' rfl rfl one_pos μs hμs (JL.qOf r 1 c) hq1 hζ).2, JL.coordSc_qOf r one_pos]`. Establish `hfin : μH Set.univ ≠ ⊤` using `by rw [hma]; exact ENNReal.ofReal_ne_top`. Establish `hfin' : μH' Set.univ ≠ ⊤` using `by rw [hma']; exact ENNReal.ofReal_ne_top`.

Use `disint_switch hFL (fun s hs => rightX_of hF hz hT hH hfin κ hκ s hs) (fun s hs => rightX_of hF hz' hT' hH' hfin' κ hκ s hs) hh0 hh ?_` and prove the remaining obligations. Establish `hW` using `measW_of hF hH`. Establish `hW'` using `measW_of hF hH'`. Establish `hWa : (μH.map (cM (ε` using `ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a := by`. Rewrite using `[emb.map_apply, Set.preimage_univ, hma]`.

Establish `hWa' : (μH'.map (cM (ε` using `ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a' := by`. Rewrite using `[emb.map_apply, Set.preimage_univ, hma']`. Establish `hJG` using `hJ k r zB zB' hk hz hz' hT hT' _ _ _ (gaugeTr_of hF hG) hW hW' a a' ha ha' hWa hWa' κ hκ μs hμs`. Establish `hS1` using `measS_of hF hz hT hH κ hκ`. Establish `hS2` using `measS_of hF hz' hT' hH' κ hκ`.

Introduce `φ hφ`. Use `set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ`. Set `φh : Mt k r → ℝ≥0∞` to `Function.extend Ψ φ 0`. Establish `hφh : Measurable φh` using `emb.measurable_extend hφ measurable_const`. Establish `hext : ∀ u, φh (Ψ u) = φ u` using `fun u => emb.injective.extend_apply φ 0 u`.

Establish `hgU : 0 < Formalism.MainNotions.S.Gauge.gaugeU ε` using `hG.2`. Establish `hL : ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε) * ∫⁻ x, φh x ∂(((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map Ψ)`. Rewrite using `[emb.lintegral_map, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hgU).ne' ENNReal.ofReal_ne_top, one_mul]`. Simplify using `only [hext]`. Rewrite using `[hL, hJG φh hφh, ← hS1, ← hS2]`.

Use `set F : (Fin (r + 1) → ℂ) → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹) ∂(muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)) ∂(muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)) with hF0`. Establish `hpt : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) * ∫⁻ s, ∫⁻ s', φh (fun i j => (Matrix.of s * bigCell k r q.1 (μs q.2) * (Matrix.of s')⁻¹) i j) ∂((muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ) ∂((muSL μH (ENNReal.ofReal κ • refN ε e f …`. Introduce `q`. Distinguish the cases in `hq : ∀ a, q.1 a ≠ 0`. Use `congr 1`.

Rewrite using `[emb.lintegral_map]`. Use `lintegral_congr fun u => ?_` and prove the remaining obligations. Rewrite using `[emb.lintegral_map]`. Use `lintegral_congr fun u' => ?_` and prove the remaining obligations. Establish `hw` using `JL.psiP_mul_B hdet u u' (bigCell k r q.1 (μs q.2)) (h0 (JL.coordSc r 1 q)) (hh0q q hq)`.

Rewrite `hw` using `[hpsi]`. Rewrite using `[hw, hext]`. Use `push_neg at hq`. Take `⟨a, ha0⟩` from `hq`. Rewrite using `[JL.bcWeight_zero _ _ q a ha0, ENNReal.ofReal_zero, zero_mul, zero_mul]`.

Rewrite using `[lintegral_congr hpt, JL.coordinate_weight_lintegral r k (Tz k r zB) (Tz k r zB') hk hT hT' F]`. Establish `hK0` using `Jac.jacConst_nonneg (k := k) (r := r) hT hT' ha ha' hκ`. Establish `hV1` using `Jac.volU_pos (k - 1)`. Establish `hCX : Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 / ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) = Formalism.MainNotions.S.Gauge.gaugeU ε * (jacConst k r (Tz k r zB) (Tz …`. Unfold `jacConst`.

Clear the denominators using the available nonvanishing facts. Establish `hC0 : 0 ≤ Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 / ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2)`. Rewrite using `[hCX]`. Check the signs of the components of the expression. Establish `hpt2 : ∀ c, ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 / ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) * wtLoc k (Tz k r zB) (Tz k r zB') c) * F c = ENNRe …` using `fun c => by`.

Rewrite using `[ENNReal.ofReal_mul hC0, mul_assoc]`. Rewrite using `[lintegral_congr hpt2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCX, ENNReal.ofReal_mul hgU.le, ENNReal.ofReal_mul hK0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacLocX_of (hJ : JacGauge) : JacLocX := by
  intro k r ε e f wf z0 zB zB' hF hk hz hz' hT hT' hG μH μH' hH hH' a a' ha ha' hma hma' κ hκ h hh
  have emb := embQ hF
  have hFL := frameX_of hF hk hz hz' hT hT'
  have hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0 := Matrix.inv_eq_left_inv (Qi_mul_Qm hF)
  have hdet : IsUnit (Qm e f wf z0).det := Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)
  have hpsi : JL.psiP (ε := ε) (Qm e f wf z0) = cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) := by
    funext u
    show (fun i j => ((Qm e f wf z0)⁻¹ * uMat u * Qm e f wf z0) i j) =
      (Qi ε e f wf z0 * uMat u * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    rw [hQinv]

  obtain ⟨μsec, hμ⟩ := JL.secWb_holds k r zB zB' hk hz hz' hT hT'
  let μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun ζ =>
    if Tz k r zB * Tz k r zB' < Complex.normSq ζ then μsec ζ else 1
  have hμs : IsSection k r zB zB' μs := by
    refine ⟨fun i j => (hμ.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩
    · have hζ' : Tz k r zB * Tz k r zB' < Complex.normSq ζ := hζ
      simp only [μs, if_pos hζ']
    · simp only [μs, if_pos hζ]
      exact hμ.2 ζ hζ
  have hU : ∀ ζ, (μs ζ)ᴴ * Hb k * μs ζ = Hb k := by
    intro ζ
    by_cases hζ : Tz k r zB * Tz k r zB' < Complex.normSq ζ
    · simp only [μs, if_pos hζ]; exact (hμ.2 ζ hζ).1
    · simp only [μs, if_neg hζ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hMuj : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      Formalism.REAL.inUJ ε (Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹) := fun q hq =>
    JL.inUJ_conj (gramQ hF) hdet (JL.bigMem_holds k r q.1 (μs q.2) hq (hU q.2))

  let h0 : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε := fun c =>
    if hc : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 then JL.ujOf _ (hMuj (JL.qOf r 1 c) hc) else 1
  have hh0q : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      uMat (h0 (JL.coordSc r 1 q)) = Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹ := by
    intro q hq
    have hq' : ∀ a, (JL.qOf r 1 (JL.coordSc r 1 q)).1 a ≠ 0 := by rw [JL.qOf_coordSc r one_pos]; exact hq
    simp only [h0, dif_pos hq', JL.uMat_ujOf, JL.qOf_coordSc r one_pos]
  have hh0 : IsSecLoc ε 1 e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') h0 := by
    intro c hc
    have hq1 : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 := fun a =>
      mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ one_ne_zero)) (hc.1 _)
    have hζ : Tz k r zB * Tz k r zB' < Complex.normSq (JL.qOf r 1 c).2 := by
      have h2 := hc.2
      rw [JL.gv_diag_eq] at h2
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · show Tz k r zB * Tz k r zB' < Complex.normSq (c (Fin.last r)); linarith
      · exact absurd h3 (not_lt.2 (sq_nonneg _))
    have he0 := hh0q (JL.qOf r 1 c) hq1
    rw [JL.coordSc_qOf r one_pos] at he0
    show Zhat ε (famSc 1 e (Qm e f wf z0 *ᵥ zB)) (famSc 1 e (Qm e f wf z0 *ᵥ zB')) (uMat (h0 c)) = Matrix.diagonal c
    rw [he0, (JL.zBig r k ε e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') zB zB' (Qm e f wf z0) 1 (gramQ hF) hdet
      (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz hz' rfl rfl one_pos μs hμs (JL.qOf r 1 c) hq1 hζ).2,
      JL.coordSc_qOf r one_pos]

  have hfin : μH Set.univ ≠ ⊤ := by rw [hma]; exact ENNReal.ofReal_ne_top
  have hfin' : μH' Set.univ ≠ ⊤ := by rw [hma']; exact ENNReal.ofReal_ne_top
  refine disint_switch hFL (fun s hs => rightX_of hF hz hT hH hfin κ hκ s hs)
    (fun s hs => rightX_of hF hz' hT' hH' hfin' κ hκ s hs) hh0 hh ?_
  have hW := measW_of hF hH
  have hW' := measW_of hF hH'
  have hWa : (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a := by
    rw [emb.map_apply, Set.preimage_univ, hma]
  have hWa' : (μH'.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a' := by
    rw [emb.map_apply, Set.preimage_univ, hma']
  have hJG := hJ k r zB zB' hk hz hz' hT hT' _ _ _ (gaugeTr_of hF hG) hW hW' a a' ha ha' hWa hWa' κ hκ μs hμs
  have hS1 := measS_of hF hz hT hH κ hκ
  have hS2 := measS_of hF hz' hT' hH' κ hκ
  intro φ hφ
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  let φh : Mt k r → ℝ≥0∞ := Function.extend Ψ φ 0
  have hφh : Measurable φh := emb.measurable_extend hφ measurable_const
  have hext : ∀ u, φh (Ψ u) = φ u := fun u => emb.injective.extend_apply φ 0 u
  have hgU : 0 < Formalism.MainNotions.S.Gauge.gaugeU ε := hG.2
  have hL : ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε) *
      ∫⁻ x, φh x ∂(((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map Ψ) := by
    rw [emb.lintegral_map, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hgU).ne' ENNReal.ofReal_ne_top, one_mul]
    simp only [hext]
  rw [hL, hJG φh hφh, ← hS1, ← hS2]
  set F : (Fin (r + 1) → ℂ) → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹)
    ∂(muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)) ∂(muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)) with hF0
  have hpt : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) *
      ∫⁻ s, ∫⁻ s', φh (fun i j => (Matrix.of s * bigCell k r q.1 (μs q.2) * (Matrix.of s')⁻¹) i j)
        ∂((muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ)
        ∂((muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ) =
      ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) * F (JL.coordSc r 1 q) := by
    intro q
    by_cases hq : ∀ a, q.1 a ≠ 0
    · congr 1
      rw [emb.lintegral_map]
      refine lintegral_congr fun u => ?_
      rw [emb.lintegral_map]
      refine lintegral_congr fun u' => ?_
      have hw := JL.psiP_mul_B hdet u u' (bigCell k r q.1 (μs q.2)) (h0 (JL.coordSc r 1 q)) (hh0q q hq)
      rw [hpsi] at hw
      rw [hw, hext]
    · push_neg at hq
      obtain ⟨a, ha0⟩ := hq
      rw [JL.bcWeight_zero _ _ q a ha0, ENNReal.ofReal_zero, zero_mul, zero_mul]
  rw [lintegral_congr hpt, JL.coordinate_weight_lintegral r k (Tz k r zB) (Tz k r zB') hk hT hT' F]
  have hK0 := Jac.jacConst_nonneg (k := k) (r := r) hT hT' ha ha' hκ
  have hV1 := Jac.volU_pos (k - 1)
  have hCX : Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) =
      Formalism.MainNotions.S.Gauge.gaugeU ε * (jacConst k r (Tz k r zB) (Tz k r zB') a a' κ * (2 ^ (r + 1))⁻¹) := by
    unfold jacConst
    field_simp
  have hC0 : 0 ≤ Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) := by
    rw [hCX]; positivity
  have hpt2 : ∀ c, ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) * wtLoc k (Tz k r zB) (Tz k r zB') c) *
        F c =
      ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2)) *
        (ENNReal.ofReal (wtLoc k (Tz k r zB) (Tz k r zB') c) * F c) := fun c => by
    rw [ENNReal.ofReal_mul hC0, mul_assoc]
  rw [lintegral_congr hpt2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCX,
    ENNReal.ofReal_mul hgU.le, ENNReal.ofReal_mul hK0]
  ring

end Formalism.L2.SG.Pf.NcReal.JX
