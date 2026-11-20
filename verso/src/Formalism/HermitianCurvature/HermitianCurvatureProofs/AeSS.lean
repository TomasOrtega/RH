import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuadAOf

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

/- English proof (translation)
Establish `hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r D.z`. Rewrite using `[ae_iff]`. Conclude with `measure_mono_null (fun x hx => hx) D.haarW.conc`. Establish `hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r`. Rewrite using `[ae_iff]`.

Conclude with `measure_mono_null (fun x hx => hx) D.haarN.conc`. Conclude with `(Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)`.
-/
theorem ae_mem_UWset_and_mem_Nset {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] :
    ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r D.z := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => hx) D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => hx) D.haarN.conc
  exact (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)

set_option maxHeartbeats 800000 in
/- English proof (translation)
Establish `hS1'` using `hS1`. Take `⟨hl, hds, -, hG, hw0, hz1, hT, -, hπ, hW, hN, hGm, hq⟩` from `hS1'`. Establish `: SigmaFinite D.μW` using `hW.1`. Establish `: SigmaFinite D.μN` using `hN.1`. Establish `: SigmaFinite D.μG` using `hGm.1`.

Establish `hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)`. Rewrite using `[ae_iff]`. Simplify using `using hGm.2.2.1`. Establish `hw0DD` using `cmHalfIntegralGenerator_mem_algebraicClosure hds w0`. Establish `hf1` using `DDSmoothness.muSof_facts hW hN`.

Establish `hae1` using `DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf1.1 hf1.2 hq`. Distinguish the cases in `hA : ∃ v ∈ DDsp σ w0, l v ≠ 0`. Use `swap`. Use `push Not at hA`. Combine the equalities or inequalities in the displayed calculation.

Apply `lintegral_mono_ae` to reduce the goal to its premises. Use `filter_upwards [hae1] with zz hzz`. Simplify using `[hA _ (dd_stable hds hzz w0 hw0DD)]`. Use `_ < ⊤ := by simp`. Take `⟨v, hv, hlv⟩` from `hA`.

Take `⟨e0, he0, hee0⟩` from `coef_ext hds w0 w0`. Take `⟨e1, he1, hee1⟩` from `coef_ext hds v w0`. Take `⟨C0, hC0⟩` from `hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD w0 hw0DD`. Take `⟨C1, hC1⟩` from `hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv`. Establish `hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-aOf r h)` using `fun y hy => by rw [hee0 y hy]; exact hC0 y hy`.

Establish `hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h)` using `fun y hy => by rw [hee1 y hy]; exact hC1 y hy`. Establish `h4` using `gap4 hG`. Establish `hAG` using `ag_nonneg k r`. Establish `hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`. Take `⟨ee, heedef⟩ : ∃ ee : ℝ, ee = AG k r + 1` from `⟨_, rfl⟩`.

Establish `hee0' : 0 ≤ ee` using `by rw [heedef]; linarith`. Establish `heea : ee ≤ aOf r h` using `by rw [heedef]; linarith`. Establish `hLs : ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) < ⊤` using `(hGS k r D.z D.μW D.μN D.μG νq ee hz1 hT hW hN hGm hq (by rw [heedef]; linarith)).hasFiniteIntegral`. Take `⟨Ls, hLsdef⟩ : ∃ Ls : ℝ≥0∞, Ls = ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN)` from `⟨_, rfl⟩`. Rewrite `hLs` using `[← hLsdef]`.

Establish `hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ ∂D.μG < ⊤` using `(hGG k r D.μG _ hGm (by rw [heedef]; linarith)).hasFiniteIntegral`. Establish `hpUH : ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `(prod_ae hW hN).mono fun p hp => DDSmoothness.uh_mul hp.1.1 hp.2.1`. Take `⟨K1, hK1⟩ : ∃ K1 : ℝ≥0∞, K1 = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ` from `⟨_, rfl⟩`. Establish `hK : K1 * K1 ≠ ⊤` using `by rw [hK1]; simp [ENNReal.mul_eq_top]`. Establish `hA1m` using `Aext_meas he1`.

Establish `hI1m` using `Iint_meas hA1m (D.μW.prod D.μN)`. Take `⟨LL, hLL⟩ : ∃ LL : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, LL = Lam1 e0 (D.μW.prod D.μN)` from `⟨_, rfl⟩`. Establish `hLLm : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => LL t.1 t.2)`. Rewrite using `[hLL]`. Conclude with `measurable_lambda_integral he0 (D.μW.prod D.μN)`.

Establish `step1 : ∀ᵐ zz ∂νq, ∀ᵐ zz' ∂νq, ∫⁻ s, ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞) ∂(muSof D.μW D.μN) ≤ (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) …` using `by filter_upwards [hae1] with zz hzz filter_upwards [hae1] with zz' hzz'`. Establish `bl : ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz`. Rewrite using `[hK1]`. Conclude with `l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz`. Establish `bl' : ‖l (σ (Matrix.of zz') w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz'`.

Rewrite using `[hK1]`. Conclude with `l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz'`. Establish `hc : ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ≠ ⊤` using `ENNReal.mul_ne_top enorm_ne_top enorm_ne_top`. Establish `hqi` using `quad_inner1 hds w0 he0 hee0 hf1.2 hzz hzz'`. Rewrite `hqi` using `[← hLL]`.

Simplify using `only [← enorm_eq_nnnorm]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Establish `hinvR : ∀ zz, ∀ᵐ z ∂νq, ∀ᵐ q ∂(D.μW.prod D.μN), LL zz (fun i j => (Matrix.of q.1 * Matrix.of q.2 * Matrix.of z) i j) = LL zz z`. Introduce `zz`.

Rewrite using `[hLL]`. Conclude with `Filter.Eventually.of_forall fun z => (ae_mem_UWset_and_mem_Nset D).mono fun q hq0 => lambda_right_translation he0 D.haarW D.haarN hz1 hT hq0.1 hq0.2 zz z`. Establish `hinvL : ∀ᵐ z ∂νq, ∀ᵐ p ∂(D.μW.prod D.μN), (∫⁻ y, Aext e1 y * LL (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) y ∂D.μG) = ∫⁻ y, Aext e1 y * LL z y ∂D.μG`. Rewrite using `[hLL]`. Conclude with `Filter.Eventually.of_forall fun z => (prod_ae hW hN).mono fun p hp0 => lintegral_congr fun y => by rw [lambda_left_translation he0 hW hN hz1 hp0.1 hp0.2 z y]`.

Establish `hLz : ∀ zz, Measurable (fun y => LL zz y)` using `fun zz => hLLm.comp (measurable_const.prodMk measurable_id)`. Establish `hΦm : Measurable (fun x => ∫⁻ y, Aext e1 y * LL x y ∂D.μG)` using `((hA1m.comp measurable_snd).mul hLLm).lintegral_prod_right'`. Take `⟨Fx, hFx⟩ : ∃ Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Fx = fun x => ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ` from `⟨_, rfl⟩`. Establish `hFxm : Measurable Fx`. Rewrite using `[hFx]`.

Conclude with `(((gN_cont.comp mt_cont).measurable).pow_const _).enorm`. Establish `hKg' : ∫⁻ x, Fx x ∂D.μG < ⊤` using `by rw [hFx]; exact hKg`. Take `⟨c, hcdef⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal |C1| * ENNReal.ofReal |C1| * (ENNReal.ofReal |C0| * Ls)` from `⟨_, rfl⟩`. Establish `hc : c ≠ ⊤`. Rewrite using `[hcdef]`.

Conclude with `ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLs.ne)`. Establish `hgpos : ∀ x : Mx k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → 0 < B.gN x` using `fun x hx => lt_of_lt_of_le one_pos ((hNI k r).2 x hx).2`. Establish `hpt : ∀ᵐ x ∂D.μG, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ≤ ∫⁻ y, c * (Fx x * Fx y) ∂D.μG` using `by filter_upwards [hGc] with x hx`. Rewrite using `[← lintegral_const_mul' (Aext e1 x) _ (by unfold Aext; exact enorm_ne_top)]`. Apply `lintegral_mono_ae` to reduce the goal to its premises.

Use `filter_upwards [hGc] with y hy`. Establish `hL` using `lambda_integral_bound hNI hb0e hee0' heea hpUH hx hy`. Rewrite `hL` using `[← hLL, ← hLsdef]`. Establish `hx0` using `hgpos _ hx`. Establish `hy0` using `hgpos _ hy`.

Establish `w1` using `e_weight (b := ee) hb1 hx hx0`. Establish `w2` using `e_weight (b := ee) hb1 hy hy0`. Establish `split : ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) = ENNReal.ofReal |C0| * (ENNReal.ofReal (B.gN (Matrix.of x) ^ ee) * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee))`. Rewrite using `[Real.mul_rpow hx0.le hy0.le, ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]`. Establish `hFxx : Fx x = ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ` using `by rw [hFx]`.

Establish `hFxy : Fx y = ‖B.gN (Matrix.of y) ^ (-(aOf r h - ee))‖ₑ` using `by rw [hFx]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[split]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (ENNReal.ofReal |C1| * Fx x) * (ENNReal.ofReal |C1| * Fx y) * (ENNReal.ofReal |C0| * Ls) := by`.

Rewrite using `[hFxx, hFxy]`. Conclude with `mul_le_mul' (mul_le_mul' w1 w2) le_rfl`. Use `_ = c * (Fx x * Fx y) := by rw [hcdef]; ring`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Apply `lintegral_congr` to reduce the goal to its premises. Introduce `zz`. Use `congr 1`. Conclude with `unfold_Iint hq hA1m (hLz zz) (hinvR zz)`. Use `_ = (K1 * K1) * ∫⁻ x, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ∂D.μG := by`.

Use `congr 1`. Conclude with `unfold_Iint hq hA1m hΦm hinvL`. Use `_ ≤ (K1 * K1) * ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂D.μG ∂D.μG := by gcongr 1`. Conclude with `lintegral_mono_ae hpt`. Use `_ = (K1 * K1) * (c * ((∫⁻ x, Fx x ∂D.μG) * ∫⁻ y, Fx y ∂D.μG)) := by rw [final2 Fx hFxm hc]`.

Use `_ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (ENNReal.mul_lt_top hKg' hKg'))`.
-/
theorem quadB_of (hNI : NormInv) (hGS : GrowthS) (hGG : GrowthG) (hDD : DecDD) (hIn : Inputs) {k r : ℕ}
    {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    {u : Fin k → ℝ} {νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hS1 : Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq)
    {l : H → Wp}
    (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x)) :
    ∫⁻ zz, ∫⁻ zz', ∫⁻ s,
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW D.μN) ∂νq ∂νq < ⊤ := by
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, hz1, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hf1 := DDSmoothness.muSof_facts hW hN
  have hae1 := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf1.1 hf1.2 hq
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    calc _ ≤ ∫⁻ zz, (0 : ℝ≥0∞) ∂νq := by
          apply lintegral_mono_ae
          filter_upwards [hae1] with zz hzz
          simp [hA _ (dd_stable hds hzz w0 hw0DD)]
      _ < ⊤ := by simp
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨e0, he0, hee0⟩ := coef_ext hds w0 w0
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨C0, hC0⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD
    w0 hw0DD
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  have hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee0 y hy]; exact hC0 y hy
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨ee, heedef⟩ : ∃ ee : ℝ, ee = AG k r + 1 := ⟨_, rfl⟩
  have hee0' : 0 ≤ ee := by rw [heedef]; linarith
  have heea : ee ≤ aOf r h := by rw [heedef]; linarith
  have hLs : ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) < ⊤ :=
    (hGS k r D.z D.μW D.μN D.μG νq ee hz1 hT hW hN hGm hq (by rw [heedef]; linarith)).hasFiniteIntegral
  obtain ⟨Ls, hLsdef⟩ : ∃ Ls : ℝ≥0∞, Ls = ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-ee)‖ₑ ∂(D.μW.prod D.μN) :=
    ⟨_, rfl⟩
  rw [← hLsdef] at hLs
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [heedef]; linarith)).hasFiniteIntegral
  have hpUH : ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    (prod_ae hW hN).mono fun p hp => DDSmoothness.uh_mul hp.1.1 hp.2.1
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ≥0∞, K1 = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ := ⟨_, rfl⟩
  have hK : K1 * K1 ≠ ⊤ := by rw [hK1]; simp [ENNReal.mul_eq_top]
  have hA1m := Aext_meas he1
  have hI1m := Iint_meas hA1m (D.μW.prod D.μN)
  obtain ⟨LL, hLL⟩ : ∃ LL : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, LL = Lam1 e0 (D.μW.prod D.μN) := ⟨_, rfl⟩
  have hLLm : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => LL t.1 t.2) := by
    rw [hLL]; exact measurable_lambda_integral he0 (D.μW.prod D.μN)
  have step1 : ∀ᵐ zz ∂νq, ∀ᵐ zz' ∂νq, ∫⁻ s,
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW D.μN) ≤
      (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) := by
    filter_upwards [hae1] with zz hzz
    filter_upwards [hae1] with zz' hzz'
    have bl : ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz
    have bl' : ‖l (σ (Matrix.of zz') w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz' := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz'
    have hc : ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ≠ ⊤ :=
      ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    have hqi := quad_inner1 hds w0 he0 hee0 hf1.2 hzz hzz'
    rw [← hLL] at hqi
    simp only [← enorm_eq_nnnorm]
    calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ ∂(muSof D.μW D.μN)
        = ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) ∂(muSof D.μW D.μN) :=
          lintegral_congr fun s => mul_assoc _ _ _
      _ = (∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof D.μW D.μN)) *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) := lintegral_mul_const' _ _ hc
      _ = LL zz zz' * (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l (σ (Matrix.of zz') w0)‖ₑ) := by rw [hqi]
      _ ≤ LL zz zz' * ((K1 * Iint (Aext e1) (D.μW.prod D.μN) zz) * (K1 * Iint (Aext e1) (D.μW.prod D.μN) zz')) := by
          gcongr
      _ = (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) := by
          ring
  have hinvR : ∀ zz, ∀ᵐ z ∂νq, ∀ᵐ q ∂(D.μW.prod D.μN),
      LL zz (fun i j => (Matrix.of q.1 * Matrix.of q.2 * Matrix.of z) i j) = LL zz z := by
    intro zz
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (ae_mem_UWset_and_mem_Nset D).mono
      fun q hq0 => lambda_right_translation he0 D.haarW D.haarN hz1 hT hq0.1 hq0.2 zz z
  have hinvL : ∀ᵐ z ∂νq, ∀ᵐ p ∂(D.μW.prod D.μN),
      (∫⁻ y, Aext e1 y * LL (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) y ∂D.μG) =
        ∫⁻ y, Aext e1 y * LL z y ∂D.μG := by
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (prod_ae hW hN).mono
      fun p hp0 => lintegral_congr fun y => by rw [lambda_left_translation he0 hW hN hz1 hp0.1 hp0.2 z y]
  have hLz : ∀ zz, Measurable (fun y => LL zz y) := fun zz => hLLm.comp (measurable_const.prodMk measurable_id)
  have hΦm : Measurable (fun x => ∫⁻ y, Aext e1 y * LL x y ∂D.μG) :=
    ((hA1m.comp measurable_snd).mul hLLm).lintegral_prod_right'
  obtain ⟨Fx, hFx⟩ : ∃ Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Fx = fun x => ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ :=
    ⟨_, rfl⟩
  have hFxm : Measurable Fx := by
    rw [hFx]; exact (((gN_cont.comp mt_cont).measurable).pow_const _).enorm
  have hKg' : ∫⁻ x, Fx x ∂D.μG < ⊤ := by rw [hFx]; exact hKg
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal |C1| * ENNReal.ofReal |C1| * (ENNReal.ofReal |C0| * Ls) :=
    ⟨_, rfl⟩
  have hc : c ≠ ⊤ := by
    rw [hcdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLs.ne)
  have hgpos : ∀ x : Mx k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → 0 < B.gN x :=
    fun x hx => lt_of_lt_of_le one_pos ((hNI k r).2 x hx).2
  have hpt : ∀ᵐ x ∂D.μG, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ≤ ∫⁻ y, c * (Fx x * Fx y) ∂D.μG := by
    filter_upwards [hGc] with x hx
    rw [← lintegral_const_mul' (Aext e1 x) _ (by unfold Aext; exact enorm_ne_top)]
    apply lintegral_mono_ae
    filter_upwards [hGc] with y hy
    have hL := lambda_integral_bound hNI hb0e hee0' heea hpUH hx hy
    rw [← hLL, ← hLsdef] at hL
    have hx0 := hgpos _ hx
    have hy0 := hgpos _ hy
    have w1 := e_weight (b := ee) hb1 hx hx0
    have w2 := e_weight (b := ee) hb1 hy hy0
    have split : ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) =
        ENNReal.ofReal |C0| * (ENNReal.ofReal (B.gN (Matrix.of x) ^ ee) * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee)) := by
      rw [Real.mul_rpow hx0.le hy0.le, ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]
    have hFxx : Fx x = ‖B.gN (Matrix.of x) ^ (-(aOf r h - ee))‖ₑ := by rw [hFx]
    have hFxy : Fx y = ‖B.gN (Matrix.of y) ^ (-(aOf r h - ee))‖ₑ := by rw [hFx]
    calc Aext e1 x * (Aext e1 y * LL x y)
        ≤ Aext e1 x * (Aext e1 y * (ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ ee) * Ls)) := by
          gcongr
      _ = (Aext e1 x * ENNReal.ofReal (B.gN (Matrix.of x) ^ ee)) *
            (Aext e1 y * ENNReal.ofReal (B.gN (Matrix.of y) ^ ee)) * (ENNReal.ofReal |C0| * Ls) := by
          rw [split]; ring
      _ ≤ (ENNReal.ofReal |C1| * Fx x) * (ENNReal.ofReal |C1| * Fx y) * (ENNReal.ofReal |C0| * Ls) := by
          rw [hFxx, hFxy]
          exact mul_le_mul' (mul_le_mul' w1 w2) le_rfl
      _ = c * (Fx x * Fx y) := by rw [hcdef]; ring
  calc _ ≤ ∫⁻ zz, ∫⁻ zz', (K1 * K1) * (Iint (Aext e1) (D.μW.prod D.μN) zz *
          (Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz')) ∂νq ∂νq :=
        lintegral_mono_ae (step1.mono fun zz h => lintegral_mono_ae h)
    _ = (K1 * K1) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz *
          ∫⁻ zz', Iint (Aext e1) (D.μW.prod D.μN) zz' * LL zz zz' ∂νq ∂νq :=
        pull2 _ _ _ hK (fun zz => hI1m.mul (hLz zz))
    _ = (K1 * K1) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz * ∫⁻ y, Aext e1 y * LL zz y ∂D.μG ∂νq := by
        congr 1; apply lintegral_congr; intro zz; congr 1
        exact unfold_Iint hq hA1m (hLz zz) (hinvR zz)
    _ = (K1 * K1) * ∫⁻ x, Aext e1 x * ∫⁻ y, Aext e1 y * LL x y ∂D.μG ∂D.μG := by
        congr 1
        exact unfold_Iint hq hA1m hΦm hinvL
    _ ≤ (K1 * K1) * ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂D.μG ∂D.μG := by
        gcongr 1
        exact lintegral_mono_ae hpt
    _ = (K1 * K1) * (c * ((∫⁻ x, Fx x ∂D.μG) * ∫⁻ y, Fx y ∂D.μG)) := by rw [final2 Fx hFxm hc]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK)
          (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (ENNReal.mul_lt_top hKg' hKg'))

end Formalism.FourierDecayAlt.P.S3dx4
