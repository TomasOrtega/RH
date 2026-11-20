import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalHalfSumNonneg

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

def UWComp : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsCompact (UWset k r z)

/- English proof (translation)
Unfold `psiGen`. Rewrite using `[mul_comm]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem psiGen_norm (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖psiGen k r z c g‖ = 1 := by
  unfold psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

section Bound

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Vp →L[ℂ] Vp)}

/- English proof (translation)
Use `set h := Matrix.of p.1 with hdef`. Use `set m := Matrix.of p.2 with mdef`. Use `set N := N1H k r`. Establish `hN : 0 ≤ N` using `nilradical_half_sum_nonneg`. Establish `hmg : m * g ∈ Gr k r` using `gr_mul hm hg`.

Establish `hy : h * (m * g) ∈ Gr k r` using `gr_mul hh hmg`. Establish `hhm : h * m ∈ Gr k r` using `gr_mul hh hm`. Establish `hσeq : σ (h * m) (σ g w) = σ (h * (m * g)) w`. Rewrite using `[← mul_assoc, sigma_mul hσ hhm hg]`. Establish `hpsi : ‖star (psiGen k r z c m)‖ = 1`.

Rewrite using `[norm_star]`. Conclude with `psiGen_norm z c m`. Establish `hnorm : ‖bInt z c σ π w' ξ (σ g w) p‖ = ‖⟪w', σ (h * (m * g)) w⟫_ℂ‖ * ‖ξ‖`. Simplify using `only [bInt]`. Rewrite using `[norm_smul, norm_mul, hpsi, ← hdef, ← mdef, hσeq, hπ, mul_one]`.

Rewrite using `[hnorm]`. Use `set y := h * (m * g)`. Establish `hypos : 0 < opn y` using `opn_pos hy`. Establish `hmpos : 0 < opn m` using `opn_pos hm`. Establish `hCφ0 : 0 ≤ Cφ` using `le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _)) (hCφ 1 gr_one)`.

Establish `hA : ‖⟪w', σ y w⟫_ℂ‖ ≤ Cφ * opn y ^ (-N)`. Establish `h1` using `hCφ y hy`. Establish `hpow : 0 < opn y ^ N` using `Real.rpow_pos_of_pos hypos _`. Rewrite using `[Real.rpow_neg (le_of_lt hypos), ← div_eq_mul_inv, le_div_iff₀ hpow]`. Conclude with `h1`.

Establish `hinvh : h⁻¹ * y = m * g`. Simplify using `only [y]`. Rewrite using `[← mul_assoc, Matrix.nonsing_inv_mul h (gr_isUnit hh), one_mul]`. Establish `hmle : opn m ≤ Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g) * opn y`. Establish `e1 : opn m ≤ opn (m * g) * opn g⁻¹` using `opn_le_mul_inv m hg`.

Establish `e2 : opn (m * g) ≤ opn h⁻¹ * opn y`. Rewrite using `[← hinvh]`. Conclude with `opn_mul _ _`. Establish `e3 : opn g⁻¹ ≤ opn (Hpk k r) * opn (Hpk k r) * opn g` using `opn_inv_le hg`. Establish `e4 : opn h⁻¹ * opn y ≤ Kw * opn y` using `mul_le_mul_of_nonneg_right hhinv (le_of_lt hypos)`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (e2.trans e4) e3 (opn_nonneg _)` to reduce the goal to its premises. Conclude with `mul_nonneg hKw0 (le_of_lt hypos)`. Use `_ = Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g) * opn y := by ring`. Establish `hB0 : 0 ≤ Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)` using `mul_nonneg hKw0 (mul_nonneg (mul_nonneg (opn_nonneg _) (opn_nonneg _)) (opn_nonneg _))`.

Establish `hyN : opn y ^ (-N) ≤ (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * opn m ^ (-N)`. Establish `hp : opn m ^ N ≤ (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * opn y ^ N`. Rewrite using `[← Real.mul_rpow hB0 (le_of_lt hypos)]`. Conclude with `Real.rpow_le_rpow (le_of_lt hmpos) hmle hN`. Establish `hmN : 0 < opn m ^ N` using `Real.rpow_pos_of_pos hmpos _`.

Establish `hyN' : 0 < opn y ^ N` using `Real.rpow_pos_of_pos hypos _`. Rewrite using `[Real.rpow_neg (le_of_lt hypos), Real.rpow_neg (le_of_lt hmpos), ← div_eq_mul_inv, inv_le_iff_one_le_mul₀' hyN', mul_div_assoc', le_div_iff₀ hmN, one_mul]`. Combine the linear relations using `[hp]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (norm_nonneg _)` to reduce the goal to its premises.

Conclude with `mul_le_mul_of_nonneg_left hyN hCφ0`. Use `_ = Cφ * (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * ‖ξ‖ * opn m ^ (-N) := by ring`.
-/
theorem bInt_bound (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hσ : IsURepOn (Gr k r) σ)
    {w w' : H} {Cφ : ℝ} (hCφ : ∀ y ∈ Gr k r, ‖⟪w', σ y w⟫_ℂ‖ * opn y ^ N1H k r ≤ Cφ)
    {Kw : ℝ} (hKw0 : 0 ≤ Kw) (ξ : Vp) (p : Mt k r × Mt k r)
    (hh : Matrix.of p.1 ∈ Gr k r) (hhinv : opn (Matrix.of p.1)⁻¹ ≤ Kw)
    (hπ : ‖π (Matrix.of p.1)⁻¹ ξ‖ = ‖ξ‖) (hm : Matrix.of p.2 ∈ Gr k r)
    {g : Mat k r} (hg : g ∈ Gr k r) :
    ‖bInt z c σ π w' ξ (σ g w) p‖ ≤
      Cφ * (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N1H k r * ‖ξ‖ *
        opn (Matrix.of p.2) ^ (-N1H k r) := by
  set h := Matrix.of p.1 with hdef
  set m := Matrix.of p.2 with mdef
  set N := N1H k r
  have hN : 0 ≤ N := nilradical_half_sum_nonneg
  have hmg : m * g ∈ Gr k r := gr_mul hm hg
  have hy : h * (m * g) ∈ Gr k r := gr_mul hh hmg
  have hhm : h * m ∈ Gr k r := gr_mul hh hm
  have hσeq : σ (h * m) (σ g w) = σ (h * (m * g)) w := by
    rw [← mul_assoc, sigma_mul hσ hhm hg]
  have hpsi : ‖star (psiGen k r z c m)‖ = 1 := by
    rw [norm_star]
    exact psiGen_norm z c m
  have hnorm : ‖bInt z c σ π w' ξ (σ g w) p‖ = ‖⟪w', σ (h * (m * g)) w⟫_ℂ‖ * ‖ξ‖ := by
    simp only [bInt]
    rw [norm_smul, norm_mul, hpsi, ← hdef, ← mdef, hσeq, hπ, mul_one]
  rw [hnorm]
  set y := h * (m * g)
  have hypos : 0 < opn y := opn_pos hy
  have hmpos : 0 < opn m := opn_pos hm
  have hCφ0 : 0 ≤ Cφ := le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _))
    (hCφ 1 gr_one)
  have hA : ‖⟪w', σ y w⟫_ℂ‖ ≤ Cφ * opn y ^ (-N) := by
    have h1 := hCφ y hy
    have hpow : 0 < opn y ^ N := Real.rpow_pos_of_pos hypos _
    rw [Real.rpow_neg (le_of_lt hypos), ← div_eq_mul_inv, le_div_iff₀ hpow]
    exact h1
  have hinvh : h⁻¹ * y = m * g := by
    simp only [y]
    rw [← mul_assoc, Matrix.nonsing_inv_mul h (gr_isUnit hh), one_mul]
  have hmle : opn m ≤ Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g) * opn y := by
    have e1 : opn m ≤ opn (m * g) * opn g⁻¹ := opn_le_mul_inv m hg
    have e2 : opn (m * g) ≤ opn h⁻¹ * opn y := by
      rw [← hinvh]
      exact opn_mul _ _
    have e3 : opn g⁻¹ ≤ opn (Hpk k r) * opn (Hpk k r) * opn g := opn_inv_le hg
    have e4 : opn h⁻¹ * opn y ≤ Kw * opn y := mul_le_mul_of_nonneg_right hhinv (le_of_lt hypos)
    calc opn m ≤ opn (m * g) * opn g⁻¹ := e1
      _ ≤ (Kw * opn y) * (opn (Hpk k r) * opn (Hpk k r) * opn g) := by
        apply mul_le_mul (e2.trans e4) e3 (opn_nonneg _)
        exact mul_nonneg hKw0 (le_of_lt hypos)
      _ = Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g) * opn y := by ring
  have hB0 : 0 ≤ Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g) :=
    mul_nonneg hKw0 (mul_nonneg (mul_nonneg (opn_nonneg _) (opn_nonneg _)) (opn_nonneg _))
  have hyN : opn y ^ (-N) ≤ (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * opn m ^ (-N) := by
    have hp : opn m ^ N ≤ (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * opn y ^ N := by
      rw [← Real.mul_rpow hB0 (le_of_lt hypos)]
      exact Real.rpow_le_rpow (le_of_lt hmpos) hmle hN
    have hmN : 0 < opn m ^ N := Real.rpow_pos_of_pos hmpos _
    have hyN' : 0 < opn y ^ N := Real.rpow_pos_of_pos hypos _
    rw [Real.rpow_neg (le_of_lt hypos), Real.rpow_neg (le_of_lt hmpos), ← div_eq_mul_inv,
      inv_le_iff_one_le_mul₀' hyN', mul_div_assoc', le_div_iff₀ hmN, one_mul]
    linarith [hp]
  calc ‖⟪w', σ y w⟫_ℂ‖ * ‖ξ‖ ≤ (Cφ * opn y ^ (-N)) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ ≤ (Cφ * ((Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * opn m ^ (-N))) * ‖ξ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hyN hCφ0
    _ = Cφ * (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * ‖ξ‖ * opn m ^ (-N) := by ring

end Bound

/- English proof (translation)
Establish `hc : Continuous fun m : Mt k r => opn (of m)` using `(opn_continuous (k := k) (r := r)).comp continuous_id`. Conclude with `ENNReal.measurable_ofReal.comp ((hc.measurable.pow_const _).comp measurable_snd)`.
-/
private theorem measurable_ofReal_opn_rpow_snd : Measurable fun p : Mt k r × Mt k r => ENNReal.ofReal (opn (of p.2) ^ (-(N1H k r))) := by
  have hc : Continuous fun m : Mt k r => opn (of m) := (opn_continuous (k := k) (r := r)).comp continuous_id
  exact ENNReal.measurable_ofReal.comp ((hc.measurable.pow_const _).comp measurable_snd)

/- English proof (translation)
Introduce `k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hRD hCW x₀ hx₀ ξ`. Take `⟨hset, hDS, hHCW, hLow, hGh, hSh, hQ, hWh, hNh, hWfin, hNfin⟩` from `hyp`. Establish `hinWb : inWb k r z` using `hset.2.2.1`. Establish `hTz : 0 < Tz k r z` using `hset.2.2.2.1`. Establish `hσ : IsURepOn (Gr k r) σ` using `hSG k r _ _ H σ hDS`.

Take `⟨hUWG, hNG, hUWgrp, _, _⟩` from `hS k r z c hinWb hTz`. Establish `hπu` using `(hPi k r z u Vp π hinWb hTz hHCW).2`. Take `⟨Cφ, _, hCφ⟩` from `ptDecay_of hSG hD hRG k r z c u v b H σ Vp π w μG μS ν μW μN ⟨hset, hDS, hHCW, hLow, hGh, hSh, hQ, hWh, hNh, hWfin, hNfin⟩ hRD hCW x₀ hx₀`. Take `⟨K0, hK0⟩` from `(hU k r z hinWb hTz).exists_bound_of_continuousOn (opn_continuous (k := k) (r := r)).continuousOn`. Use `set Kw := max K0 0`.

Establish `hKw0 : 0 ≤ Kw` using `le_max_right _ _`. Establish `hKw : ∀ h ∈ UWset k r z, opn h⁻¹ ≤ Kw`. Introduce `h hh`. Establish `hinv : h⁻¹ ∈ UWset k r z` using `((hUWgrp h hh h hh).2.1)`. Use `hK0 _ hinv` as an intermediate fact.

Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `le_trans (le_abs_self _) (le_trans this (le_max_left _ _))`. Use `set N := N1H k r`. Use `haveI : SigmaFinite μN := hNh.1`. Use `haveI : SigmaFinite μW := hWh.1`.

Use `set I := ∫⁻ m : Mt k r, ENNReal.ofReal (opn (of m) ^ (-N)) ∂μN`. Establish `hI : I < ∞` using `hNI k r μN hNh hNfin`. Use `set A := Cφ * (Kw * (opn (Hpk k r) * opn (Hpk k r))) ^ N * ‖ξ‖`. Establish `hCφ0 : 0 ≤ Cφ` using `le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _)) (hCφ 1 gr_one)`. Establish `hH0 : 0 ≤ opn (Hpk k r) * opn (Hpk k r)` using `mul_nonneg (opn_nonneg _) (opn_nonneg _)`.

Establish `hA0 : 0 ≤ A` using `mul_nonneg (mul_nonneg hCφ0 (Real.rpow_nonneg (mul_nonneg hKw0 hH0) _)) (norm_nonneg _)`. Use `⟨A * I.toReal * (μW Set.univ).toReal, mul_nonneg (mul_nonneg hA0 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Establish `hW_ae : ∀ᵐ x ∂μW, of x ∈ UWset k r z` using `ae_iff.mpr (by simpa using hWh.2.2.1)`. Establish `hN_ae : ∀ᵐ x ∂μN, of x ∈ Nset k r` using `ae_iff.mpr (by simpa using hNh.2.2.1)`.

Establish `hae : ∀ᵐ p ∂(μW.prod μN), of p.1 ∈ UWset k r z ∧ of p.2 ∈ Nset k r` using `(Measure.quasiMeasurePreserving_fst.ae hW_ae).and (Measure.quasiMeasurePreserving_snd.ae hN_ae)`. Establish `hg0 : 0 ≤ opn g` using `opn_nonneg g`. Establish `hpt : ∀ p : Mt k r × Mt k r, of p.1 ∈ UWset k r z → of p.2 ∈ Nset k r → ‖bInt z c σ π (σ x₀ w) ξ (σ g w) p‖ ≤ (A * opn g ^ N) * opn (of p.2) ^ (-N)`. Introduce `p h1 h2`. Establish `hinv1 : (of p.1)⁻¹ ∈ UWset k r z` using `(hUWgrp _ h1 _ h1).2.1`.

Establish `hb` using `bInt_bound z c hσ (w := w) (w' := σ x₀ w) (fun y hy => hCφ y hy) hKw0 ξ p (hUWG h1) (hKw _ h1) (hπu _ hinv1 ξ) (hNG h2) hg`. Establish `heq : (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N = (Kw * (opn (Hpk k r) * opn (Hpk k r))) ^ N * opn g ^ N`. Rewrite using `[← Real.mul_rpow (mul_nonneg hKw0 hH0) hg0]`. Put the polynomial expressions in normal form. Rewrite `hb` using `[heq]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hmeas : Measurable fun p : Mt k r × Mt k r => ENNReal.ofReal (opn (of p.2) ^ (-N))` using `measurable_ofReal_opn_rpow_snd`. Combine the equalities or inequalities in the displayed calculation. Apply `lintegral_mono_ae` to reduce the goal to its premises. Use `filter_upwards [hae] with p hp`.

Rewrite using `[← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (mul_nonneg hA0 (Real.rpow_nonneg hg0 _))]`. Conclude with `ENNReal.ofReal_le_ofReal (hpt p hp.1 hp.2)`. Use `_ = ENNReal.ofReal (A * opn g ^ N) * (μW Set.univ * I) := by`. Rewrite using `[lintegral_const_mul _ hmeas, lintegral_prod _ hmeas.aemeasurable]`. Simplify using `only [lintegral_const]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ENNReal.ofReal (A * I.toReal * (μW Set.univ).toReal * opn g ^ N) := by`. Rewrite using `[ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hA0 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg), ENNReal.ofReal_mul (mul_nonneg hA0 ENNReal.toReal_nonneg), ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul hA0, ENNReal.ofReal_toReal hI.ne, ENNReal.ofReal_toReal (measure_ne_top μW Set.univ …`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := le_rfl`.
-/
theorem aBound_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) : ABound := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hRD hCW x₀ hx₀ ξ
  obtain ⟨hset, hDS, hHCW, hLow, hGh, hSh, hQ, hWh, hNh, hWfin, hNfin⟩ := hyp
  have hinWb : inWb k r z := hset.2.2.1
  have hTz : 0 < Tz k r z := hset.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUWgrp, _, _⟩ := hS k r z c hinWb hTz
  have hπu := (hPi k r z u Vp π hinWb hTz hHCW).2
  obtain ⟨Cφ, _, hCφ⟩ := ptDecay_of hSG hD hRG k r z c u v b H σ Vp π w μG μS ν μW μN
    ⟨hset, hDS, hHCW, hLow, hGh, hSh, hQ, hWh, hNh, hWfin, hNfin⟩ hRD hCW x₀ hx₀
  obtain ⟨K0, hK0⟩ := (hU k r z hinWb hTz).exists_bound_of_continuousOn
    (opn_continuous (k := k) (r := r)).continuousOn
  set Kw := max K0 0
  have hKw0 : 0 ≤ Kw := le_max_right _ _
  have hKw : ∀ h ∈ UWset k r z, opn h⁻¹ ≤ Kw := by
    intro h hh
    have hinv : h⁻¹ ∈ UWset k r z := ((hUWgrp h hh h hh).2.1)
    have := hK0 _ hinv
    rw [Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) (le_trans this (le_max_left _ _))
  set N := N1H k r
  haveI : SigmaFinite μN := hNh.1
  haveI : SigmaFinite μW := hWh.1
  set I := ∫⁻ m : Mt k r, ENNReal.ofReal (opn (of m) ^ (-N)) ∂μN
  have hI : I < ∞ := hNI k r μN hNh hNfin
  set A := Cφ * (Kw * (opn (Hpk k r) * opn (Hpk k r))) ^ N * ‖ξ‖
  have hCφ0 : 0 ≤ Cφ := le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _))
    (hCφ 1 gr_one)
  have hH0 : 0 ≤ opn (Hpk k r) * opn (Hpk k r) := mul_nonneg (opn_nonneg _) (opn_nonneg _)
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg hCφ0 (Real.rpow_nonneg (mul_nonneg hKw0 hH0) _)) (norm_nonneg _)
  refine ⟨A * I.toReal * (μW Set.univ).toReal,
    mul_nonneg (mul_nonneg hA0 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg, ?_⟩
  intro g hg
  have hW_ae : ∀ᵐ x ∂μW, of x ∈ UWset k r z := ae_iff.mpr (by simpa using hWh.2.2.1)
  have hN_ae : ∀ᵐ x ∂μN, of x ∈ Nset k r := ae_iff.mpr (by simpa using hNh.2.2.1)
  have hae : ∀ᵐ p ∂(μW.prod μN), of p.1 ∈ UWset k r z ∧ of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW_ae).and (Measure.quasiMeasurePreserving_snd.ae hN_ae)
  have hg0 : 0 ≤ opn g := opn_nonneg g
  have hpt : ∀ p : Mt k r × Mt k r, of p.1 ∈ UWset k r z → of p.2 ∈ Nset k r →
      ‖bInt z c σ π (σ x₀ w) ξ (σ g w) p‖ ≤ (A * opn g ^ N) * opn (of p.2) ^ (-N) := by
    intro p h1 h2
    have hinv1 : (of p.1)⁻¹ ∈ UWset k r z := (hUWgrp _ h1 _ h1).2.1
    have hb := bInt_bound z c hσ (w := w) (w' := σ x₀ w) (fun y hy => hCφ y hy) hKw0 ξ p (hUWG h1)
      (hKw _ h1) (hπu _ hinv1 ξ) (hNG h2) hg
    have heq : (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N
        = (Kw * (opn (Hpk k r) * opn (Hpk k r))) ^ N * opn g ^ N := by
      rw [← Real.mul_rpow (mul_nonneg hKw0 hH0) hg0]
      ring_nf
    rw [heq] at hb
    calc _ ≤ _ := hb
      _ = (A * opn g ^ N) * opn (of p.2) ^ (-N) := by simp only [A]; ring
  have hmeas : Measurable fun p : Mt k r × Mt k r => ENNReal.ofReal (opn (of p.2) ^ (-N)) :=
    measurable_ofReal_opn_rpow_snd
  calc ∫⁻ p, ‖bInt z c σ π (σ x₀ w) ξ (σ g w) p‖ₑ ∂(μW.prod μN)
      ≤ ∫⁻ p, ENNReal.ofReal (A * opn g ^ N) * ENNReal.ofReal (opn (of p.2) ^ (-N)) ∂(μW.prod μN) := by
        apply lintegral_mono_ae
        filter_upwards [hae] with p hp
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (mul_nonneg hA0 (Real.rpow_nonneg hg0 _))]
        exact ENNReal.ofReal_le_ofReal (hpt p hp.1 hp.2)
    _ = ENNReal.ofReal (A * opn g ^ N) * (μW Set.univ * I) := by
        rw [lintegral_const_mul _ hmeas, lintegral_prod _ hmeas.aemeasurable]
        simp only [lintegral_const]
        ring
    _ = ENNReal.ofReal (A * I.toReal * (μW Set.univ).toReal * opn g ^ N) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hA0 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul (mul_nonneg hA0 ENNReal.toReal_nonneg), ENNReal.ofReal_mul hA0,
          ENNReal.ofReal_mul hA0, ENNReal.ofReal_toReal hI.ne,
          ENNReal.ofReal_toReal (measure_ne_top μW Set.univ)]
        ring
    _ ≤ _ := le_rfl

end WlocSk.PtD
