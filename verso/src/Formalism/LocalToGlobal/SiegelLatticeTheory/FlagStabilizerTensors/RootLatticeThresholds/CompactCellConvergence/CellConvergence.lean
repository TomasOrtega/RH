import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.GrowthSide

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

def gProxy (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (x : PairSp k r) : ℝ :=
  Formalism.FourierDecayAlt.B.gN (Hpk k r * (Matrix.of x.1.1)ᴴ * Hpk k r * (Hpk k r * (Matrix.of x.1.2)ᴴ * Hpk k r) * γ *
    Matrix.of x.2.2 * Matrix.of x.2.1) ^ (-b)

/- English proof (translation)
Unfold `gProxy`. Apply `Measurable.pow_const` to reduce the goal to its premises. Apply `Continuous.measurable` to reduce the goal to its premises. Unfold `Formalism.FourierDecayAlt.B.gN`. Use `fun_prop`.
-/
theorem gProxy_meas (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) :
    Measurable (gProxy (k := k) (r := r) γ b) := by
  unfold gProxy
  apply Measurable.pow_const
  apply Continuous.measurable
  unfold Formalism.FourierDecayAlt.B.gN
  fun_prop

/- English proof (translation)
Take `⟨h12, h22, h11, h21⟩` from `hx`. Establish `e11` using `uh_inv_eq (Formalism.L2.SG.Pf.WFL.Sset_sub_UH (uw_in_sset _ h11))`. Establish `e12` using `uh_inv_eq (Formalism.L2.SG.Pf.WFL.Sset_sub_UH (n_in_sset L.z h12))`. Simplify using `only [gProxy, Formalism.MainNotions.S.Pv.AmpDD.pairMaj, e11, e12]`.
-/
theorem gProxy_eq (L : LocBessel k r) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ)
    {x : PairSp k r} (hx : Good L x) : gProxy γ b x = Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b x := by
  obtain ⟨h12, h22, h11, h21⟩ := hx
  have e11 := uh_inv_eq (Formalism.L2.SG.Pf.WFL.Sset_sub_UH (uw_in_sset _ h11))
  have e12 := uh_inv_eq (Formalism.L2.SG.Pf.WFL.Sset_sub_UH (n_in_sset L.z h12))
  simp only [gProxy, Formalism.MainNotions.S.Pv.AmpDD.pairMaj, e11, e12]

/- English proof (translation)
Unfold `gProxy`. Apply `Real.rpow_nonneg` to reduce the goal to its premises. Unfold `Formalism.FourierDecayAlt.B.gN`. Conclude with `Real.sqrt_nonneg _`.
-/
private theorem gProxy_nonneg (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (x : PairSp k r) :
    0 ≤ gProxy γ b x := by
  unfold gProxy
  apply Real.rpow_nonneg
  unfold Formalism.FourierDecayAlt.B.gN
  exact Real.sqrt_nonneg _

/- English proof (translation)
Introduce `k r L h μG γ μR νR ν hκ hgap hcell hdata hmono`. Take `⟨hUH, hGf, -, -, hHaar, hOrb, -⟩` from `hdata`. Establish `hk : 1 ≤ k` using `hgap.1`. Establish `hStd : FourierDecayAlt.C2.Std k r L.z L.z'` using `⟨hk, L.hz, L.hz'⟩`. Establish `hPos : FourierDecayAlt.C2.PosPt k r L.z L.z' γ` using `⟨hUH, hGf⟩`.

Establish `hAG : 0 ≤ FourierDecayAlt.ThreeDimData.AG k r` using `by unfold FourierDecayAlt.ThreeDimData.AG; positivity`. Establish `hAS : 0 ≤ FourierDecayAlt.ThreeDimData.AS k r`. Unfold `FourierDecayAlt.ThreeDimData.AS FourierDecayAlt.ThreeDimData.dN`. Establish `e : (r:ℝ) * ((r:ℝ) - 1) + 2 * r * (k + 1) + r ^ 2 = 2 * r ^ 2 + r + 2 * r * k` using `by ring`. Rewrite using `[e]`.

Check the signs of the components of the expression. Establish `hR : (0:ℝ) < 10 * ((r:ℝ) + 1) ^ 2` using `by positivity`. Use `set b : ℝ := 10 * ((r:ℝ) + 1) ^ 2 * FourierDecayAlt.ThreeDimData.AG k r + 1 with hb`. Establish `hb0 : 0 ≤ b` using `by positivity`. Use `set β : ℝ := b / (2 * ((5 * (r + 1) ^ 2 : ℕ) : ℝ)) with hβdef`.

Establish `hβ : FourierDecayAlt.ThreeDimData.AG k r < β`. Establish `e : (2 * ((5 * (r + 1) ^ 2 : ℕ) : ℝ)) = 10 * ((r:ℝ) + 1) ^ 2` using `by push_cast; ring`. Rewrite using `[hβdef, e, lt_div_iff₀ hR, hb]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨b, hb0, ?_, ?_⟩` and prove the remaining obligations.

Unfold `Formalism.MainNotions.S.Pv.AmpDD.GapCell at hcell`. Establish `h1 : 0 ≤ ((r:ℝ) + 1) ^ 2 * FourierDecayAlt.ThreeDimData.AS k r` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hgN : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, 0 ≤ FourierDecayAlt.B.gN M`. Introduce `M`.

Unfold `FourierDecayAlt.B.gN`. Conclude with `Real.sqrt_nonneg _`. Establish `hHaarC` using `Formalism.MainNotions.S.Pv.AmpDDPf.haarR_bi k r hk L γ μR hUH hmono hHaar`. Take `⟨hσ, hne, hconc, -⟩` from `hHaar`. Take `⟨T, hT⟩` from `at_pos (γ := γ) hne hconc`.

Use `set T' : ℝ := (T:ℝ) + 1 with hT'`. Establish `hT1 : 1 ≤ T'`. Use `(Nat.cast_nonneg T : (0:ℝ) ≤ T)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : AT γ (T:ℝ) ⊆ AT γ T'`.

Introduce `y hy`. Conclude with `⟨hy.1, by linarith [hy.2]⟩`. Establish `hAT : μR (AT γ T') ≠ 0` using `fun h0 => hT (measure_mono_null hsub h0)`. Take `⟨K, hK, hKb⟩` from `pair_bound L hStd hPos hmono T' hT1 b hb0`. Take `⟨ρh, hρh⟩` from `et_equiv L hStd hPos hmono T'`.

Use `set F : PairSp k r → ℝ≥0∞ := fun x => ENNReal.ofReal (gProxy γ b x) with hFdef`. Establish `hFm : Measurable F` using `ENNReal.measurable_ofReal.comp (gProxy_meas γ b)`. Establish `hFinv : ∀ x, Good L x → ∀ a ∈ RStab k r γ, F (stabAct γ a x) = F x`. Introduce `x hx a ha`. Simplify using `only [hFdef]`.

Rewrite using `[gProxy_eq L γ b ((good_stabAct L ha x).2 hx), gProxy_eq L γ b hx, pairMaj_inv L hUH b hx ha]`. Establish `hETm : MeasurableSet (ET L.z L.z' γ T')` using `(et_closed L.z L.z' hStd.2.1 hUH T').measurableSet`. Establish `hid` using `orbit_identity L hHaarC hconc hne hOrb F hFm hFinv _ hETm _ (at_mset hUH T') ρh hρh`. Use `set f1 : Mt k r × Mt k r → ℝ≥0∞ := fun p => ENNReal.ofReal (FourierDecayAlt.B.gN (of p.2 * of p.1) ^ (-β)) with hf1`. Establish `hf1m : Measurable f1`.

Apply `Measurable.ennreal_ofReal` to reduce the goal to its premises. Apply `Measurable.pow_const` to reduce the goal to its premises. Apply `Continuous.measurable` to reduce the goal to its premises. Unfold `FourierDecayAlt.B.gN`. Use `fun_prop`.

Establish `hGood : ∀ᵐ x ∂pairMeas L, Good L x` using `ae_iff.2 (pairMeas_bad L)`. Establish `hle : ∀ᵐ x ∂pairMeas L, F x * (ET L.z L.z' γ T').indicator 1 x.1.2 ≤ ENNReal.ofReal K * (f1 x.1 * f1 x.2)` using `by filter_upwards [hGood] with x hx`. Distinguish the cases in `hm : x.1.2 ∈ ET L.z L.z' γ T'`. Rewrite using `[Set.indicator_of_mem hm, Pi.one_apply, mul_one]`. Simplify using `only [hFdef, hf1]`.

Rewrite using `[gProxy_eq L γ b hx, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hgN _) _), ← ENNReal.ofReal_mul hK.le]`. Conclude with `ENNReal.ofReal_le_ofReal (hKb x hx hm)`. Simplify using `[hm]`. Use `haveI := sfin_muN L`. Use `haveI : SigmaFinite L.μW := L.hμW.1.1`.

Use `haveI : SigmaFinite L.μW' := L.hμW'.1.1`. Establish `hfin : ∀ {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)}, inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∫⁻ p, f1 p ∂(μW.prod L.μN) < ∞`. Introduce `z μW h1 h2 h3 h4`. Distinguish the cases in `hκ0 : L.κN = 0`. Simplify using `[LocBessel.μN, haarLie, hκ0]`.

Conclude with `growth_side h1 h2 h3 h4 hκ0 hκ hβ`. Establish `hLHS : ∫⁻ x, F x * (ET L.z L.z' γ T').indicator 1 x.1.2 ∂pairMeas L < ∞`. Use `(lintegral_mono_ae hle).trans_lt ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Unfold `pairMeas`.

Rewrite using `[lintegral_prod_mul hf1m.aemeasurable hf1m.aemeasurable]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (hfin L.hz.1 L.hz.2 L.hμW.1 L.hμW.2) (hfin L.hz'.1 L.hz'.2 L.hμW'.1 L.hμW'.2))`. Establish `hFν : ∫⁻ x, F x ∂ν < ∞`. Rewrite `hLHS` using `[hid]`. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[not_lt, top_le_iff]`. Rewrite `hLHS` using `[hc, ENNReal.mul_top hAT]`. Conclude with `lt_irrefl _ hLHS`. Establish `hae : gProxy γ b =ᵐ[ν] Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b` using `by filter_upwards [ae_iff.2 (nu_bad L hne hconc hOrb)] with x hx`. Conclude with `gProxy_eq L γ b hx`.

Establish `hint : Integrable (gProxy γ b) ν`. Use `⟨(gProxy_meas γ b).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (ae_of_all _ (gProxy_nonneg γ b))]`. Conclude with `hFν`. Conclude with `hint.congr hae`.
-/
theorem cell_convergence : Formalism.MainNotions.S.Pv.AmpDD.CellConv := by
  intro k r L h μG γ μR νR ν hκ hgap hcell hdata hmono
  obtain ⟨hUH, hGf, -, -, hHaar, hOrb, -⟩ := hdata
  have hk : 1 ≤ k := hgap.1
  have hStd : FourierDecayAlt.C2.Std k r L.z L.z' := ⟨hk, L.hz, L.hz'⟩
  have hPos : FourierDecayAlt.C2.PosPt k r L.z L.z' γ := ⟨hUH, hGf⟩
  have hAG : 0 ≤ FourierDecayAlt.ThreeDimData.AG k r := by unfold FourierDecayAlt.ThreeDimData.AG; positivity
  have hAS : 0 ≤ FourierDecayAlt.ThreeDimData.AS k r := by
    unfold FourierDecayAlt.ThreeDimData.AS FourierDecayAlt.ThreeDimData.dN
    have e : (r:ℝ) * ((r:ℝ) - 1) + 2 * r * (k + 1) + r ^ 2 = 2 * r ^ 2 + r + 2 * r * k := by ring
    rw [e]
    positivity
  have hR : (0:ℝ) < 10 * ((r:ℝ) + 1) ^ 2 := by positivity
  set b : ℝ := 10 * ((r:ℝ) + 1) ^ 2 * FourierDecayAlt.ThreeDimData.AG k r + 1 with hb
  have hb0 : 0 ≤ b := by positivity
  set β : ℝ := b / (2 * ((5 * (r + 1) ^ 2 : ℕ) : ℝ)) with hβdef
  have hβ : FourierDecayAlt.ThreeDimData.AG k r < β := by
    have e : (2 * ((5 * (r + 1) ^ 2 : ℕ) : ℝ)) = 10 * ((r:ℝ) + 1) ^ 2 := by push_cast; ring
    rw [hβdef, e, lt_div_iff₀ hR, hb]
    linarith
  refine ⟨b, hb0, ?_, ?_⟩
  · unfold Formalism.MainNotions.S.Pv.AmpDD.GapCell at hcell
    have h1 : 0 ≤ ((r:ℝ) + 1) ^ 2 * FourierDecayAlt.ThreeDimData.AS k r := by positivity
    nlinarith
  have hgN : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, 0 ≤ FourierDecayAlt.B.gN M := by
    intro M
    unfold FourierDecayAlt.B.gN
    exact Real.sqrt_nonneg _
  have hHaarC := Formalism.MainNotions.S.Pv.AmpDDPf.haarR_bi k r hk L γ μR hUH hmono hHaar
  obtain ⟨hσ, hne, hconc, -⟩ := hHaar
  obtain ⟨T, hT⟩ := at_pos (γ := γ) hne hconc
  set T' : ℝ := (T:ℝ) + 1 with hT'
  have hT1 : 1 ≤ T' := by
    have := (Nat.cast_nonneg T : (0:ℝ) ≤ T)
    linarith
  have hsub : AT γ (T:ℝ) ⊆ AT γ T' := by
    intro y hy
    exact ⟨hy.1, by linarith [hy.2]⟩
  have hAT : μR (AT γ T') ≠ 0 := fun h0 => hT (measure_mono_null hsub h0)
  obtain ⟨K, hK, hKb⟩ := pair_bound L hStd hPos hmono T' hT1 b hb0
  obtain ⟨ρh, hρh⟩ := et_equiv L hStd hPos hmono T'
  set F : PairSp k r → ℝ≥0∞ := fun x => ENNReal.ofReal (gProxy γ b x) with hFdef
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp (gProxy_meas γ b)
  have hFinv : ∀ x, Good L x → ∀ a ∈ RStab k r γ, F (stabAct γ a x) = F x := by
    intro x hx a ha
    simp only [hFdef]
    rw [gProxy_eq L γ b ((good_stabAct L ha x).2 hx), gProxy_eq L γ b hx, pairMaj_inv L hUH b hx ha]
  have hETm : MeasurableSet (ET L.z L.z' γ T') := (et_closed L.z L.z' hStd.2.1 hUH T').measurableSet
  have hid := orbit_identity L hHaarC hconc hne hOrb F hFm hFinv _ hETm _ (at_mset hUH T') ρh hρh
  set f1 : Mt k r × Mt k r → ℝ≥0∞ := fun p => ENNReal.ofReal (FourierDecayAlt.B.gN (of p.2 * of p.1) ^ (-β)) with hf1
  have hf1m : Measurable f1 := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply Continuous.measurable
    unfold FourierDecayAlt.B.gN
    fun_prop
  have hGood : ∀ᵐ x ∂pairMeas L, Good L x := ae_iff.2 (pairMeas_bad L)
  have hle : ∀ᵐ x ∂pairMeas L, F x * (ET L.z L.z' γ T').indicator 1 x.1.2 ≤ ENNReal.ofReal K * (f1 x.1 * f1 x.2) := by
    filter_upwards [hGood] with x hx
    by_cases hm : x.1.2 ∈ ET L.z L.z' γ T'
    · rw [Set.indicator_of_mem hm, Pi.one_apply, mul_one]
      simp only [hFdef, hf1]
      rw [gProxy_eq L γ b hx, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hgN _) _), ← ENNReal.ofReal_mul hK.le]
      exact ENNReal.ofReal_le_ofReal (hKb x hx hm)
    · simp [hm]
  haveI := sfin_muN L
  haveI : SigmaFinite L.μW := L.hμW.1.1
  haveI : SigmaFinite L.μW' := L.hμW'.1.1
  have hfin : ∀ {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)}, inWb k r z → 0 < Tz k r z →
      IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∫⁻ p, f1 p ∂(μW.prod L.μN) < ∞ := by
    intro z μW h1 h2 h3 h4
    by_cases hκ0 : L.κN = 0
    · simp [LocBessel.μN, haarLie, hκ0]
    · exact growth_side h1 h2 h3 h4 hκ0 hκ hβ
  have hLHS : ∫⁻ x, F x * (ET L.z L.z' γ T').indicator 1 x.1.2 ∂pairMeas L < ∞ := by
    refine (lintegral_mono_ae hle).trans_lt ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    unfold pairMeas
    rw [lintegral_prod_mul hf1m.aemeasurable hf1m.aemeasurable]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (hfin L.hz.1 L.hz.2 L.hμW.1 L.hμW.2) (hfin L.hz'.1 L.hz'.2 L.hμW'.1 L.hμW'.2))
  have hFν : ∫⁻ x, F x ∂ν < ∞ := by
    rw [hid] at hLHS
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.mul_top hAT] at hLHS
    exact lt_irrefl _ hLHS
  have hae : gProxy γ b =ᵐ[ν] Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b := by
    filter_upwards [ae_iff.2 (nu_bad L hne hconc hOrb)] with x hx
    exact gProxy_eq L γ b hx
  have hint : Integrable (gProxy γ b) ν := by
    refine ⟨(gProxy_meas γ b).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gProxy_nonneg γ b))]
    exact hFν
  exact hint.congr hae

end Formalism.MainNotions.S.Pv.AmpDDPf.CC

/- English proof (translation)
The claim follows from `Formalism.MainNotions.S.Pv.AmpDDPf.CC.cell_convergence`.
-/
theorem Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence : Formalism.MainNotions.S.Pv.AmpDD.CellConv :=
  Formalism.MainNotions.S.Pv.AmpDDPf.CC.cell_convergence
