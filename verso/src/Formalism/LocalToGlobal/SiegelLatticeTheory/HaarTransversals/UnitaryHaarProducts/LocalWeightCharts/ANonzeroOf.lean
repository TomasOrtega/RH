import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Unfold
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped ENNReal InnerProductSpace

namespace WlocSk.ANz

variable {k r : ℕ}

/- English proof (translation)
Take `⟨c, hc0, -, hμeq⟩` from `WlocSk.HM.haar_unique (Gr k r) WlocSk.HM.uh_clsub μG hμ`. Establish `hVm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r}` using `(hU.preimage WlocSk.Grp.continuous_of).measurableSet.inter (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet`. Establish `hvt : Continuous (WlocSk.HM.Grp.vt : WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub → Formalism.QuantumDeterminants.Mt k r)` using `WlocSk.HM.Grp.embt.continuous`. Establish `hO : IsOpen ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U : Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub))` using `hU.preimage (WlocSk.Grp.continuous_of.comp hvt)`. Establish `hne : ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U : Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)).Nonempty` using `⟨WlocSk.HM.Grp.mk x hxG, hxU⟩`.

Establish `hpos` using `hO.measure_pos (Measure.haar : Measure (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) hne`. Rewrite using `[hμeq, Measure.smul_apply, smul_eq_mul, WlocSk.HM.hmeas, Measure.map_apply hvt.measurable hVm]`. Use `ENNReal.mul_pos hc0 (ne_of_gt (lt_of_lt_of_le hpos (measure_mono ?_)))` and prove the remaining obligations. Introduce `a ha`. Conclude with `⟨ha, WlocSk.HM.Grp.mem a⟩`.
-/
theorem haarG_pos {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : IsHaarOn (Gr k r) μG) {U : Set (Mat k r)}
    (hU : IsOpen U) {x : Mat k r} (hxU : x ∈ U) (hxG : x ∈ Gr k r) :
    0 < μG {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r} := by
  obtain ⟨c, hc0, -, hμeq⟩ := WlocSk.HM.haar_unique (Gr k r) WlocSk.HM.uh_clsub μG hμ
  have hVm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r} :=
    (hU.preimage WlocSk.Grp.continuous_of).measurableSet.inter
      (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet
  have hvt : Continuous (WlocSk.HM.Grp.vt :
      WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub → Formalism.QuantumDeterminants.Mt k r) := WlocSk.HM.Grp.embt.continuous
  have hO : IsOpen ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U :
      Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) :=
    hU.preimage (WlocSk.Grp.continuous_of.comp hvt)
  have hne : ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U :
      Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)).Nonempty :=
    ⟨WlocSk.HM.Grp.mk x hxG, hxU⟩
  have hpos := hO.measure_pos (Measure.haar : Measure (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) hne
  rw [hμeq, Measure.smul_apply, smul_eq_mul, WlocSk.HM.hmeas, Measure.map_apply hvt.measurable hVm]
  refine ENNReal.mul_pos hc0 (ne_of_gt (lt_of_lt_of_le hpos (measure_mono ?_)))
  intro a ha
  exact ⟨ha, WlocSk.HM.Grp.mem a⟩

/- English proof (translation)
Introduce `hNV k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW`. Take `⟨hset, hDS, hHC, hLU, hG, -, -, hW, hN, -, -⟩` from `id hyp`. Take `⟨hk1, hev, hz, hT, hc, hu, hl, hI, hH2, hGB⟩` from `hset`. Establish `hk2 : 2 ≤ k` using `by obtain ⟨m, hm⟩ := hev; omega`. Take `⟨x, x₀, hx, hx₀, hne⟩` from `hNV k r z c u v b hk2 hev hz hT hc hu hl hI hH2 hGB H σ hDS Vp π hHC w hLU μW μN hW hN`.

Establish `hFi : Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹) (μW.prod μN)`. Assume the negation of the conclusion as `hni`. Conclude with `hne (integral_undef hni)`. Choose the witnesses or unpack the hypotheses as in `⟨ξ, hξ⟩ : ∃ ξ : Vp, (∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ ∂(μW.prod μN)) ξ ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Use `push Not at hall`. Conclude with `hne (ContinuousLinearMap.ext hall)`. Rewrite `hξ` using `[ContinuousLinearMap.integral_apply hFi]`. Use `set A := Af z c σ π μW μN w x₀ ξ with hAdef`. Establish `hAx : A x ≠ 0` using `hξ`.

Establish `hcont : ContinuousOn A (Gr k r)` using `hAC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ`. Establish `hequiv : IsSPsiEquiv z (psiGen k r z c) π A` using `hAE k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ`. Take `⟨hWG, hNG, -, hNg, -⟩` from `hSG k r z c hz hT`. Establish `hπ` using `(hPU k r z u Vp π hz hT hHC).2`. Establish `hApos : 0 < ‖A x‖` using `norm_pos_iff.mpr hAx`.

Take `⟨ε, hε, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < ‖A x‖` from `⟨‖A x‖ / 2, half_pos hApos, half_lt_self hApos⟩`. Establish `hevn : ∀ᶠ y in nhdsWithin x (Gr k r), ε < ‖A y‖` using `(hcont x hx).norm.eventually (lt_mem_nhds hεlt)`. Take `⟨U, hUo, hxU, hUsub⟩` from `mem_nhdsWithin.mp hevn`. Use `set V : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ U ∩ Gr k r} with hVdef`. Establish `hVm : MeasurableSet V` using `(hUo.preimage WlocSk.Grp.continuous_of).measurableSet.inter (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet`.

Establish `hμV : 0 < μG V` using `haarG_pos hG hUo hxU hx`. Take `⟨cS, hcS0, -, hunf⟩` from `unfold_of hSP hyp`. Establish `hfm : Measurable (V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞))` using `measurable_one.indicator hVm`. Use `hW.1` as an intermediate fact. Use `hN.1` as an intermediate fact.

Use `set g : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) with hgdef`. Establish `hU' : ∫⁻ x, g x ∂ν = cS * μG V`. Establish `h` using `hunf _ hfm`. Rewrite `h` using `[lintegral_indicator_one hVm]`. Conclude with `h`.

Establish `hjoint : Measurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (fun i j => (Matrix.of (mulP q.2) * Matrix.of q.1) i j))`. Use `hfm.comp (Continuous.measurable ?_)` and prove the remaining obligations. Conclude with `(WlocSk.Grp.continuous_of.comp (continuous_mulP.comp continuous_snd)).matrix_mul (WlocSk.Grp.continuous_of.comp continuous_fst)`. Establish `hgm : Measurable g` using `hjoint.lintegral_prod_right'`. Use `set P : Set (Formalism.QuantumDeterminants.Mt k r) := {x | 0 < g x} with hPdef`.

Establish `hPm : MeasurableSet P` using `measurableSet_lt measurable_const hgm`. Establish `hPpos : ν P ≠ 0`. Introduce `h0`. Establish `hae : ∀ᵐ x ∂ν, g x = 0`. Use `ae_iff.mpr (measure_mono_null (fun x hx => ?_) h0)` and prove the remaining obligations.

Conclude with `pos_iff_ne_zero.mpr hx`. Establish `h1 : ∫⁻ x, g x ∂ν = 0` using `by rw [lintegral_congr_ae hae, lintegral_zero]`. Rewrite `hU'` using `[h1]`. Conclude with `(ENNReal.mul_pos hcS0 hμV.ne').ne' hU'.symm`. Establish `hTae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r`.

Establish `h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z` using `Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hW.2.2.1)`. Establish `h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r` using `Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hN.2.2.1)`. Use `filter_upwards [h1, h2] with p hp1 hp2`. Conclude with `⟨hp1, hp2⟩`. Establish `key : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Gr k r → 0 < g x → ε < ‖A (Matrix.of x)‖`.

Introduce `x hxG hgx`. Assume the negation of the conclusion as `hle`. Apply `hgx.ne'` to reduce the goal to its premises. Establish `hae : ∀ᵐ p ∂(μW.prod μN), V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) = 0` using `by filter_upwards [hTae] with p hp`. Apply `Set.indicator_of_notMem` to reduce the goal to its premises.

Introduce `hpV`. Establish `h1 : ε < ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖` using `hUsub hpV`. Establish `h2 : ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ = ‖A (Matrix.of x)‖`. Rewrite using `[hequiv _ hp.1 _ hp.2 _ hxG, norm_smul, (hNg _ hp.2 _ hp.2).2.2.2.2, hπ _ hp.1, one_mul]`. Conclude with `hle (h2 ▸ h1)`.

Use `show ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) = 0`. Rewrite using `[lintegral_congr_ae hae, lintegral_zero]`. Establish `hνG : ∀ᵐ x ∂ν, Matrix.of x ∈ Gr k r` using `ae_iff.mpr (nu_conc_of hSG hyp)`. Establish `hlow : ∀ᵐ x ∂ν, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ≤ (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2` using `by filter_upwards [hνG] with x hxG`. Distinguish the cases in `hxP : x ∈ P`.

Rewrite using `[Set.indicator_of_mem hxP]`. Establish `hb : ENNReal.ofReal ε ≤ (‖A (Matrix.of x)‖₊ : ℝ≥0∞)`. Use `ENNReal.ofReal_le_of_le_toReal ?_` and prove the remaining obligations. Rewrite using `[ENNReal.coe_toReal, coe_nnnorm]`. Conclude with `(key x hxG hxP).le`.

Use `gcongr`. Rewrite using `[Set.indicator_of_notMem hxP]`. Conclude with `bot_le`. Use `⟨x₀, hx₀, ξ, fun hzero => ?_⟩` and prove the remaining obligations. Establish `hmono : ∫⁻ x, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ∂ν ≤ ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν` using `lintegral_mono_ae hlow`.

Establish `hz' : ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0` using `hzero`. Rewrite `hmono` using `[lintegral_indicator_const hPm, hz']`. Establish `hne0 : ENNReal.ofReal ε ^ 2 * ν P ≠ 0` using `mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hε).ne') hPpos`. Conclude with `hne0 (le_zero_iff.mp hmono)`.
-/
theorem aNonzero_of (hSG : SGrp) (hPU : PiUnit) (hSP : SProd) (hAE : AEquiv) (hAC : ACont) :
    ANonzero := by
  intro hNV k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW
  obtain ⟨hset, hDS, hHC, hLU, hG, -, -, hW, hN, -, -⟩ := id hyp
  obtain ⟨hk1, hev, hz, hT, hc, hu, hl, hI, hH2, hGB⟩ := hset
  have hk2 : 2 ≤ k := by obtain ⟨m, hm⟩ := hev; omega
  obtain ⟨x, x₀, hx, hx₀, hne⟩ :=
    hNV k r z c u v b hk2 hev hz hT hc hu hl hI hH2 hGB H σ hDS Vp π hHC w hLU μW μN hW hN
  have hFi : Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹) (μW.prod μN) := by
    by_contra hni
    exact hne (integral_undef hni)
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Vp, (∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN)) ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (ContinuousLinearMap.ext hall)
  rw [ContinuousLinearMap.integral_apply hFi] at hξ
  set A := Af z c σ π μW μN w x₀ ξ with hAdef
  have hAx : A x ≠ 0 := hξ
  have hcont : ContinuousOn A (Gr k r) :=
    hAC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  have hequiv : IsSPsiEquiv z (psiGen k r z c) π A :=
    hAE k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  obtain ⟨hWG, hNG, -, hNg, -⟩ := hSG k r z c hz hT
  have hπ := (hPU k r z u Vp π hz hT hHC).2

  have hApos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx
  obtain ⟨ε, hε, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < ‖A x‖ := ⟨‖A x‖ / 2, half_pos hApos, half_lt_self hApos⟩
  have hevn : ∀ᶠ y in nhdsWithin x (Gr k r), ε < ‖A y‖ :=
    (hcont x hx).norm.eventually (lt_mem_nhds hεlt)
  obtain ⟨U, hUo, hxU, hUsub⟩ := mem_nhdsWithin.mp hevn

  set V : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ U ∩ Gr k r} with hVdef
  have hVm : MeasurableSet V :=
    (hUo.preimage WlocSk.Grp.continuous_of).measurableSet.inter
      (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet
  have hμV : 0 < μG V := haarG_pos hG hUo hxU hx

  obtain ⟨cS, hcS0, -, hunf⟩ := unfold_of hSP hyp
  have hfm : Measurable (V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)) := measurable_one.indicator hVm
  have := hW.1
  have := hN.1
  set g : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
      (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) with hgdef
  have hU' : ∫⁻ x, g x ∂ν = cS * μG V := by
    have h := hunf _ hfm
    rw [lintegral_indicator_one hVm] at h
    exact h
  have hjoint : Measurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (fun i j => (Matrix.of (mulP q.2) * Matrix.of q.1) i j)) := by
    refine hfm.comp (Continuous.measurable ?_)
    exact (WlocSk.Grp.continuous_of.comp (continuous_mulP.comp continuous_snd)).matrix_mul
      (WlocSk.Grp.continuous_of.comp continuous_fst)
  have hgm : Measurable g := hjoint.lintegral_prod_right'
  set P : Set (Formalism.QuantumDeterminants.Mt k r) := {x | 0 < g x} with hPdef
  have hPm : MeasurableSet P := measurableSet_lt measurable_const hgm
  have hPpos : ν P ≠ 0 := by
    intro h0
    have hae : ∀ᵐ x ∂ν, g x = 0 := by
      refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) h0)
      exact pos_iff_ne_zero.mpr hx
    have h1 : ∫⁻ x, g x ∂ν = 0 := by rw [lintegral_congr_ae hae, lintegral_zero]
    rw [h1] at hU'
    exact (ENNReal.mul_pos hcS0 hμV.ne').ne' hU'.symm

  have hTae : ∀ᵐ p ∂(μW.prod μN),
      Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
      Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hW.2.2.1)
    have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hN.2.2.1)
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1, hp2⟩

  have key : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Gr k r → 0 < g x → ε < ‖A (Matrix.of x)‖ := by
    intro x hxG hgx
    by_contra hle
    apply hgx.ne'
    have hae : ∀ᵐ p ∂(μW.prod μN), V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
        (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) = 0 := by
      filter_upwards [hTae] with p hp
      apply Set.indicator_of_notMem
      intro hpV
      have h1 : ε < ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ := hUsub hpV
      have h2 : ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ = ‖A (Matrix.of x)‖ := by
        rw [hequiv _ hp.1 _ hp.2 _ hxG, norm_smul, (hNg _ hp.2 _ hp.2).2.2.2.2, hπ _ hp.1, one_mul]
      exact hle (h2 ▸ h1)
    show ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
        (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) = 0
    rw [lintegral_congr_ae hae, lintegral_zero]
  have hνG : ∀ᵐ x ∂ν, Matrix.of x ∈ Gr k r := ae_iff.mpr (nu_conc_of hSG hyp)
  have hlow : ∀ᵐ x ∂ν, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ≤
      (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hνG] with x hxG
    by_cases hxP : x ∈ P
    · rw [Set.indicator_of_mem hxP]
      have hb : ENNReal.ofReal ε ≤ (‖A (Matrix.of x)‖₊ : ℝ≥0∞) := by
        refine ENNReal.ofReal_le_of_le_toReal ?_
        rw [ENNReal.coe_toReal, coe_nnnorm]
        exact (key x hxG hxP).le
      gcongr
    · rw [Set.indicator_of_notMem hxP]
      exact bot_le
  refine ⟨x₀, hx₀, ξ, fun hzero => ?_⟩
  have hmono : ∫⁻ x, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ∂ν ≤
      ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν := lintegral_mono_ae hlow
  have hz' : ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0 := hzero
  rw [lintegral_indicator_const hPm, hz'] at hmono
  have hne0 : ENNReal.ofReal ε ^ 2 * ν P ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hε).ne') hPpos
  exact hne0 (le_zero_iff.mp hmono)

end WlocSk.ANz
