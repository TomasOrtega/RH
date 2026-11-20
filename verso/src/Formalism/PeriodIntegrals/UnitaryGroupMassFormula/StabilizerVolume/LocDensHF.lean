import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCountHolds

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Core

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/- English proof (translation)
Take `⟨hconc, hdis, hcont⟩` from `hfib`. Establish `hpre : ∀ b, f ⁻¹' {ι b} = G ⁻¹' {b}`. Introduce `b`. Use extensionality with `x`. Simplify using `[hfG, hι.eq_iff]`.

Use `set S : ℕ → Set X := fun n => {z | z - T ∈ H n} with hSdef`. Use `set P : ℕ → Set V := fun n => Q ∩ G ⁻¹' S n with hPdef`. Establish `hSo : ∀ n, IsOpen (S n)` using `fun n => (hHo n).preimage (continuous_id.sub continuous_const)`. Establish `hScl : ∀ n, IsClosed (S n)` using `fun n => (AddSubgroup.isClosed_of_isOpen _ (hHo n)).preimage (continuous_id.sub continuous_const)`. Establish `hSeq : ∀ n, S n = (fun w => w + -T) ⁻¹' (H n : Set X)`.

Introduce `n`. Use extensionality with `z`. Simplify using `[hSdef, sub_eq_add_neg]`. Establish `hSc : ∀ n, IsCompact (S n)`. Introduce `n`.

Establish `: S n = (fun w => w + T) '' (H n : Set X)`. Use extensionality with `z`. Simplify using `only [hSdef, mem_setOf_eq, mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Conclude with `⟨z - T, hz, by abel⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Simplify using `using hw`. Rewrite using `[this]`. Conclude with `(hHc n).image (continuous_id.add continuous_const)`.

Establish `hνS : ∀ n, ν (S n) = ν (H n)`. Introduce `n`. Rewrite using `[hSeq, measure_preimage_add_right]`. Establish `hPcl : ∀ n, IsClosed (P n)` using `fun n => hQcl.inter ((hScl n).preimage hGc)`. Establish `hPo : ∀ n, IsOpen (P n)` using `fun n => hQo.inter ((hSo n).preimage hGc)`.

Establish `hPc : ∀ n, IsCompact (P n)` using `fun n => hQc.of_isClosed_subset (hPcl n) inter_subset_left`. Establish `hPm : ∀ n, MeasurableSet (P n)` using `fun n => (hPo n).measurableSet`. Establish `hO : (fun w : X => T + w) ⁻¹' (Nb ∩ B) ∈ 𝓝 (0 : X)`. Establish `hc : Continuous fun w : X => T + w` using `continuous_const.add continuous_id`. Conclude with `hc.continuousAt.preimage_mem_nhds (by simpa using inter_mem hNb hB)`.

Take `⟨k, hk⟩` from `hHb _ hO`. Establish `hSk : ∀ z ∈ S k, z ∈ Nb ∩ B`. Introduce `z hz`. Use `hk hz` as an intermediate fact. Simplify using `using this`.

Establish `hPkU : P k ⊆ U` using `fun x hx => hNbU x (hSk _ hx.2).1`. Use `set φ : V → ℝ := (P k).indicator (fun _ => (1 : ℝ)) with hφdef`. Establish `hφc : Continuous φ` using `(LocallyConstant.indicator (LocallyConstant.const V (1 : ℝ)) ⟨hPcl k, hPo k⟩).isLocallyConstant.continuous`. Establish `hφs : HasCompactSupport φ` using `HasCompactSupport.intro' (hPc k) (hPcl k) fun x hx => indicator_of_notMem hx _`. Establish `hφU : tsupport φ ⊆ U` using `(closure_minimal Set.support_indicator_subset (hPcl k)).trans hPkU`.

Take `⟨hint, hΦc⟩` from `hcont φ hφc hφs hφU`. Use `set Φ : X → ℝ := fun b => ∫ x, φ x ∂(fib b) with hΦdef`. Establish `hΦval : ∀ b, Φ b = (fib b).real (P k)` using `fun b => integral_indicator_one (hPm k)`. Establish `hfin : ∀ b ∈ B, fib b (P k) ≠ ⊤`. Introduce `b hb`.

Establish `h` using `hint b hb`. Rewrite `h` using `[hφdef, integrable_indicator_iff (hPm k)]`. Conclude with `((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne`. Establish `hcon : ∀ b (A : Set V), fib b A = fib b (A ∩ (G ⁻¹' {b} ∩ U))`. Introduce `b A`.

Rewrite using `[measure_inter_conull]`. Rewrite using `[← hpre]`. Conclude with `hconc b`. Establish `hPn : ∀ n, (H n : Set X) ⊆ H k → ∀ b, fib b (P n) = (S n).indicator (fun b => fib b (P k)) b`. Introduce `n hn b`.

Distinguish the cases in `hb : b ∈ S n`. Rewrite using `[indicator_of_mem hb, hcon b (P n), hcon b (P k)]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨hxQ, _⟩, hxb, hxU⟩`. Establish `hxb' : G x = b` using `hxb`. Use `⟨⟨hxQ, ?_⟩, hxb, hxU⟩` and prove the remaining obligations. Use `show G x ∈ S k`. Rewrite using `[hxb']`.

Conclude with `hn hb`. Introduce and unpack `⟨⟨hxQ, _⟩, hxb, hxU⟩`. Establish `hxb' : G x = b` using `hxb`. Use `⟨⟨hxQ, ?_⟩, hxb, hxU⟩` and prove the remaining obligations. Use `show G x ∈ S n`.

Rewrite using `[hxb']`. Conclude with `hb`. Rewrite using `[indicator_of_notMem hb, hcon b (P n)]`. Use `measure_empty (μ := fib b)` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Use `⟨fun hx => ?_, fun hx => hx.elim⟩` and prove the remaining obligations. Take `⟨⟨_, hxS⟩, hxb, _⟩` from `hx`. Establish `hxb' : G x = b` using `hxb`. Establish `hxS' : G x ∈ S n` using `hxS`. Rewrite `hxS'` using `[hxb']`.

Conclude with `hb hxS'`. Establish `hstep : ∀ n, (H n : Set X) ⊆ H k → μ.real (P n) = ∫ b in S n, Φ b ∂ν`. Introduce `n hn`. Establish `hSnk : S n ⊆ S k` using `fun z hz => hn hz`. Establish `hΦon : ContinuousOn Φ (S n)` using `hΦc.mono fun z hz => (hSk z (hSnk hz)).2`.

Establish `hΦint : IntegrableOn Φ (S n) ν` using `hΦon.integrableOn_compact (hSc n)`. Establish `hΦnn : ∀ b, 0 ≤ Φ b` using `fun b => integral_nonneg fun x => by`. Simplify using `only [hφdef]`. Conclude with `indicator_nonneg (fun _ _ => zero_le_one) x`. Establish `h1 : μ (P n) = ∫⁻ b in S n, ENNReal.ofReal (Φ b) ∂ν`.

Establish `hU : μ (P n) = ∫⁻ x in U, (P n).indicator 1 x ∂μ`. Rewrite using `[lintegral_indicator_one (hPm n), Measure.restrict_apply (hPm n), inter_eq_left.2 (fun x hx => hPkU ⟨hx.1, hn hx.2⟩)]`. Rewrite using `[hU, hdis ((P n).indicator 1) (measurable_one.indicator (hPm n))]`. Repeatedly rewrite using `[lintegral_indicator_one (hPm n)]`. Rewrite using `[← lintegral_indicator (hSo n).measurableSet]`.

Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Rewrite using `[hPn n hn b]`. Distinguish the cases in `hb : b ∈ S n`. Rewrite using `[indicator_of_mem hb, indicator_of_mem hb, hΦval, measureReal_def, ENNReal.ofReal_toReal (hfin b (hSk b (hSnk hb)).2)]`. Rewrite using `[indicator_of_notMem hb, indicator_of_notMem hb]`.

Rewrite using `[measureReal_def, h1, ← ofReal_integral_eq_lintegral_ofReal hΦint (Eventually.of_forall hΦnn), ENNReal.toReal_ofReal (setIntegral_nonneg (hSo n).measurableSet fun b _ => hΦnn b)]`. Establish `hνpos : ∀ n, 0 < ν.real (H n)`. Introduce `n`. Rewrite using `[measureReal_def]`. Conclude with `ENNReal.toReal_pos ((hHo n).measure_pos ν ⟨0, (H n).zero_mem⟩).ne' (hHc n).measure_lt_top.ne`.

Establish `hκ : κ = Φ T`. Establish `hΦT : ContinuousAt Φ T` using `hΦc.continuousAt hB`. Use `eq_of_forall_dist_le fun ε hε => ?_` and prove the remaining obligations. Establish `hev : ∀ᶠ b in 𝓝 T, dist (Φ b) (Φ T) < ε` using `hΦT.eventually (Metric.ball_mem_nhds _ hε)`. Establish `hO' : (fun w : X => T + w) ⁻¹' {b | dist (Φ b) (Φ T) < ε} ∩ (H k : Set X) ∈ 𝓝 (0 : X)`.

Establish `hc : Continuous fun w : X => T + w` using `continuous_const.add continuous_id`. Use `inter_mem (hc.continuousAt.preimage_mem_nhds (by show _ ∈ 𝓝 (T + 0); rw [add_zero]; exact hev)) ?_` and prove the remaining obligations. Conclude with `(hHo k).mem_nhds (H k).zero_mem`. Take `⟨n, hn⟩` from `hHb _ hO'`. Establish `hnk : (H n : Set X) ⊆ H k` using `fun z hz => (hn hz).2`.

Establish `hclose : ∀ b ∈ S n, ‖Φ b - Φ T‖ ≤ ε`. Introduce `b hb`. Use `(hn hb).1` as an intermediate fact. Simplify using `only [mem_preimage, mem_setOf_eq, add_sub_cancel] at this`. Rewrite using `[← dist_eq_norm]`.

Conclude with `this.le`. Establish `hΦint : IntegrableOn Φ (S n) ν` using `(hΦc.mono fun z hz => (hSk z (hnk hz)).2).integrableOn_compact (hSc n)`. Establish `hbound` using `norm_setIntegral_le_of_norm_le_const (μ := ν) (hSc n).measure_lt_top hclose`. Rewrite `hbound` using `[integral_sub hΦint (integrableOn_const (hSc n).measure_lt_top.ne), setIntegral_const, ← hstep n hnk, hratio n, smul_eq_mul]`. Establish `hνSn : ν.real (S n) = ν.real (H n)` using `by rw [measureReal_def, measureReal_def, hνS]`.

Rewrite `hbound` using `[hνSn, mul_comm (ν.real (H n : Set X)) (Φ T), ← sub_mul, norm_mul, Real.norm_of_nonneg (hνpos n).le]`. Rewrite using `[Real.dist_eq, ← Real.norm_eq_abs]`. Conclude with `le_of_mul_le_mul_right hbound (hνpos n)`. Establish `hT : T ∈ S k` using `by simp [hSdef, (H k).zero_mem]`. Establish `hae : ∀ᵐ x ∂(fib T), Q.indicator (1 : V → ℂ) x = ((φ x : ℝ) : ℂ)`.

Establish `hm : G ⁻¹' {T} ∩ U ∈ ae (fib T)`. Rewrite using `[mem_ae_iff, ← hpre]`. Conclude with `hconc T`. Use `filter_upwards [hm] with x hx`. Establish `hxT : G x = T` using `hx.1`.

Distinguish the cases in `hxQ : x ∈ Q`. Establish `hxP : x ∈ P k` using `⟨hxQ, by simp only [mem_preimage, hxT]; exact hT⟩`. Simplify using `[hφdef, indicator_of_mem hxQ, indicator_of_mem hxP]`. Establish `hxP : x ∉ P k` using `fun h => hxQ h.1`. Simplify using `[hφdef, indicator_of_notMem hxQ, indicator_of_notMem hxP]`.

Rewrite using `[integral_congr_ae hae, integral_complex_ofReal, hκ]`.
-/
theorem fib_of_ratio (μ : Measure V) (ν : Measure X) [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (hNbU : ∀ x, G x ∈ Nb → x ∈ U) (Q : Set V) (hQo : IsOpen Q) (hQcl : IsClosed Q)
    (hQc : IsCompact Q) (H : ℕ → AddSubgroup X) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (κ : ℝ) (hratio : ∀ n, μ.real (Q ∩ G ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n)) :
    ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (κ : ℂ) := by
  obtain ⟨hconc, hdis, hcont⟩ := hfib
  have hpre : ∀ b, f ⁻¹' {ι b} = G ⁻¹' {b} := by
    intro b
    ext x
    simp [hfG, hι.eq_iff]
  set S : ℕ → Set X := fun n => {z | z - T ∈ H n} with hSdef
  set P : ℕ → Set V := fun n => Q ∩ G ⁻¹' S n with hPdef
  have hSo : ∀ n, IsOpen (S n) := fun n => (hHo n).preimage (continuous_id.sub continuous_const)
  have hScl : ∀ n, IsClosed (S n) := fun n =>
    (AddSubgroup.isClosed_of_isOpen _ (hHo n)).preimage (continuous_id.sub continuous_const)
  have hSeq : ∀ n, S n = (fun w => w + -T) ⁻¹' (H n : Set X) := by
    intro n
    ext z
    simp [hSdef, sub_eq_add_neg]
  have hSc : ∀ n, IsCompact (S n) := by
    intro n
    have : S n = (fun w => w + T) '' (H n : Set X) := by
      ext z
      simp only [hSdef, mem_setOf_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - T, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [this]
    exact (hHc n).image (continuous_id.add continuous_const)
  have hνS : ∀ n, ν (S n) = ν (H n) := by
    intro n
    rw [hSeq, measure_preimage_add_right]
  have hPcl : ∀ n, IsClosed (P n) := fun n => hQcl.inter ((hScl n).preimage hGc)
  have hPo : ∀ n, IsOpen (P n) := fun n => hQo.inter ((hSo n).preimage hGc)
  have hPc : ∀ n, IsCompact (P n) := fun n => hQc.of_isClosed_subset (hPcl n) inter_subset_left
  have hPm : ∀ n, MeasurableSet (P n) := fun n => (hPo n).measurableSet

  have hO : (fun w : X => T + w) ⁻¹' (Nb ∩ B) ∈ 𝓝 (0 : X) := by
    have hc : Continuous fun w : X => T + w := continuous_const.add continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using inter_mem hNb hB)
  obtain ⟨k, hk⟩ := hHb _ hO
  have hSk : ∀ z ∈ S k, z ∈ Nb ∩ B := by
    intro z hz
    have := hk hz
    simpa using this
  have hPkU : P k ⊆ U := fun x hx => hNbU x (hSk _ hx.2).1
  set φ : V → ℝ := (P k).indicator (fun _ => (1 : ℝ)) with hφdef
  have hφc : Continuous φ :=
    (LocallyConstant.indicator (LocallyConstant.const V (1 : ℝ))
      ⟨hPcl k, hPo k⟩).isLocallyConstant.continuous
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro' (hPc k) (hPcl k) fun x hx => indicator_of_notMem hx _
  have hφU : tsupport φ ⊆ U :=
    (closure_minimal Set.support_indicator_subset (hPcl k)).trans hPkU
  obtain ⟨hint, hΦc⟩ := hcont φ hφc hφs hφU
  set Φ : X → ℝ := fun b => ∫ x, φ x ∂(fib b) with hΦdef
  have hΦval : ∀ b, Φ b = (fib b).real (P k) := fun b => integral_indicator_one (hPm k)
  have hfin : ∀ b ∈ B, fib b (P k) ≠ ⊤ := by
    intro b hb
    have h := hint b hb
    rw [hφdef, integrable_indicator_iff (hPm k)] at h
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne

  have hcon : ∀ b (A : Set V), fib b A = fib b (A ∩ (G ⁻¹' {b} ∩ U)) := by
    intro b A
    rw [measure_inter_conull]
    rw [← hpre]
    exact hconc b
  have hPn : ∀ n, (H n : Set X) ⊆ H k → ∀ b, fib b (P n) = (S n).indicator (fun b => fib b (P k)) b := by
    intro n hn b
    by_cases hb : b ∈ S n
    · rw [indicator_of_mem hb, hcon b (P n), hcon b (P k)]
      congr 1
      ext x
      constructor
      · rintro ⟨⟨hxQ, _⟩, hxb, hxU⟩
        have hxb' : G x = b := hxb
        refine ⟨⟨hxQ, ?_⟩, hxb, hxU⟩
        show G x ∈ S k
        rw [hxb']
        exact hn hb
      · rintro ⟨⟨hxQ, _⟩, hxb, hxU⟩
        have hxb' : G x = b := hxb
        refine ⟨⟨hxQ, ?_⟩, hxb, hxU⟩
        show G x ∈ S n
        rw [hxb']
        exact hb
    · rw [indicator_of_notMem hb, hcon b (P n)]
      convert measure_empty (μ := fib b)
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      obtain ⟨⟨_, hxS⟩, hxb, _⟩ := hx
      have hxb' : G x = b := hxb
      have hxS' : G x ∈ S n := hxS
      rw [hxb'] at hxS'
      exact hb hxS'

  have hstep : ∀ n, (H n : Set X) ⊆ H k → μ.real (P n) = ∫ b in S n, Φ b ∂ν := by
    intro n hn
    have hSnk : S n ⊆ S k := fun z hz => hn hz
    have hΦon : ContinuousOn Φ (S n) := hΦc.mono fun z hz => (hSk z (hSnk hz)).2
    have hΦint : IntegrableOn Φ (S n) ν := hΦon.integrableOn_compact (hSc n)
    have hΦnn : ∀ b, 0 ≤ Φ b := fun b => integral_nonneg fun x => by
      simp only [hφdef]
      exact indicator_nonneg (fun _ _ => zero_le_one) x
    have h1 : μ (P n) = ∫⁻ b in S n, ENNReal.ofReal (Φ b) ∂ν := by
      have hU : μ (P n) = ∫⁻ x in U, (P n).indicator 1 x ∂μ := by
        rw [lintegral_indicator_one (hPm n), Measure.restrict_apply (hPm n),
          inter_eq_left.2 (fun x hx => hPkU ⟨hx.1, hn hx.2⟩)]
      rw [hU, hdis ((P n).indicator 1) (measurable_one.indicator (hPm n))]
      simp_rw [lintegral_indicator_one (hPm n)]
      rw [← lintegral_indicator (hSo n).measurableSet]
      refine lintegral_congr fun b => ?_
      rw [hPn n hn b]
      by_cases hb : b ∈ S n
      · rw [indicator_of_mem hb, indicator_of_mem hb, hΦval, measureReal_def,
          ENNReal.ofReal_toReal (hfin b (hSk b (hSnk hb)).2)]
      · rw [indicator_of_notMem hb, indicator_of_notMem hb]
    rw [measureReal_def, h1, ← ofReal_integral_eq_lintegral_ofReal hΦint
      (Eventually.of_forall hΦnn), ENNReal.toReal_ofReal (setIntegral_nonneg
        (hSo n).measurableSet fun b _ => hΦnn b)]

  have hνpos : ∀ n, 0 < ν.real (H n) := by
    intro n
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo n).measure_pos ν ⟨0, (H n).zero_mem⟩).ne'
      (hHc n).measure_lt_top.ne
  have hκ : κ = Φ T := by
    have hΦT : ContinuousAt Φ T := hΦc.continuousAt hB
    refine eq_of_forall_dist_le fun ε hε => ?_
    have hev : ∀ᶠ b in 𝓝 T, dist (Φ b) (Φ T) < ε := hΦT.eventually (Metric.ball_mem_nhds _ hε)
    have hO' : (fun w : X => T + w) ⁻¹' {b | dist (Φ b) (Φ T) < ε} ∩ (H k : Set X) ∈ 𝓝 (0 : X) := by
      have hc : Continuous fun w : X => T + w := continuous_const.add continuous_id
      refine inter_mem (hc.continuousAt.preimage_mem_nhds (by show _ ∈ 𝓝 (T + 0); rw [add_zero]; exact hev)) ?_
      exact (hHo k).mem_nhds (H k).zero_mem
    obtain ⟨n, hn⟩ := hHb _ hO'
    have hnk : (H n : Set X) ⊆ H k := fun z hz => (hn hz).2
    have hclose : ∀ b ∈ S n, ‖Φ b - Φ T‖ ≤ ε := by
      intro b hb
      have := (hn hb).1
      simp only [mem_preimage, mem_setOf_eq, add_sub_cancel] at this
      rw [← dist_eq_norm]
      exact this.le
    have hΦint : IntegrableOn Φ (S n) ν :=
      (hΦc.mono fun z hz => (hSk z (hnk hz)).2).integrableOn_compact (hSc n)
    have hbound := norm_setIntegral_le_of_norm_le_const (μ := ν) (hSc n).measure_lt_top hclose
    rw [integral_sub hΦint (integrableOn_const (hSc n).measure_lt_top.ne), setIntegral_const,
      ← hstep n hnk, hratio n, smul_eq_mul] at hbound
    have hνSn : ν.real (S n) = ν.real (H n) := by rw [measureReal_def, measureReal_def, hνS]
    rw [hνSn, mul_comm (ν.real (H n : Set X)) (Φ T), ← sub_mul, norm_mul,
      Real.norm_of_nonneg (hνpos n).le] at hbound
    rw [Real.dist_eq, ← Real.norm_eq_abs]
    exact le_of_mul_le_mul_right hbound (hνpos n)

  have hT : T ∈ S k := by simp [hSdef, (H k).zero_mem]
  have hae : ∀ᵐ x ∂(fib T), Q.indicator (1 : V → ℂ) x = ((φ x : ℝ) : ℂ) := by
    have hm : G ⁻¹' {T} ∩ U ∈ ae (fib T) := by
      rw [mem_ae_iff, ← hpre]
      exact hconc T
    filter_upwards [hm] with x hx
    have hxT : G x = T := hx.1
    by_cases hxQ : x ∈ Q
    · have hxP : x ∈ P k := ⟨hxQ, by simp only [mem_preimage, hxT]; exact hT⟩
      simp [hφdef, indicator_of_mem hxQ, indicator_of_mem hxP]
    · have hxP : x ∉ P k := fun h => hxQ h.1
      simp [hφdef, indicator_of_notMem hxQ, indicator_of_notMem hxP]
  rw [integral_congr_ae hae, integral_complex_ofReal, hκ]

end Core

section Lat

variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] in
/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_inter_iff, mem_setOf_eq, mem_preimage, hlev, neg_add_eq_sub, add_sub_cancel]`.
-/
theorem cos_inter_eq (Λ0 : AddSubgroup V) (Hn : AddSubgroup X) (G : V → X) (y : V) (T : X) :
    {x | x - y ∈ Λ0} ∩ G ⁻¹' {z | z - T ∈ Hn} = (fun x => -y + x) ⁻¹' hlev Λ0 Hn G y T := by
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, hlev, neg_add_eq_sub, add_sub_cancel]

/- English proof (translation)
Rewrite using `[cos_inter_eq, measure_preimage_add]`. Establish `hh : T - G y ∈ H 0`. Use `(H 0).neg_mem hyT` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Conclude with `hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hh n`.
-/
theorem cos_ratio (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (T : X) (hyT : G y - T ∈ H 0) (n : ℕ) :
    μ ({x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  rw [cos_inter_eq, measure_preimage_add]
  have hh : T - G y ∈ H 0 := by
    have := (H 0).neg_mem hyT
    rwa [neg_sub] at this
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hh n

end Lat

section Fin

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/- English proof (translation)
Establish `hQe : {x | x - y ∈ Λ 0} = (fun x => x + -y) ⁻¹' (Λ 0 : Set V)`. Use extensionality with `x`. Simplify using `[sub_eq_add_neg]`. Establish `hQo : IsOpen {x | x - y ∈ Λ 0}` using `(hΛo 0).preimage (continuous_id.sub continuous_const)`. Establish `hQcl : IsClosed {x | x - y ∈ Λ 0}` using `(AddSubgroup.isClosed_of_isOpen _ (hΛo 0)).preimage (continuous_id.sub continuous_const)`.

Establish `hQc : IsCompact {x | x - y ∈ Λ 0}`. Establish `: {x | x - y ∈ Λ 0} = (fun w => w + y) '' (Λ 0 : Set V)`. Use extensionality with `z`. Simplify using `only [mem_setOf_eq, mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Conclude with `⟨z - y, hz, by abel⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Simplify using `using hw`. Rewrite using `[this]`.

Conclude with `(hΛc 0).image (continuous_id.add continuous_const)`. Establish `hν0 : 0 < ν.real (H 0)`. Rewrite using `[measureReal_def]`. Conclude with `ENNReal.toReal_pos ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne' (hHc 0).measure_lt_top.ne`. Establish `hratio : ∀ n, μ.real ({x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}) = μ.real (Λ 0 : Set V) / ν.real (H 0) * ν.real (H n)`.

Introduce `n`. Establish `e` using `cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hyT n`. Establish `e'` using `congrArg ENNReal.toReal e`. Rewrite `e'` using `[ENNReal.toReal_mul, ENNReal.toReal_mul]`. Simplify using `only [← measureReal_def] at e'`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[fib_of_ratio μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU _ hQo hQcl hQc H hHo hHc hHb _ hratio, ENNReal.toReal_div, measureReal_def, measureReal_def]`.
-/
theorem fibCos (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (hNbU : ∀ x, G x ∈ Nb → x ∈ U)
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛc : ∀ n, IsCompact (Λ n : Set V)) (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (hyT : G y - T ∈ H 0) :
    ∫ x, {x | x - y ∈ Λ 0}.indicator (1 : V → ℂ) x ∂(fib T) =
      (((μ (Λ 0 : Set V)) / ν (H 0)).toReal : ℂ) := by
  have hQe : {x | x - y ∈ Λ 0} = (fun x => x + -y) ⁻¹' (Λ 0 : Set V) := by
    ext x; simp [sub_eq_add_neg]
  have hQo : IsOpen {x | x - y ∈ Λ 0} := (hΛo 0).preimage (continuous_id.sub continuous_const)
  have hQcl : IsClosed {x | x - y ∈ Λ 0} :=
    (AddSubgroup.isClosed_of_isOpen _ (hΛo 0)).preimage (continuous_id.sub continuous_const)
  have hQc : IsCompact {x | x - y ∈ Λ 0} := by
    have : {x | x - y ∈ Λ 0} = (fun w => w + y) '' (Λ 0 : Set V) := by
      ext z
      simp only [mem_setOf_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - y, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [this]
    exact (hΛc 0).image (continuous_id.add continuous_const)
  have hν0 : 0 < ν.real (H 0) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
      (hHc 0).measure_lt_top.ne
  have hratio : ∀ n, μ.real ({x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}) =
      μ.real (Λ 0 : Set V) / ν.real (H 0) * ν.real (H n) := by
    intro n
    have e := cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hyT n
    have e' := congrArg ENNReal.toReal e
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at e'
    simp only [← measureReal_def] at e'
    field_simp
    linarith
  rw [fib_of_ratio μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU _ hQo hQcl hQc H hHo hHc
    hHb _ hratio, ENNReal.toReal_div, measureReal_def, measureReal_def]

end Fin

/- English proof (translation)
Introduce `V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc hHb hyp`. Use `hμ` as an intermediate fact. Use `hν` as an intermediate fact. Establish `hLcl : IsClosed (L : Set V)` using `AddSubgroup.isClosed_of_isOpen _ hLo`. Establish `hScl : ∀ n, IsClosed {z | z - T ∈ H n}` using `fun n => (AddSubgroup.isClosed_of_isOpen _ (hHo n)).preimage (continuous_id.sub continuous_const)`.

Use `set Pn : ℕ → Set V := fun n => (L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n} with hPndef`. Establish `hPcl : ∀ n, IsClosed (Pn n)` using `fun n => hLcl.inter ((hScl n).preimage hGc)`. Establish `hPo : ∀ n, IsOpen (Pn n)` using `fun n => hLo.inter (((hHo n).preimage (continuous_id.sub continuous_const)).preimage hGc)`. Establish `hPc : ∀ n, IsCompact (Pn n)` using `fun n => hLc.of_isClosed_subset (hPcl n) inter_subset_left`. Establish `hν0 : 0 < ν.real (H 0)`.

Rewrite using `[measureReal_def]`. Conclude with `ENNReal.toReal_pos ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne' (hHc 0).measure_lt_top.ne`. Distinguish the cases in `hne : (Pn 0).Nonempty`. Take `⟨y0, hy0⟩` from `hne`. Take `⟨D0, hD0, _⟩` from `hyp y0 hy0.1 hy0.2`.

Establish `hHa : ∀ n, H n ≤ H 0`. Introduce `n`. Rewrite using `[← hD0, ← hD0]`. Conclude with `AddSubgroup.map_mono (hΛa (Nat.zero_le n))`. Establish `hsat : ∀ y ∈ Pn 0, ∀ Z ∈ Λ 0, y + Z ∈ Pn 0`.

Introduce and unpack `y ⟨hyL, hyS⟩ Z hZ`. Take `⟨D, hD, hG⟩` from `hyp y hyL hyS`. Use `⟨L.add_mem hyL (hΛL hZ), ?_⟩` and prove the remaining obligations. Establish `h1` using `hG 0 0 (Λ 0).zero_mem Z hZ`. Simplify using `only [add_zero] at h1`.

Establish `h2 : D Z ∈ H 0` using `hD 0 ▸ AddSubgroup.mem_map_of_mem D hZ`. Establish `hyS' : G y - T ∈ H 0` using `hyS`. Use `show G (y + Z) - T ∈ H 0`. Establish `e : G (y + Z) - T = (G (y + Z) - G y - D Z) + D Z + (G y - T)` using `by abel`. Rewrite using `[e]`.

Conclude with `(H 0).add_mem ((H 0).add_mem (hHa 1 h1) h2) hyS'`. Establish `: DiscreteTopology (V ⧸ Λ 0)` using `QuotientAddGroup.discreteTopology (hΛo 0)`. Set `q : V → V ⧸ Λ 0` to `QuotientAddGroup.mk`. Establish `hq : Continuous q` using `continuous_quot_mk`. Establish `hfin : (q '' Pn 0).Finite` using `((hPc 0).image hq).finite_of_discrete`.

Use `set Tf := hfin.toFinset with hTf`. Establish `hmemT : ∀ p, p ∈ Tf ↔ ∃ y ∈ Pn 0, q y = p`. Introduce `p`. Simplify using `[hTf]`. Establish `hcos : ∀ y, q ⁻¹' {q y} = {x | x - y ∈ Λ 0}`.

Introduce `y`. Use extensionality with `x`. Simplify using `only [mem_preimage, mem_singleton_iff, mem_setOf_eq, q]`. Conclude with `QuotientAddGroup.eq_iff_sub_mem`. Establish `hcount : ∀ n, μ (Pn n) * ν (H 0) = (Tf.card : ENNReal) * (μ (Λ 0) * ν (H n))`.

Introduce `n`. Establish `hdec : Pn n = ⋃ p ∈ Tf, (Pn n ∩ q ⁻¹' {p})`. Use extensionality with `x`. Simplify using `only [mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `⟨q x, (hmemT _).2 ⟨x, ⟨hx.1, hHa n hx.2⟩, rfl⟩, hx, rfl⟩` and prove the remaining obligations. Introduce and unpack `⟨_, _, hx, _⟩`. Conclude with `hx`. Establish `hdisj : PairwiseDisjoint (↑Tf : Set (V ⧸ Λ 0)) (fun p => Pn n ∩ q ⁻¹' {p})` using `fun p _ p' _ hne => ((disjoint_singleton.2 hne).preimage q).mono inter_subset_right inter_subset_right`.

Establish `hmeas : ∀ p ∈ Tf, MeasurableSet (Pn n ∩ q ⁻¹' {p})` using `fun p _ => (hPo n).measurableSet.inter ((isOpen_discrete ({p} : Set (V ⧸ Λ 0))).preimage hq).measurableSet`. Establish `hval : ∀ p ∈ Tf, μ (Pn n ∩ q ⁻¹' {p}) * ν (H 0) = μ (Λ 0) * ν (H n)`. Introduce `p hp`. Take `⟨y, hy, rfl⟩` from `(hmemT p).1 hp`. Take `⟨D, hD, hG⟩` from `hyp y hy.1 hy.2`.

Establish `e : Pn n ∩ q ⁻¹' {q y} = {x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}`. Rewrite using `[hcos]`. Use extensionality with `x`. Simplify using `only [hPndef, mem_inter_iff, mem_setOf_eq, mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨_, hxS⟩, hxy⟩`. Conclude with `⟨hxy, hxS⟩`. Introduce and unpack `⟨hxy, hxS⟩`. Use `⟨⟨?_, hxS⟩, hxy⟩` and prove the remaining obligations. Use `L.add_mem hy.1 (hΛL hxy)` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[e]`. Conclude with `cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hy.2 n`. Use `conv_lhs => rw [hdec]`. Rewrite using `[measure_biUnion_finset hdisj hmeas, Finset.sum_mul, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]`.

Establish `hreal : ∀ n, μ.real (Pn n) * ν.real (H 0) = (Tf.card : ℝ) * (μ.real (Λ 0 : Set V) * ν.real (H n))`. Introduce `n`. Establish `e'` using `congrArg ENNReal.toReal (hcount n)`. Simplify using `only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← measureReal_def] at e'`. Conclude with `e'`.

Establish `hratio : ∀ n, μ.real ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n}) = μ.real (Pn 0) / ν.real (H 0) * ν.real (H n)`. Introduce `n`. Establish `h0` using `hreal 0`. Establish `hn` using `hreal n`. Use `show μ.real (Pn n) = _`.

Establish `e0 : μ.real (Pn 0) = (Tf.card : ℝ) * μ.real (Λ 0 : Set V)`. Establish `h' : μ.real (Pn 0) * ν.real (H 0) = ((Tf.card : ℝ) * μ.real (Λ 0 : Set V)) * ν.real (H 0)`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_right_cancel₀ hν0.ne' h'`.

Rewrite using `[e0]`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[fib_of_ratio μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU _ hLo hLcl hLc H hHo hHc hHb _ hratio, ENNReal.toReal_div, measureReal_def, measureReal_def]`. Establish `hP0 : Pn 0 = ∅` using `not_nonempty_iff_eq_empty.1 hne`.

Establish `hP0' : (L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0} = ∅` using `hP0`. Rewrite using `[hP0', measure_empty, ENNReal.zero_div, ENNReal.toReal_zero, Complex.ofReal_zero]`. Establish `hpre : f ⁻¹' {ι T} = G ⁻¹' {T}`. Use extensionality with `x`. Simplify using `[hfG, hι.eq_iff]`.

Establish `hm : G ⁻¹' {T} ∩ U ∈ ae (fib T)`. Rewrite using `[mem_ae_iff, ← hpre]`. Conclude with `hfib.1 T`. Establish `hae : ∀ᵐ x ∂(fib T), (L : Set V).indicator (1 : V → ℂ) x = 0` using `by filter_upwards [hm] with x hx`. Establish `hxT : G x = T` using `hx.1`.

Distinguish the cases in `hxL : x ∈ (L : Set V)`. It suffices to derive a contradiction. Establish `: x ∈ Pn 0` using `⟨hxL, by show G x - T ∈ H 0`. Rewrite using `[hxT, sub_self]`. Conclude with `(H 0).zero_mem⟩`.

Rewrite `this` using `[hP0]`. Conclude with `this`. Conclude with `indicator_of_notMem hxL _`. Rewrite using `[integral_congr_ae hae, integral_zero]`.
-/
theorem fibLat_holds : FibLat := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν f ι hι G hGc hfG U B fib hfib T hB Nb hNb
    hNbU L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc hHb hyp
  have := hμ
  have := hν
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen _ hLo
  have hScl : ∀ n, IsClosed {z | z - T ∈ H n} := fun n =>
    (AddSubgroup.isClosed_of_isOpen _ (hHo n)).preimage (continuous_id.sub continuous_const)
  set Pn : ℕ → Set V := fun n => (L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n} with hPndef
  have hPcl : ∀ n, IsClosed (Pn n) := fun n => hLcl.inter ((hScl n).preimage hGc)
  have hPo : ∀ n, IsOpen (Pn n) := fun n =>
    hLo.inter (((hHo n).preimage (continuous_id.sub continuous_const)).preimage hGc)
  have hPc : ∀ n, IsCompact (Pn n) := fun n => hLc.of_isClosed_subset (hPcl n) inter_subset_left
  have hν0 : 0 < ν.real (H 0) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
      (hHc 0).measure_lt_top.ne
  by_cases hne : (Pn 0).Nonempty
  · obtain ⟨y0, hy0⟩ := hne
    obtain ⟨D0, hD0, _⟩ := hyp y0 hy0.1 hy0.2
    have hHa : ∀ n, H n ≤ H 0 := by
      intro n
      rw [← hD0, ← hD0]
      exact AddSubgroup.map_mono (hΛa (Nat.zero_le n))
    have hsat : ∀ y ∈ Pn 0, ∀ Z ∈ Λ 0, y + Z ∈ Pn 0 := by
      rintro y ⟨hyL, hyS⟩ Z hZ
      obtain ⟨D, hD, hG⟩ := hyp y hyL hyS
      refine ⟨L.add_mem hyL (hΛL hZ), ?_⟩
      have h1 := hG 0 0 (Λ 0).zero_mem Z hZ
      simp only [add_zero] at h1
      have h2 : D Z ∈ H 0 := hD 0 ▸ AddSubgroup.mem_map_of_mem D hZ
      have hyS' : G y - T ∈ H 0 := hyS
      show G (y + Z) - T ∈ H 0
      have e : G (y + Z) - T = (G (y + Z) - G y - D Z) + D Z + (G y - T) := by abel
      rw [e]
      exact (H 0).add_mem ((H 0).add_mem (hHa 1 h1) h2) hyS'
    have : DiscreteTopology (V ⧸ Λ 0) := QuotientAddGroup.discreteTopology (hΛo 0)
    let q : V → V ⧸ Λ 0 := QuotientAddGroup.mk
    have hq : Continuous q := continuous_quot_mk
    have hfin : (q '' Pn 0).Finite := ((hPc 0).image hq).finite_of_discrete
    set Tf := hfin.toFinset with hTf
    have hmemT : ∀ p, p ∈ Tf ↔ ∃ y ∈ Pn 0, q y = p := by
      intro p
      simp [hTf]
    have hcos : ∀ y, q ⁻¹' {q y} = {x | x - y ∈ Λ 0} := by
      intro y
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, q]
      exact QuotientAddGroup.eq_iff_sub_mem
    have hcount : ∀ n, μ (Pn n) * ν (H 0) = (Tf.card : ENNReal) * (μ (Λ 0) * ν (H n)) := by
      intro n
      have hdec : Pn n = ⋃ p ∈ Tf, (Pn n ∩ q ⁻¹' {p}) := by
        ext x
        simp only [mem_iUnion, exists_prop]
        constructor
        · intro hx
          refine ⟨q x, (hmemT _).2 ⟨x, ⟨hx.1, hHa n hx.2⟩, rfl⟩, hx, rfl⟩
        · rintro ⟨_, _, hx, _⟩
          exact hx
      have hdisj : PairwiseDisjoint (↑Tf : Set (V ⧸ Λ 0)) (fun p => Pn n ∩ q ⁻¹' {p}) :=
        fun p _ p' _ hne => ((disjoint_singleton.2 hne).preimage q).mono inter_subset_right
          inter_subset_right
      have hmeas : ∀ p ∈ Tf, MeasurableSet (Pn n ∩ q ⁻¹' {p}) := fun p _ =>
        (hPo n).measurableSet.inter
          ((isOpen_discrete ({p} : Set (V ⧸ Λ 0))).preimage hq).measurableSet
      have hval : ∀ p ∈ Tf, μ (Pn n ∩ q ⁻¹' {p}) * ν (H 0) = μ (Λ 0) * ν (H n) := by
        intro p hp
        obtain ⟨y, hy, rfl⟩ := (hmemT p).1 hp
        obtain ⟨D, hD, hG⟩ := hyp y hy.1 hy.2
        have e : Pn n ∩ q ⁻¹' {q y} = {x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n} := by
          rw [hcos]
          ext x
          simp only [hPndef, mem_inter_iff, mem_setOf_eq, mem_preimage]
          constructor
          · rintro ⟨⟨_, hxS⟩, hxy⟩
            exact ⟨hxy, hxS⟩
          · rintro ⟨hxy, hxS⟩
            refine ⟨⟨?_, hxS⟩, hxy⟩
            have := L.add_mem hy.1 (hΛL hxy)
            rwa [add_sub_cancel] at this
        rw [e]
        exact cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hy.2 n
      conv_lhs => rw [hdec]
      rw [measure_biUnion_finset hdisj hmeas, Finset.sum_mul, Finset.sum_congr rfl hval,
        Finset.sum_const, nsmul_eq_mul]
    have hreal : ∀ n, μ.real (Pn n) * ν.real (H 0) = (Tf.card : ℝ) * (μ.real (Λ 0 : Set V) * ν.real (H n)) := by
      intro n
      have e' := congrArg ENNReal.toReal (hcount n)
      simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← measureReal_def] at e'
      exact e'
    have hratio : ∀ n, μ.real ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H n}) =
        μ.real (Pn 0) / ν.real (H 0) * ν.real (H n) := by
      intro n
      have h0 := hreal 0
      have hn := hreal n
      show μ.real (Pn n) = _
      have e0 : μ.real (Pn 0) = (Tf.card : ℝ) * μ.real (Λ 0 : Set V) := by
        have h' : μ.real (Pn 0) * ν.real (H 0) =
            ((Tf.card : ℝ) * μ.real (Λ 0 : Set V)) * ν.real (H 0) := by
          rw [h0]
          ring
        exact mul_right_cancel₀ hν0.ne' h'
      rw [e0]
      field_simp
      linarith
    rw [fib_of_ratio μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU _ hLo hLcl hLc H hHo hHc
      hHb _ hratio, ENNReal.toReal_div, measureReal_def, measureReal_def]
  · have hP0 : Pn 0 = ∅ := not_nonempty_iff_eq_empty.1 hne
    have hP0' : (L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0} = ∅ := hP0
    rw [hP0', measure_empty, ENNReal.zero_div, ENNReal.toReal_zero, Complex.ofReal_zero]
    have hpre : f ⁻¹' {ι T} = G ⁻¹' {T} := by
      ext x
      simp [hfG, hι.eq_iff]
    have hm : G ⁻¹' {T} ∩ U ∈ ae (fib T) := by
      rw [mem_ae_iff, ← hpre]
      exact hfib.1 T
    have hae : ∀ᵐ x ∂(fib T), (L : Set V).indicator (1 : V → ℂ) x = 0 := by
      filter_upwards [hm] with x hx
      have hxT : G x = T := hx.1
      by_cases hxL : x ∈ (L : Set V)
      · exfalso
        have : x ∈ Pn 0 := ⟨hxL, by
          show G x - T ∈ H 0
          rw [hxT, sub_self]
          exact (H 0).zero_mem⟩
        rw [hP0] at this
        exact this
      · exact indicator_of_notMem hxL _
    rw [integral_congr_ae hae, integral_zero]

end PI.VolStabS
