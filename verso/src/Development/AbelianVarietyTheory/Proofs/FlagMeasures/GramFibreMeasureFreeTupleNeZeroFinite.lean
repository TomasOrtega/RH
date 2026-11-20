import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapPreimageVolumeLowerBoundStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreNonzero

open Topology Set Filter

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

/- English proof (translation)
Take `⟨O, hO, hxO, hOU, hOc⟩` from `exists_open_between_and_isCompact_closure isCompact_singleton hU (Set.singleton_subset_iff.mpr hx)`. Take `⟨g, hgs, hg1, hg01⟩` from `exists_tsupport_one_of_isOpen_isClosed hO hOc isClosed_singleton hxO`. Use `⟨g, g.continuous, ?_, hgs.trans (subset_closure.trans hOU), ?_, fun v => (hg01 v).1⟩` and prove the remaining obligations. Conclude with `hOc.of_isClosed_subset (isClosed_tsupport _) (hgs.trans subset_closure)`. Simplify using `using hg1 (Set.mem_singleton x)`.
-/
private theorem exists_continuous_compactSupport_bump_of_isOpen (hU : IsOpen U) {x : V} (hx : x ∈ U) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧ φ x = 1 ∧
      ∀ v, 0 ≤ φ v := by
  obtain ⟨O, hO, hxO, hOU, hOc⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hU
      (Set.singleton_subset_iff.mpr hx)
  obtain ⟨g, hgs, hg1, hg01⟩ :=
    exists_tsupport_one_of_isOpen_isClosed hO hOc isClosed_singleton hxO
  refine ⟨g, g.continuous, ?_, hgs.trans (subset_closure.trans hOU), ?_, fun v => (hg01 v).1⟩
  · exact hOc.of_isClosed_subset (isClosed_tsupport _) (hgs.trans subset_closure)
  · simpa using hg1 (Set.mem_singleton x)

/- English proof (translation)
Introduce `h0`. Take `⟨φ, hφc, hφs, hφU, hφx, hφ0⟩` from `exists_continuous_compactSupport_bump_of_isOpen hU hx`. Take `⟨hsupp, hdis, hcont⟩` from `h`. Take `⟨hint, hgc⟩` from `hcont φ hφc hφs hφU`. Use `set W : Set V := {v | (1 / 2 : ℝ) < φ v} with hW`.

Establish `hWo : IsOpen W` using `isOpen_lt continuous_const hφc`. Establish `hxW : x ∈ W` using `by show (1 / 2 : ℝ) < φ x`. Rewrite using `[hφx]`. Evaluate the numerical expressions. Establish `hWU : W ⊆ U` using `fun v hv => hφU (subset_tsupport _ (by show φ v ≠ 0`.

Conclude with `ne_of_gt (lt_trans (by norm_num) hv)))`. Take `⟨c, hc0, hctop, N, hN, hlbN⟩` from `hlb W hWo hxW`. Use `set e : ℝ≥0∞ := ENNReal.ofReal (1 / 2) * c with he`. Establish `he0 : e ≠ 0` using `mul_ne_zero (by simp) hc0.ne'`. Establish `hetop : e ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop`.

Establish `hepos : 0 < e.toReal` using `ENNReal.toReal_pos he0 hetop`. Use `set δ : ℝ := e.toReal / 2 with hδ`. Establish `hδpos : 0 < δ` using `by rw [hδ]; linarith`. Establish `hδe : ENNReal.ofReal δ < e`. Rewrite using `[← ENNReal.ofReal_toReal hetop, ENNReal.ofReal_lt_ofReal_iff hepos, hδ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgcont : Continuous (fun b => ∫ v, φ v ∂(fib b))` using `continuousOn_univ.mp hgc`. Establish `hg0 : (∫ v, φ v ∂(fib b0)) = 0` using `by simp [h0]`. Establish `hnear : {b | (∫ v, φ v ∂(fib b)) < δ} ∈ 𝓝 b0` using `hgcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hg0]; exact hδpos))`. Take `⟨K, hK, hKsub, hKc⟩` from `local_compact_nhds (Filter.inter_mem hN hnear)`.

Establish `hKm : MeasurableSet K` using `hKc.isClosed.measurableSet`. Establish `hK0 : 0 < ν K` using `Measure.measure_pos_of_mem_nhds ν hK`. Establish `hKtop : ν K ≠ ⊤` using `hKc.measure_lt_top.ne`. Use `set A : Set V := f' ⁻¹' K with hA`. Establish `hAm : MeasurableSet A` using `(hKc.isClosed.preimage hf').measurableSet`.

Use `set Φ : V → ℝ≥0∞ := A.indicator (fun v => ENNReal.ofReal (φ v)) with hΦ`. Establish `hΦm : Measurable Φ` using `(ENNReal.measurable_ofReal.comp hφc.measurable).indicator hAm`. Establish `hinner : ∀ b, ∫⁻ v, Φ v ∂(fib b) = K.indicator (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) b`. Introduce `b`. Establish `hon : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U` using `ae_iff.mpr (hsupp b)`.

Establish `hae : ∀ᵐ v ∂(fib b), f' v = b` using `by filter_upwards [hon] with v hv`. Apply `hι` to reduce the goal to its premises. Rewrite using `[← hff']`. Conclude with `hv.1`. Establish `hcongr : Φ =ᵐ[fib b] fun v => K.indicator (fun _ => ENNReal.ofReal (φ v)) b` using `by filter_upwards [hae] with v hv`.

Distinguish the cases in `hb : b ∈ K`. Establish `hvA : v ∈ A` using `by rw [hA, Set.mem_preimage, hv]; exact hb`. Rewrite using `[hΦ, Set.indicator_of_mem hvA, Set.indicator_of_mem hb]`. Establish `hvA : v ∉ A` using `by rw [hA, Set.mem_preimage, hv]; exact hb`. Rewrite using `[hΦ, Set.indicator_of_notMem hvA, Set.indicator_of_notMem hb]`.

Rewrite using `[lintegral_congr_ae hcongr]`. Distinguish the cases in `hb : b ∈ K`. Simplify using `only [Set.indicator_of_mem hb]`. Conclude with `(ofReal_integral_eq_lintegral_ofReal (hint b (Set.mem_univ b)) (ae_of_all _ hφ0)).symm`. Simplify using `[Set.indicator_of_notMem hb]`.

Establish `hupper : ∫⁻ v in U, Φ v ∂μ ≤ ENNReal.ofReal δ * ν K`. Rewrite using `[hdis Φ hΦm]`. Repeatedly rewrite using `[hinner]`. Rewrite using `[lintegral_indicator hKm]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hpre : f ⁻¹' (ι '' K) = A`. Use extensionality with `v`. Simplify using `only [Set.mem_preimage, Set.mem_image, hff', hA]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, hbv⟩`.

Rewrite using `[← hι hbv]` and apply the resulting hypothesis. Introduce `hv`. Conclude with `⟨_, hv, rfl⟩`. Establish `hsub : A ∩ W ⊆ {v | ENNReal.ofReal (1 / 2) ≤ Φ v} ∩ U`. Introduce `v hv`.

Use `⟨?_, hWU hv.2⟩` and prove the remaining obligations. Use `show ENNReal.ofReal (1 / 2) ≤ Φ v`. Rewrite using `[hΦ, Set.indicator_of_mem hv.1]`. Conclude with `ENNReal.ofReal_le_ofReal hv.2.le`. Establish `hlower : e * ν K ≤ ∫⁻ v in U, Φ v ∂μ`.

Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[hpre]`. Conclude with `(measure_mono hsub).trans (Measure.le_restrict_apply _ _)`. Use `_ ≤ ∫⁻ v in U, Φ v ∂μ := mul_meas_ge_le_lintegral hΦm _`.

Establish `hle` using `hlower.trans hupper`. Rewrite `hle` using `[mul_comm e, mul_comm (ENNReal.ofReal δ)]`. Conclude with `absurd hle (not_le.mpr (ENNReal.mul_lt_mul_right hK0.ne' hKtop hδe))`.
-/
theorem fib_ne_zero_of_lb (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U) {f' : V → X}
    (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    {x : V} (hx : x ∈ U) {b0 : X}
    (hlb : ∀ W : Set V, IsOpen W → x ∈ W → ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 b0,
      ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W)) :
    fib b0 ≠ 0 := by
  intro h0
  obtain ⟨φ, hφc, hφs, hφU, hφx, hφ0⟩ := exists_continuous_compactSupport_bump_of_isOpen hU hx
  obtain ⟨hsupp, hdis, hcont⟩ := h
  obtain ⟨hint, hgc⟩ := hcont φ hφc hφs hφU

  set W : Set V := {v | (1 / 2 : ℝ) < φ v} with hW
  have hWo : IsOpen W := isOpen_lt continuous_const hφc
  have hxW : x ∈ W := by
    show (1 / 2 : ℝ) < φ x
    rw [hφx]; norm_num
  have hWU : W ⊆ U := fun v hv =>
    hφU (subset_tsupport _ (by
      show φ v ≠ 0
      exact ne_of_gt (lt_trans (by norm_num) hv)))
  obtain ⟨c, hc0, hctop, N, hN, hlbN⟩ := hlb W hWo hxW
  set e : ℝ≥0∞ := ENNReal.ofReal (1 / 2) * c with he
  have he0 : e ≠ 0 := mul_ne_zero (by simp) hc0.ne'
  have hetop : e ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have hepos : 0 < e.toReal := ENNReal.toReal_pos he0 hetop
  set δ : ℝ := e.toReal / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδe : ENNReal.ofReal δ < e := by
    rw [← ENNReal.ofReal_toReal hetop, ENNReal.ofReal_lt_ofReal_iff hepos, hδ]
    linarith

  have hgcont : Continuous (fun b => ∫ v, φ v ∂(fib b)) := continuousOn_univ.mp hgc
  have hg0 : (∫ v, φ v ∂(fib b0)) = 0 := by simp [h0]
  have hnear : {b | (∫ v, φ v ∂(fib b)) < δ} ∈ 𝓝 b0 :=
    hgcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hg0]; exact hδpos))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hN hnear)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hK0 : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
  have hKtop : ν K ≠ ⊤ := hKc.measure_lt_top.ne

  set A : Set V := f' ⁻¹' K with hA
  have hAm : MeasurableSet A := (hKc.isClosed.preimage hf').measurableSet
  set Φ : V → ℝ≥0∞ := A.indicator (fun v => ENNReal.ofReal (φ v)) with hΦ
  have hΦm : Measurable Φ := (ENNReal.measurable_ofReal.comp hφc.measurable).indicator hAm
  have hinner : ∀ b, ∫⁻ v, Φ v ∂(fib b) =
      K.indicator (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) b := by
    intro b
    have hon : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U := ae_iff.mpr (hsupp b)
    have hae : ∀ᵐ v ∂(fib b), f' v = b := by
      filter_upwards [hon] with v hv
      apply hι
      rw [← hff']
      exact hv.1
    have hcongr : Φ =ᵐ[fib b] fun v => K.indicator (fun _ => ENNReal.ofReal (φ v)) b := by
      filter_upwards [hae] with v hv
      by_cases hb : b ∈ K
      · have hvA : v ∈ A := by rw [hA, Set.mem_preimage, hv]; exact hb
        rw [hΦ, Set.indicator_of_mem hvA, Set.indicator_of_mem hb]
      · have hvA : v ∉ A := by rw [hA, Set.mem_preimage, hv]; exact hb
        rw [hΦ, Set.indicator_of_notMem hvA, Set.indicator_of_notMem hb]
    rw [lintegral_congr_ae hcongr]
    by_cases hb : b ∈ K
    · simp only [Set.indicator_of_mem hb]
      exact (ofReal_integral_eq_lintegral_ofReal (hint b (Set.mem_univ b))
        (ae_of_all _ hφ0)).symm
    · simp [Set.indicator_of_notMem hb]
  have hupper : ∫⁻ v in U, Φ v ∂μ ≤ ENNReal.ofReal δ * ν K := by
    rw [hdis Φ hΦm]
    simp_rw [hinner]
    rw [lintegral_indicator hKm]
    calc ∫⁻ b in K, ENNReal.ofReal (∫ v, φ v ∂(fib b)) ∂ν
        ≤ ∫⁻ _ in K, ENNReal.ofReal δ ∂ν :=
          setLIntegral_mono measurable_const
            (fun b hb => ENNReal.ofReal_le_ofReal (hKsub hb).2.le)
      _ = ENNReal.ofReal δ * ν K := setLIntegral_const K _
  have hpre : f ⁻¹' (ι '' K) = A := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, hff', hA]
    constructor
    · rintro ⟨b, hb, hbv⟩
      rwa [← hι hbv]
    · intro hv
      exact ⟨_, hv, rfl⟩
  have hsub : A ∩ W ⊆ {v | ENNReal.ofReal (1 / 2) ≤ Φ v} ∩ U := by
    intro v hv
    refine ⟨?_, hWU hv.2⟩
    show ENNReal.ofReal (1 / 2) ≤ Φ v
    rw [hΦ, Set.indicator_of_mem hv.1]
    exact ENNReal.ofReal_le_ofReal hv.2.le
  have hlower : e * ν K ≤ ∫⁻ v in U, Φ v ∂μ := by
    calc e * ν K = ENNReal.ofReal (1 / 2) * (c * ν K) := by rw [he, mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 2) * μ (f ⁻¹' (ι '' K) ∩ W) :=
          mul_le_mul_of_nonneg_left (hlbN K (fun b hb => (hKsub hb).1) hKm) (by positivity)
      _ ≤ ENNReal.ofReal (1 / 2) * (μ.restrict U) {v | ENNReal.ofReal (1 / 2) ≤ Φ v} := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hpre]
          exact (measure_mono hsub).trans (Measure.le_restrict_apply _ _)
      _ ≤ ∫⁻ v in U, Φ v ∂μ := mul_meas_ge_le_lintegral hΦm _
  have hle := hlower.trans hupper
  rw [mul_comm e, mul_comm (ENNReal.ofReal δ)] at hle
  exact absurd hle (not_le.mpr (ENNReal.mul_lt_mul_right hK0.ne' hKtop hδe))

end Gen

section Tens

open PI.VolStabS PI.VolStabS.TensAllW

/- English proof (translation)
Establish `hopen : IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}` using `isOpen_linIndep (Module.finBasis F E) R hU hL`. Use `⟨fib_ne_zero_of_lb h hopen (f' := gramH R σ hσ J hJ) (continuous_gramH R σ hσ J hJ) (fun _ => rfl) Subtype.val_injective hx hlb, fun K hK hKU => ?_⟩` and prove the remaining obligations. Conclude with `PI.VolStabS.FibUniq.fin_cpt h hopen S K hK hKU`.
-/
theorem fib_tens {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (x : Fin a → Fin M → R ⊗[F] E) (S : HermR R σ a) (hx : LinearIndependent (R ⊗[F] E) x)
    (hlb : ∀ W : Set (Fin a → Fin M → R ⊗[F] E), IsOpen W → x ∈ W →
      ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ nhds S, ∀ T ⊆ N, MeasurableSet T →
        c * ν T ≤ μ ((gramR R σ J) ⁻¹' (Subtype.val '' T) ∩ W)) :
    fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin M → R ⊗[F] E), IsCompact K →
      K ⊆ {X | LinearIndependent (R ⊗[F] E) X} → fib S K < ⊤ := by
  have hopen : IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    isOpen_linIndep (Module.finBasis F E) R hU hL
  refine ⟨fib_ne_zero_of_lb h hopen (f' := gramH R σ hσ J hJ) (continuous_gramH R σ hσ J hJ)
    (fun _ => rfl) Subtype.val_injective hx hlb, fun K hK hKU => ?_⟩
  exact PI.VolStabS.FibUniq.fin_cpt h hopen S K hK hKU

end Tens

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib h x S hx hS`. Use `PI.VolStabS.secondCountable_Fv F v` as an intermediate fact. Use `PI.VolStabS.locallyCompact_Fv F v` as an intermediate fact. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Establish `hσ : ∀ y, σ (σ y) = y` using `PI.VolStabS.sigma_invol σ hCM.2.2.2`.

Conclude with `fib_tens σ hσ J hJ.1 a (Fv F v) (PI.VolStabS.isOpen_units_Fv F v) (PI.VolStabS.TensAllW.lip_field _) μ ν fib h x S hx (GlobalTheory.T.gramMap_preimage_volume_lower_bound F E σ hCM n J hJ v a μ ν hμ hν x S hx hS)`.
-/
theorem fibre_nonzero_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsCompact K → K ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} → fib S K < ⊤ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib h x S hx hS
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ y, σ (σ y) = y := PI.VolStabS.sigma_invol σ hCM.2.2.2
  exact fib_tens σ hσ J hJ.1 a (Fv F v) (PI.VolStabS.isOpen_units_Fv F v)
    (PI.VolStabS.TensAllW.lip_field _) μ ν fib h x S hx
    (GlobalTheory.T.gramMap_preimage_volume_lower_bound F E σ hCM n J hJ v a μ ν hμ hν x S hx hS)

end GlobalTheory.LocalFibreNonzero
