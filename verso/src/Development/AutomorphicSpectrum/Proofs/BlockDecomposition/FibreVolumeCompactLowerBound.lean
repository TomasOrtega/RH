import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramified
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibreMass

/- English proof (translation)
Introduce `V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ hfam _ _ P hPc hPo hPZ c hc s`. Take `⟨hconc, hdis, hcont⟩` from `hfam`. Establish `hPm : MeasurableSet P` using `hPo.measurableSet`. Establish `hφc : Continuous (P.indicator (fun _ => (1 : ℝ)))` using `IsClopen.continuous_indicator ⟨hPc.isClosed, hPo⟩ continuous_const`. Establish `hφs : HasCompactSupport (P.indicator (fun _ => (1 : ℝ)))` using `HasCompactSupport.intro hPc (fun x hx => by simp [hx])`.

Establish `hφt : tsupport (P.indicator (fun _ => (1 : ℝ))) ⊆ Z` using `(closure_minimal Set.support_indicator_subset hPc.isClosed).trans hPZ`. Take `⟨hint, hgc⟩` from `hcont _ hφc hφs hφt`. Establish `hfin : ∀ b, m b P < ∞`. Introduce `b`. Establish `h2 : IntegrableOn (fun _ => (1 : ℝ)) P (m b)` using `(integrable_indicator_iff hPm).1 (hint b (Set.mem_univ b))`.

Conclude with `((integrableOn_const_iff (by simp)).1 h2).resolve_left (by simp)`. Establish `hgeq : ∀ b, ∫ v, P.indicator (fun _ => (1 : ℝ)) v ∂(m b) = (m b P).toReal`. Introduce `b`. Rewrite using `[integral_indicator hPm, setIntegral_const]`. Simplify using `[Measure.real]`.

Establish `hgcont : Continuous (fun b => (m b P).toReal)`. Establish `h` using `continuousOn_univ.1 hgc`. Simplify `h` using `only [hgeq]`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`.

Establish `hcs : (c : ℝ) < (m s P).toReal`. Establish `h` using `(ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hfin s).ne).2 hlt`. Simplify using `using h`. Take `⟨d, hcd, hds⟩` from `exists_between hcs`. Take `⟨N, ⟨hsN, hNo⟩, hNfin⟩` from `(lam.finiteAt_nhds s).exists_mem_basis (nhds_basis_opens s)`.

Establish `hWo : IsOpen ({b | d < (m b P).toReal} ∩ N)` using `(isOpen_lt continuous_const hgcont).inter hNo`. Establish `hWm : MeasurableSet ({b | d < (m b P).toReal} ∩ N)` using `hWo.measurableSet`. Establish `hpos : lam ({b | d < (m b P).toReal} ∩ N) ≠ 0` using `(hWo.measure_pos lam ⟨s, hds, hsN⟩).ne'`. Establish `hfinW : lam ({b | d < (m b P).toReal} ∩ N) ≠ ∞` using `((measure_mono Set.inter_subset_right).trans_lt hNfin).ne`. Establish `hAm : MeasurableSet (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N))` using `hPm.inter (hQ.measurable hWm)`.

Establish `key : ∀ b, m b (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) = ({b | d < (m b P).toReal} ∩ N).indicator (fun b => m b P) b`. Introduce `b`. Establish `hcb` using `hconc b`. Rewrite using `[← measure_inter_conull hcb]`. Distinguish the cases in `hb : b ∈ ({b | d < (m b P).toReal} ∩ N)`.

Rewrite using `[Set.indicator_of_mem hb, ← measure_inter_conull (s := P) hcb]`. Use `congr 1`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hvP, _⟩, hvT⟩`.

Conclude with `⟨hvP, hvT⟩`. Introduce and unpack `⟨hvP, hvT⟩`. Use `⟨⟨hvP, ?_⟩, hvT⟩` and prove the remaining obligations. Establish `hQv : Q v = b` using `hvT.1`. Use `show Q v ∈ ({b | d < (m b P).toReal} ∩ N)`.

Rewrite using `[hQv]`. Conclude with `hb`. Rewrite using `[Set.indicator_of_notMem hb]`. Establish `hE : (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) ∩ (Q ⁻¹' {id b} ∩ Z) = ∅`. Use extensionality with `v`.

Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨⟨_, hvW⟩, hvT⟩`. Establish `hQv : Q v = b` using `hvT.1`. Apply `hb` to reduce the goal to its premises. Rewrite using `[← hQv]`.

Conclude with `hvW`. Rewrite using `[hE, measure_empty]`. Establish `hlhs : ∫⁻ v in Z, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂μ = μ (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N))`. Rewrite using `[lintegral_indicator_one hAm, Measure.restrict_apply hAm, Set.inter_eq_left.2 (Set.inter_subset_left.trans hPZ)]`. Establish `hrhs : ∫⁻ b, ∫⁻ v, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂(m b) ∂lam = ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam`.

Repeatedly rewrite using `[lintegral_indicator_one hAm, key]`. Rewrite using `[lintegral_indicator hWm]`. Establish `hmain : ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam ≤ (c : ℝ≥0∞) * lam ({b | d < (m b P).toReal} ∩ N)`. Rewrite using `[← hrhs, ← hdis _ (measurable_one.indicator hAm), hlhs]`. Conclude with `hc _ hWm`.

Establish `hlow : ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N) ≤ ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam`. Combine the equalities or inequalities in the displayed calculation. Establish `hd0 : 0 ≤ d` using `(NNReal.coe_nonneg c).trans hcd.le`. Establish `h` using `ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinW) (hlow.trans hmain)`. Rewrite `h` using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd0, ENNReal.coe_toReal]`.

Establish `hLpos : 0 < (lam ({b | d < (m b P).toReal} ∩ N)).toReal` using `ENNReal.toReal_pos hpos hfinW`. Establish `h' : d ≤ (c : ℝ)` using `le_of_mul_le_mul_right h hLpos`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fibre_mass_le_of_pushforward : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ [lam.IsOpenPosMeasure] [IsLocallyFiniteMeasure lam] (P : Set V), IsCompact P → IsOpen P → P ⊆ Z → ∀ c : ℝ≥0, (∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ s, m s P ≤ (c : ℝ≥0∞) := by
  intro V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ hfam _ _ P hPc hPo hPZ c hc s
  classical
  obtain ⟨hconc, hdis, hcont⟩ := hfam
  have hPm : MeasurableSet P := hPo.measurableSet
  have hφc : Continuous (P.indicator (fun _ => (1 : ℝ))) :=
    IsClopen.continuous_indicator ⟨hPc.isClosed, hPo⟩ continuous_const
  have hφs : HasCompactSupport (P.indicator (fun _ => (1 : ℝ))) :=
    HasCompactSupport.intro hPc (fun x hx => by simp [hx])
  have hφt : tsupport (P.indicator (fun _ => (1 : ℝ))) ⊆ Z :=
    (closure_minimal Set.support_indicator_subset hPc.isClosed).trans hPZ
  obtain ⟨hint, hgc⟩ := hcont _ hφc hφs hφt
  have hfin : ∀ b, m b P < ∞ := by
    intro b
    have h2 : IntegrableOn (fun _ => (1 : ℝ)) P (m b) :=
      (integrable_indicator_iff hPm).1 (hint b (Set.mem_univ b))
    exact ((integrableOn_const_iff (by simp)).1 h2).resolve_left (by simp)
  have hgeq : ∀ b, ∫ v, P.indicator (fun _ => (1 : ℝ)) v ∂(m b) = (m b P).toReal := by
    intro b
    rw [integral_indicator hPm, setIntegral_const]
    simp [Measure.real]
  have hgcont : Continuous (fun b => (m b P).toReal) := by
    have h := continuousOn_univ.1 hgc
    simpa only [hgeq] using h
  by_contra hlt
  rw [not_le] at hlt
  have hcs : (c : ℝ) < (m s P).toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hfin s).ne).2 hlt
    simpa using h
  obtain ⟨d, hcd, hds⟩ := exists_between hcs
  obtain ⟨N, ⟨hsN, hNo⟩, hNfin⟩ := (lam.finiteAt_nhds s).exists_mem_basis (nhds_basis_opens s)
  have hWo : IsOpen ({b | d < (m b P).toReal} ∩ N) :=
    (isOpen_lt continuous_const hgcont).inter hNo
  have hWm : MeasurableSet ({b | d < (m b P).toReal} ∩ N) := hWo.measurableSet
  have hpos : lam ({b | d < (m b P).toReal} ∩ N) ≠ 0 :=
    (hWo.measure_pos lam ⟨s, hds, hsN⟩).ne'
  have hfinW : lam ({b | d < (m b P).toReal} ∩ N) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt hNfin).ne
  have hAm : MeasurableSet (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) :=
    hPm.inter (hQ.measurable hWm)
  have key : ∀ b, m b (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) =
      ({b | d < (m b P).toReal} ∩ N).indicator (fun b => m b P) b := by
    intro b
    have hcb := hconc b
    rw [← measure_inter_conull hcb]
    by_cases hb : b ∈ ({b | d < (m b P).toReal} ∩ N)
    · rw [Set.indicator_of_mem hb, ← measure_inter_conull (s := P) hcb]
      congr 1
      ext v
      constructor
      · rintro ⟨⟨hvP, _⟩, hvT⟩
        exact ⟨hvP, hvT⟩
      · rintro ⟨hvP, hvT⟩
        refine ⟨⟨hvP, ?_⟩, hvT⟩
        have hQv : Q v = b := hvT.1
        show Q v ∈ ({b | d < (m b P).toReal} ∩ N)
        rw [hQv]
        exact hb
    · rw [Set.indicator_of_notMem hb]
      have hE : (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) ∩ (Q ⁻¹' {id b} ∩ Z) = ∅ := by
        ext v
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hvW⟩, hvT⟩
        have hQv : Q v = b := hvT.1
        apply hb
        rw [← hQv]
        exact hvW
      rw [hE, measure_empty]
  have hlhs : ∫⁻ v in Z, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂μ =
      μ (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)) := by
    rw [lintegral_indicator_one hAm, Measure.restrict_apply hAm,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hPZ)]
  have hrhs : ∫⁻ b, ∫⁻ v, (P ∩ Q ⁻¹' ({b | d < (m b P).toReal} ∩ N)).indicator 1 v ∂(m b) ∂lam =
      ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam := by
    simp_rw [lintegral_indicator_one hAm, key]
    rw [lintegral_indicator hWm]
  have hmain : ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam ≤
      (c : ℝ≥0∞) * lam ({b | d < (m b P).toReal} ∩ N) := by
    rw [← hrhs, ← hdis _ (measurable_one.indicator hAm), hlhs]
    exact hc _ hWm
  have hlow : ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N) ≤
      ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam := by
    calc ENNReal.ofReal d * lam ({b | d < (m b P).toReal} ∩ N)
        = ∫⁻ _ in ({b | d < (m b P).toReal} ∩ N), ENNReal.ofReal d ∂lam :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ b in ({b | d < (m b P).toReal} ∩ N), m b P ∂lam :=
          setLIntegral_mono' hWm (fun b hb => ENNReal.ofReal_le_of_le_toReal hb.1.le)
  have hd0 : 0 ≤ d := (NNReal.coe_nonneg c).trans hcd.le
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinW) (hlow.trans hmain)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd0, ENNReal.coe_toReal] at h
  have hLpos : 0 < (lam ({b | d < (m b P).toReal} ∩ N)).toReal := ENNReal.toReal_pos hpos hfinW
  have h' : d ≤ (c : ℝ) := le_of_mul_le_mul_right h hLpos
  linarith

end GlobalTheory.CompanionTheory.WeilSiegel.FibreMass
