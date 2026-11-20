import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open MeasureTheory Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.FibreDensityLimit

open Set

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hFc : Continuous fun s => ENNReal.ofReal (a s)` using `ENNReal.continuous_ofReal.comp ha`. Establish `hGc : Continuous fun s => ENNReal.ofReal (b s) + ENNReal.ofReal c` using `(ENNReal.continuous_ofReal.comp hb).add continuous_const`. Establish `hopen : IsOpen {s | ENNReal.ofReal (b s) + ENNReal.ofReal c < ENNReal.ofReal (a s)}` using `isOpen_lt hGc hFc`.

Take `⟨A, hAn, hAW, hAc⟩` from `local_compact_nhds (hopen.mem_nhds hlt)`. Establish `hAm : MeasurableSet A` using `hAc.measurableSet`. Establish `hpos : ν A ≠ 0` using `(MeasureTheory.Measure.measure_pos_of_mem_nhds ν hAn).ne'`. Establish `hsplit : ∫⁻ s in A, (ENNReal.ofReal (b s) + ENNReal.ofReal c) ∂ν = ∫⁻ s in A, ENNReal.ofReal (b s) ∂ν + ENNReal.ofReal c * ν A`. Rewrite using `[lintegral_add_right _ measurable_const, setLIntegral_const]`.

Establish `hfin : ∫⁻ s in A, (ENNReal.ofReal (b s) + ENNReal.ofReal c) ∂ν ≠ ∞`. Establish `hbi : IntegrableOn b A ν` using `hb.continuousOn.integrableOn_compact hAc`. Rewrite using `[hsplit]`. Conclude with `ENNReal.add_ne_top.mpr ⟨hbi.lintegral_lt_top.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAc.measure_lt_top.ne⟩`. Establish `hstrict` using `setLIntegral_strict_mono hAm hpos hFc.measurable hfin (Filter.Eventually.of_forall fun s hs => hAW hs)`.

Rewrite `hstrict` using `[hsplit]`. Conclude with `absurd (h A hAc) (not_le.mpr hstrict)`.
-/
theorem ofReal_le_of_forall_compact {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) (c : ℝ)
    (h : ∀ A : Set X, IsCompact A → ∫⁻ s in A, ENNReal.ofReal (a s) ∂ν ≤
      ∫⁻ s in A, ENNReal.ofReal (b s) ∂ν + ENNReal.ofReal c * ν A) (s₀ : X) :
    ENNReal.ofReal (a s₀) ≤ ENNReal.ofReal (b s₀) + ENNReal.ofReal c := by
  by_contra hlt
  rw [not_le] at hlt
  have hFc : Continuous fun s => ENNReal.ofReal (a s) := ENNReal.continuous_ofReal.comp ha
  have hGc : Continuous fun s => ENNReal.ofReal (b s) + ENNReal.ofReal c :=
    (ENNReal.continuous_ofReal.comp hb).add continuous_const
  have hopen : IsOpen {s | ENNReal.ofReal (b s) + ENNReal.ofReal c < ENNReal.ofReal (a s)} :=
    isOpen_lt hGc hFc
  obtain ⟨A, hAn, hAW, hAc⟩ := local_compact_nhds (hopen.mem_nhds hlt)
  have hAm : MeasurableSet A := hAc.measurableSet
  have hpos : ν A ≠ 0 := (MeasureTheory.Measure.measure_pos_of_mem_nhds ν hAn).ne'
  have hsplit : ∫⁻ s in A, (ENNReal.ofReal (b s) + ENNReal.ofReal c) ∂ν =
      ∫⁻ s in A, ENNReal.ofReal (b s) ∂ν + ENNReal.ofReal c * ν A := by
    rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  have hfin : ∫⁻ s in A, (ENNReal.ofReal (b s) + ENNReal.ofReal c) ∂ν ≠ ∞ := by
    have hbi : IntegrableOn b A ν := hb.continuousOn.integrableOn_compact hAc
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨hbi.lintegral_lt_top.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAc.measure_lt_top.ne⟩
  have hstrict := setLIntegral_strict_mono hAm hpos hFc.measurable hfin
    (Filter.Eventually.of_forall fun s hs => hAW hs)
  rw [hsplit] at hstrict
  exact absurd (h A hAc) (not_le.mpr hstrict)

/- English proof (translation)
Take `⟨L, -, hLc, hKL, hLU⟩` from `exists_compact_closed_between hK hU hKU`. Take `⟨φ, hφ1, hφ0, hφs, hφb⟩` from `exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)`. Use `⟨φ, φ.continuous, hφs, ?_, fun v => hφb v, fun v hv => hφ1 hv⟩` and prove the remaining obligations. Use `(closure_minimal ?_ hLc).trans hLU` and prove the remaining obligations. Introduce `v hv`.

Assume the negation of the conclusion as `hvL`. Conclude with `hv (hφ0 (fun hi => hvL (interior_subset hi)))`.
-/
private lemma exists_continuous_compactSupport_eq_one_on_compact {V : Type} [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : V → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
      (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) ∧ ∀ v ∈ K, ψ v = 1 := by
  obtain ⟨L, -, hLc, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨φ, hφ1, hφ0, hφs, hφb⟩ := exists_continuous_one_zero_of_isCompact hK
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  refine ⟨φ, φ.continuous, hφs, ?_, fun v => hφb v, fun v hv => hφ1 hv⟩
  refine (closure_minimal ?_ hLc).trans hLU
  intro v hv
  by_contra hvL
  exact hv (hφ0 (fun hi => hvL (interior_subset hi)))

/- English proof (translation)
Establish `: LocallyCompactSpace U` using `hU.locallyCompactSpace`. Set `Kn : ℕ → Set V` to `fun n => Subtype.val '' compactCovering U n`. Establish `hKc : ∀ n, IsCompact (Kn n)` using `fun n => (isCompact_compactCovering U n).image continuous_subtype_val`. Establish `hKU : ∀ n, Kn n ⊆ U`. Introduce and unpack `n _ ⟨x, -, rfl⟩`.

Conclude with `x.2`. Establish `hcov : ∀ v ∈ U, ∃ n, v ∈ Kn n`. Introduce `v hv`. Establish `hmem : (⟨v, hv⟩ : U) ∈ ⋃ n, compactCovering U n`. Rewrite using `[iUnion_compactCovering]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨n, hn⟩` from `Set.mem_iUnion.mp hmem`. Conclude with `⟨n, ⟨v, hv⟩, hn, rfl⟩`. Use `choose ψ hψc hψs hψU hψb hψ1 using fun n => exists_continuous_compactSupport_eq_one_on_compact (hKc n) hU (hKU n)`. Establish `hsup : ∀ a b : V → ℝ, HasCompactSupport a → HasCompactSupport b → tsupport (a ⊔ b) ⊆ tsupport a ∪ tsupport b`.

Introduce `a b _ _`. Use `closure_minimal ?_ ((isClosed_tsupport a).union (isClosed_tsupport b))` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, not_or] at hc`.

Apply `hv` to reduce the goal to its premises. Simplify using `[image_eq_zero_of_notMem_tsupport hc.1, image_eq_zero_of_notMem_tsupport hc.2]`. Establish `hP : ∀ n, Continuous (partialSups ψ n) ∧ HasCompactSupport (partialSups ψ n) ∧ tsupport (partialSups ψ n) ⊆ U ∧ ∀ v, 0 ≤ partialSups ψ n v ∧ partialSups ψ n v ≤ 1`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Rewrite using `[partialSups_zero]`. Conclude with `⟨hψc 0, hψs 0, hψU 0, hψb 0⟩`. Consider the case `succ n ih`. Take `⟨h1, h2, h3, h4⟩` from `ih`.

Establish `hs : partialSups ψ (n + 1) = partialSups ψ n ⊔ ψ (n + 1)` using `partialSups_succ ψ n`. Rewrite using `[hs]`. Use `⟨h1.sup (hψc (n + 1)), ?_, ?_, fun v => ?_⟩` and prove the remaining obligations. Conclude with `(h2.union (hψs (n + 1))).of_isClosed_subset (isClosed_tsupport _) (hsup _ _ h2 (hψs (n + 1)))`. Conclude with `(hsup _ _ h2 (hψs (n + 1))).trans (Set.union_subset h3 (hψU (n + 1)))`.

Conclude with `⟨le_sup_of_le_left (h4 v).1, sup_le (h4 v).2 (hψb (n + 1) v).2⟩`. Use `⟨fun n => partialSups ψ n, fun n => (hP n).1, fun n => (hP n).2.1, fun n => (hP n).2.2.1, fun n => (hP n).2.2.2, fun v m n hmn => (partialSups ψ).monotone hmn v, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hcov v hv`. Use `⟨n, le_antisymm ((hP n).2.2.2 v).2 ?_⟩` and prove the remaining obligations. Rewrite using `[← hψ1 n v hn]`.

Conclude with `le_partialSups ψ n v`.
-/
theorem exists_cutoffs {V : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] {U : Set V} (hU : IsOpen U) :
    ∃ χ : ℕ → V → ℝ, (∀ n, Continuous (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n, tsupport (χ n) ⊆ U) ∧ (∀ n v, 0 ≤ χ n v ∧ χ n v ≤ 1) ∧
      (∀ v, Monotone fun n => χ n v) ∧ ∀ v ∈ U, ∃ n, χ n v = 1 := by
  classical
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let Kn : ℕ → Set V := fun n => Subtype.val '' compactCovering U n
  have hKc : ∀ n, IsCompact (Kn n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n, Kn n ⊆ U := by
    rintro n _ ⟨x, -, rfl⟩
    exact x.2
  have hcov : ∀ v ∈ U, ∃ n, v ∈ Kn n := by
    intro v hv
    have hmem : (⟨v, hv⟩ : U) ∈ ⋃ n, compactCovering U n := by
      rw [iUnion_compactCovering]
      trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact ⟨n, ⟨v, hv⟩, hn, rfl⟩
  choose ψ hψc hψs hψU hψb hψ1 using fun n => exists_continuous_compactSupport_eq_one_on_compact (hKc n) hU (hKU n)
  have hsup : ∀ a b : V → ℝ, HasCompactSupport a → HasCompactSupport b →
      tsupport (a ⊔ b) ⊆ tsupport a ∪ tsupport b := by
    intro a b _ _
    refine closure_minimal ?_ ((isClosed_tsupport a).union (isClosed_tsupport b))
    intro v hv
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    apply hv
    simp [image_eq_zero_of_notMem_tsupport hc.1, image_eq_zero_of_notMem_tsupport hc.2]
  have hP : ∀ n, Continuous (partialSups ψ n) ∧ HasCompactSupport (partialSups ψ n) ∧
      tsupport (partialSups ψ n) ⊆ U ∧ ∀ v, 0 ≤ partialSups ψ n v ∧ partialSups ψ n v ≤ 1 := by
    intro n
    induction n with
    | zero =>
      rw [partialSups_zero]
      exact ⟨hψc 0, hψs 0, hψU 0, hψb 0⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hs : partialSups ψ (n + 1) = partialSups ψ n ⊔ ψ (n + 1) := partialSups_succ ψ n
      rw [hs]
      refine ⟨h1.sup (hψc (n + 1)), ?_, ?_, fun v => ?_⟩
      · exact (h2.union (hψs (n + 1))).of_isClosed_subset (isClosed_tsupport _)
          (hsup _ _ h2 (hψs (n + 1)))
      · exact (hsup _ _ h2 (hψs (n + 1))).trans (Set.union_subset h3 (hψU (n + 1)))
      · exact ⟨le_sup_of_le_left (h4 v).1, sup_le (h4 v).2 (hψb (n + 1) v).2⟩
  refine ⟨fun n => partialSups ψ n, fun n => (hP n).1, fun n => (hP n).2.1, fun n => (hP n).2.2.1,
    fun n => (hP n).2.2.2, fun v m n hmn => (partialSups ψ).monotone hmn v, fun v hv => ?_⟩
  obtain ⟨n, hn⟩ := hcov v hv
  refine ⟨n, le_antisymm ((hP n).2.2.2 v).2 ?_⟩
  rw [← hψ1 n v hn]
  exact le_partialSups ψ n v

section Family

variable {V X Y : Type} [MeasurableSpace V] [TopologicalSpace V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {U : Set V} {fib : X → Measure V}

/- English proof (translation)
Establish `hpre : f ⁻¹' (ι '' A) = g ⁻¹' A`. Use extensionality with `v`. Simplify using `only [Set.mem_preimage, Set.mem_image, hfg]`. Conclude with `⟨fun ⟨x, hx, he⟩ => hι he ▸ hx, fun hv => ⟨g v, hv, rfl⟩⟩`. Rewrite using `[hpre]`.

Establish `hgA : MeasurableSet (g ⁻¹' A)` using `hg hA`. Rewrite using `[← lintegral_indicator hgA, ← lintegral_indicator hA]`. Establish `hsupp : Function.support ((g ⁻¹' A).indicator w) ⊆ U`. Introduce `v hv`. Assume the negation of the conclusion as `hU`.

Apply `hv` to reduce the goal to its premises. Simplify using `[Set.indicator, hw0 v hU]`. Rewrite using `[← setLIntegral_eq_of_support_subset hsupp, h.2.1 _ (hw.indicator hgA)]`. Use `lintegral_congr fun s => ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ v ∂(fib s), v ∈ f ⁻¹' {ι s} ∩ U` using `(MeasureTheory.mem_ae_iff).mpr (h.1 s)`.

Distinguish the cases in `hs : s ∈ A`. Rewrite using `[Set.indicator_of_mem hs]`. Use `lintegral_congr_ae (hae.mono fun v hv => ?_)` and prove the remaining obligations. Establish `hgv : g v = s` using `hι (by rw [← hfg]; exact hv.1)`. Rewrite using `[Set.indicator_of_mem (show v ∈ g ⁻¹' A by rw [Set.mem_preimage, hgv]; exact hs)]`.

Rewrite using `[Set.indicator_of_notMem hs]`. Use `(lintegral_congr_ae (hae.mono fun v hv => ?_)).trans lintegral_zero` and prove the remaining obligations. Establish `hgv : g v = s` using `hι (by rw [← hfg]; exact hv.1)`. Rewrite using `[Set.indicator_of_notMem (show v ∉ g ⁻¹' A by rw [Set.mem_preimage, hgv]; exact hs)]`.
-/
theorem lintegral_slice (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hg : Measurable g) (hfg : ∀ v, f v = ι (g v)) {w : V → ℝ≥0∞}
    (hw : Measurable w) (hw0 : ∀ v, v ∉ U → w v = 0) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ v in f ⁻¹' (ι '' A), w v ∂μ = ∫⁻ s in A, ∫⁻ v, w v ∂(fib s) ∂ν := by
  have hpre : f ⁻¹' (ι '' A) = g ⁻¹' A := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, hfg]
    exact ⟨fun ⟨x, hx, he⟩ => hι he ▸ hx, fun hv => ⟨g v, hv, rfl⟩⟩
  rw [hpre]
  have hgA : MeasurableSet (g ⁻¹' A) := hg hA
  rw [← lintegral_indicator hgA, ← lintegral_indicator hA]
  have hsupp : Function.support ((g ⁻¹' A).indicator w) ⊆ U := by
    intro v hv
    by_contra hU
    apply hv
    simp [Set.indicator, hw0 v hU]
  rw [← setLIntegral_eq_of_support_subset hsupp, h.2.1 _ (hw.indicator hgA)]
  refine lintegral_congr fun s => ?_
  have hae : ∀ᵐ v ∂(fib s), v ∈ f ⁻¹' {ι s} ∩ U := (MeasureTheory.mem_ae_iff).mpr (h.1 s)
  by_cases hs : s ∈ A
  · rw [Set.indicator_of_mem hs]
    refine lintegral_congr_ae (hae.mono fun v hv => ?_)
    have hgv : g v = s := hι (by rw [← hfg]; exact hv.1)
    rw [Set.indicator_of_mem (show v ∈ g ⁻¹' A by rw [Set.mem_preimage, hgv]; exact hs)]
  · rw [Set.indicator_of_notMem hs]
    refine (lintegral_congr_ae (hae.mono fun v hv => ?_)).trans lintegral_zero
    have hgv : g v = s := hι (by rw [← hfg]; exact hv.1)
    rw [Set.indicator_of_notMem (show v ∉ g ⁻¹' A by rw [Set.mem_preimage, hgv]; exact hs)]

/- English proof (translation)
Establish `hw0 : ∀ v, v ∉ U → ENNReal.ofReal (ψ v) = 0`. Introduce `v hv`. Rewrite using `[image_eq_zero_of_notMem_tsupport (fun h' => hv (hψU h')), ENNReal.ofReal_zero]`. Rewrite using `[lintegral_slice (w := fun v => ENNReal.ofReal (ψ v)) h hUm hι hg hfg (ENNReal.measurable_ofReal.comp hψ.measurable) hw0 hA]`. Use `lintegral_congr fun s => ?_` and prove the remaining obligations.

Rewrite using `[ofReal_integral_eq_lintegral_ofReal ((h.2.2 ψ hψ hψc hψU).1 s (Set.mem_univ s)) (Filter.Eventually.of_forall hψ0)]`.
-/
theorem lintegral_slice_test (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib)
    [BorelSpace V] (hUm : MeasurableSet U)
    (hι : Function.Injective ι) (hg : Measurable g) (hfg : ∀ v, f v = ι (g v)) {ψ : V → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ v, 0 ≤ ψ v)
    {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v) ∂μ =
      ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v ∂(fib s)) ∂ν := by
  have hw0 : ∀ v, v ∉ U → ENNReal.ofReal (ψ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport (fun h' => hv (hψU h')), ENNReal.ofReal_zero]
  rw [lintegral_slice (w := fun v => ENNReal.ofReal (ψ v)) h hUm hι hg hfg
    (ENNReal.measurable_ofReal.comp hψ.measurable) hw0 hA]
  refine lintegral_congr fun s => ?_
  rw [ofReal_integral_eq_lintegral_ofReal ((h.2.2 ψ hψ hψc hψU).1 s (Set.mem_univ s))
    (Filter.Eventually.of_forall hψ0)]

end Family

/- English proof (translation)
Introduce `V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ f g ι hι hgc hfg U fib hUo h φ hφ hφ0 D hD hDA hK s0`. Establish `hg : Measurable g` using `hgc.measurable`. Establish `hUm : MeasurableSet U` using `hUo.measurableSet`. Establish `htest : ∀ ψ : V → ℝ, Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U → (∀ v, 0 ≤ ψ v) → (∀ v, ψ v ≤ φ v) → ENNReal.ofReal (∫ v, ψ v ∂(fib s0)) ≤ ENNReal.ofReal (D s0)`. Introduce `ψ hψ hψc hψU hψ0 hψφ`.

Establish `hcont : Continuous fun s => ∫ v, ψ v ∂(fib s)` using `continuousOn_univ.mp (h.2.2 ψ hψ hψc hψU).2`. Establish `hcmp : ∀ A : Set X, IsCompact A → ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v ∂(fib s)) ∂ν ≤ ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν + ENNReal.ofReal 0 * ν A`. Introduce `A hA`. Rewrite using `[ENNReal.ofReal_zero, zero_mul, add_zero, ← lintegral_slice_test h hUm hι hg hfg hψ hψc hψU hψ0 hA.measurableSet, ← hDA A hA.measurableSet]`. Conclude with `lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hψφ v)`.

Simplify using `using ofReal_le_of_forall_compact ν hcont hD 0 hcmp s0`. Establish `hae : ∀ᵐ v ∂(fib s0), v ∈ f ⁻¹' {ι s0} ∩ U` using `(MeasureTheory.mem_ae_iff).mpr (h.1 s0)`. Establish `hint : ∀ θ : V → ℝ, Continuous θ → HasCompactSupport θ → tsupport θ ⊆ U → (∀ v, 0 ≤ θ v) → ENNReal.ofReal (∫ v, θ v ∂(fib s0)) = ∫⁻ v, ENNReal.ofReal (θ v) ∂(fib s0)` using `fun θ hθ hθc hθU hθ0 => ofReal_integral_eq_lintegral_ofReal ((h.2.2 θ hθ hθc hθU).1 s0 (Set.mem_univ _)) (Filter.Eventually.of_forall hθ0)`. Take `⟨χ, hχc, hχs, hχU, hχb, hχm, hχ1⟩` from `exists_cutoffs hUo`. Establish `hψn : ∀ n, ∫⁻ v, ENNReal.ofReal (χ n v * φ v) ∂(fib s0) ≤ ENNReal.ofReal (D s0)`.

Introduce `n`. Establish `hc : Continuous fun v => χ n v * φ v` using `(hχc n).mul hφ`. Establish `hs : HasCompactSupport fun v => χ n v * φ v` using `(hχs n).mul_right`. Establish `hsU : tsupport (fun v => χ n v * φ v) ⊆ U` using `tsupport_mul_subset_left.trans (hχU n)`. Establish `h0 : ∀ v, 0 ≤ χ n v * φ v` using `fun v => mul_nonneg (hχb n v).1 (hφ0 v)`.

Rewrite using `[← hint _ hc hs hsU h0]`. Conclude with `htest _ hc hs hsU h0 fun v => mul_le_of_le_one_left (hφ0 v) (hχb n v).2`. Establish `hX : ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s0) ≤ ENNReal.ofReal (D s0)`. Establish `heq : ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s0) = ∫⁻ v, ⨆ n, ENNReal.ofReal (χ n v * φ v) ∂(fib s0)`. Use `lintegral_congr_ae (hae.mono fun v hv => ?_)` and prove the remaining obligations.

Take `⟨n, hn⟩` from `hχ1 v hv.2`. Use `le_antisymm (le_iSup_of_le n (by rw [hn, one_mul])) (iSup_le fun m => ?_)` and prove the remaining obligations. Conclude with `ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hφ0 v) (hχb m v).2)`. Rewrite using `[heq, lintegral_iSup (f := fun n v => ENNReal.ofReal (χ n v * φ v)) (fun n => ENNReal.measurable_ofReal.comp ((hχc n).mul hφ).measurable) (fun m n hmn v => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hχm v hmn) (hφ0 v)))]`. Conclude with `iSup_le hψn`.

Use `le_antisymm hX (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)` and prove the remaining obligations. Take `⟨K, hKc, hKU, hKε⟩` from `hK ε (NNReal.coe_pos.mpr hε)`. Take `⟨L, -, hLc, hKL, hLU⟩` from `exists_compact_closed_between hKc hUo hKU`. Take `⟨ψ, hψ1, hψ0', hψs, hψb⟩` from `exists_continuous_one_zero_of_isCompact hKc isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)`. Establish `hψU : tsupport ψ ⊆ U`.

Use `(closure_minimal ?_ hLc).trans hLU` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hvL`. Conclude with `hv (hψ0' (fun hi => hvL (interior_subset hi)))`. Establish `hc : Continuous fun v => ψ v * φ v` using `ψ.continuous.mul hφ`.

Establish `hs : HasCompactSupport fun v => ψ v * φ v` using `hψs.mul_right`. Establish `hsU : tsupport (fun v => ψ v * φ v) ⊆ U` using `tsupport_mul_subset_left.trans hψU`. Establish `h0 : ∀ v, 0 ≤ ψ v * φ v` using `fun v => mul_nonneg (hψb v).1 (hφ0 v)`. Establish `hcont : Continuous fun s => ∫ v, ψ v * φ v ∂(fib s)` using `continuousOn_univ.mp (h.2.2 _ hc hs hsU).2`. Establish `hcmp : ∀ A : Set X, IsCompact A → ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν ≤ ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v * φ v ∂(fib s)) ∂ν + ENNReal.ofReal ε * ν A`.

Introduce `A hA`. Establish `hAm` using `hA.measurableSet`. Rewrite using `[← hDA A hAm, ← lintegral_slice_test h hUm hι hg hfg hc hs hsU h0 hAm]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun v => ?_` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ K`. Rewrite using `[Set.indicator_of_notMem (show v ∉ Kᶜ from fun h' => h' hv), add_zero, hψ1 hv, Pi.one_apply, one_mul]`. Rewrite using `[Set.indicator_of_mem hv]`. Conclude with `le_add_self`. Use `_ = ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v * φ v) ∂μ + ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ := by`.

Rewrite using `[lintegral_add_left (f := fun v => ENNReal.ofReal (ψ v * φ v)) (ENNReal.measurable_ofReal.comp hc.measurable), setLIntegral_indicator hKc.measurableSet.compl, Set.inter_comm]`. Use `_ ≤ ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v * φ v) ∂μ + ENNReal.ofReal ε * ν A := by gcongr`. Conclude with `hKε A hAm`. Establish `hmain` using `ofReal_le_of_forall_compact ν hD hcont ε hcmp s0`. Rewrite `hmain` using `[hint _ hc hs hsU h0, ENNReal.ofReal_coe_nnreal]`.

Use `hmain.trans (add_le_add ?_ le_rfl)` and prove the remaining obligations. Conclude with `lintegral_mono fun v => ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hφ0 v) (hψb v).2)`.
-/
theorem fibre_lintegral_eq_density : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U : Set V) (fib : X → Measure V), IsOpen U → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ φ : V → ℝ, Continuous φ → (∀ v, 0 ≤ φ v) → ∀ D : X → ℝ, Continuous D → (∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ = ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν) → (∀ ε : ℝ, 0 < ε → ∃ K : Set V, IsCompact K ∧ K ⊆ U ∧ ∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ ≤ ENNReal.ofReal ε * ν A) → ∀ s₀ : X, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s₀) = ENNReal.ofReal (D s₀) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ f g ι hι hgc hfg U fib hUo h φ hφ hφ0 D hD hDA hK s0
  have hg : Measurable g := hgc.measurable
  have hUm : MeasurableSet U := hUo.measurableSet
  have htest : ∀ ψ : V → ℝ, Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∀ v, 0 ≤ ψ v) → (∀ v, ψ v ≤ φ v) →
      ENNReal.ofReal (∫ v, ψ v ∂(fib s0)) ≤ ENNReal.ofReal (D s0) := by
    intro ψ hψ hψc hψU hψ0 hψφ
    have hcont : Continuous fun s => ∫ v, ψ v ∂(fib s) :=
      continuousOn_univ.mp (h.2.2 ψ hψ hψc hψU).2
    have hcmp : ∀ A : Set X, IsCompact A →
        ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v ∂(fib s)) ∂ν ≤
          ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν + ENNReal.ofReal 0 * ν A := by
      intro A hA
      rw [ENNReal.ofReal_zero, zero_mul, add_zero,
        ← lintegral_slice_test h hUm hι hg hfg hψ hψc hψU hψ0 hA.measurableSet,
        ← hDA A hA.measurableSet]
      exact lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hψφ v)
    simpa using ofReal_le_of_forall_compact ν hcont hD 0 hcmp s0
  have hae : ∀ᵐ v ∂(fib s0), v ∈ f ⁻¹' {ι s0} ∩ U := (MeasureTheory.mem_ae_iff).mpr (h.1 s0)
  have hint : ∀ θ : V → ℝ, Continuous θ → HasCompactSupport θ → tsupport θ ⊆ U → (∀ v, 0 ≤ θ v) →
      ENNReal.ofReal (∫ v, θ v ∂(fib s0)) = ∫⁻ v, ENNReal.ofReal (θ v) ∂(fib s0) :=
    fun θ hθ hθc hθU hθ0 => ofReal_integral_eq_lintegral_ofReal
      ((h.2.2 θ hθ hθc hθU).1 s0 (Set.mem_univ _)) (Filter.Eventually.of_forall hθ0)
  obtain ⟨χ, hχc, hχs, hχU, hχb, hχm, hχ1⟩ := exists_cutoffs hUo
  have hψn : ∀ n, ∫⁻ v, ENNReal.ofReal (χ n v * φ v) ∂(fib s0) ≤ ENNReal.ofReal (D s0) := by
    intro n
    have hc : Continuous fun v => χ n v * φ v := (hχc n).mul hφ
    have hs : HasCompactSupport fun v => χ n v * φ v := (hχs n).mul_right
    have hsU : tsupport (fun v => χ n v * φ v) ⊆ U := tsupport_mul_subset_left.trans (hχU n)
    have h0 : ∀ v, 0 ≤ χ n v * φ v := fun v => mul_nonneg (hχb n v).1 (hφ0 v)
    rw [← hint _ hc hs hsU h0]
    exact htest _ hc hs hsU h0 fun v => mul_le_of_le_one_left (hφ0 v) (hχb n v).2
  have hX : ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s0) ≤ ENNReal.ofReal (D s0) := by
    have heq : ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s0) =
        ∫⁻ v, ⨆ n, ENNReal.ofReal (χ n v * φ v) ∂(fib s0) := by
      refine lintegral_congr_ae (hae.mono fun v hv => ?_)
      obtain ⟨n, hn⟩ := hχ1 v hv.2
      refine le_antisymm (le_iSup_of_le n (by rw [hn, one_mul])) (iSup_le fun m => ?_)
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hφ0 v) (hχb m v).2)
    rw [heq, lintegral_iSup (f := fun n v => ENNReal.ofReal (χ n v * φ v)) (fun n => ENNReal.measurable_ofReal.comp ((hχc n).mul hφ).measurable)
      (fun m n hmn v => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hχm v hmn) (hφ0 v)))]
    exact iSup_le hψn
  refine le_antisymm hX (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  obtain ⟨K, hKc, hKU, hKε⟩ := hK ε (NNReal.coe_pos.mpr hε)
  obtain ⟨L, -, hLc, hKL, hLU⟩ := exists_compact_closed_between hKc hUo hKU
  obtain ⟨ψ, hψ1, hψ0', hψs, hψb⟩ := exists_continuous_one_zero_of_isCompact hKc
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  have hψU : tsupport ψ ⊆ U := by
    refine (closure_minimal ?_ hLc).trans hLU
    intro v hv
    by_contra hvL
    exact hv (hψ0' (fun hi => hvL (interior_subset hi)))
  have hc : Continuous fun v => ψ v * φ v := ψ.continuous.mul hφ
  have hs : HasCompactSupport fun v => ψ v * φ v := hψs.mul_right
  have hsU : tsupport (fun v => ψ v * φ v) ⊆ U := tsupport_mul_subset_left.trans hψU
  have h0 : ∀ v, 0 ≤ ψ v * φ v := fun v => mul_nonneg (hψb v).1 (hφ0 v)
  have hcont : Continuous fun s => ∫ v, ψ v * φ v ∂(fib s) :=
    continuousOn_univ.mp (h.2.2 _ hc hs hsU).2
  have hcmp : ∀ A : Set X, IsCompact A →
      ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν ≤
        ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v * φ v ∂(fib s)) ∂ν + ENNReal.ofReal ε * ν A := by
    intro A hA
    have hAm := hA.measurableSet
    rw [← hDA A hAm, ← lintegral_slice_test h hUm hι hg hfg hc hs hsU h0 hAm]
    calc ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ
        ≤ ∫⁻ v in f ⁻¹' (ι '' A), (ENNReal.ofReal (ψ v * φ v) +
            Kᶜ.indicator (fun v => ENNReal.ofReal (φ v)) v) ∂μ := by
          refine lintegral_mono fun v => ?_
          by_cases hv : v ∈ K
          · rw [Set.indicator_of_notMem (show v ∉ Kᶜ from fun h' => h' hv), add_zero, hψ1 hv, Pi.one_apply, one_mul]
          · rw [Set.indicator_of_mem hv]
            exact le_add_self
      _ = ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v * φ v) ∂μ +
            ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ := by
          rw [lintegral_add_left (f := fun v => ENNReal.ofReal (ψ v * φ v))
              (ENNReal.measurable_ofReal.comp hc.measurable),
            setLIntegral_indicator hKc.measurableSet.compl, Set.inter_comm]
      _ ≤ ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v * φ v) ∂μ + ENNReal.ofReal ε * ν A := by
          gcongr
          exact hKε A hAm
  have hmain := ofReal_le_of_forall_compact ν hD hcont ε hcmp s0
  rw [hint _ hc hs hsU h0, ENNReal.ofReal_coe_nnreal] at hmain
  refine hmain.trans (add_le_add ?_ le_rfl)
  exact lintegral_mono fun v => ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hφ0 v) (hψb v).2)

end GlobalTheory.CompanionTheory.FibreDensityLimit
