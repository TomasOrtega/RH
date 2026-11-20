import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK

namespace Bru

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Set `K` to `CompactExhaustion.choice G`. Use `⟨K, fun n => K.isCompact n, fun x => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `K.exists_mem x`. Conclude with `⟨n + 1, K.subset_interior_succ n hn⟩`.
-/
theorem exists_cover :
    ∃ K : ℕ → Set G, (∀ n, IsCompact (K n)) ∧ ∀ x, ∃ n, x ∈ interior (K n) := by
  let K := CompactExhaustion.choice G
  refine ⟨K, fun n => K.isCompact n, fun x => ?_⟩
  obtain ⟨n, hn⟩ := K.exists_mem x
  exact ⟨n + 1, K.subset_interior_succ n hn⟩

def gf (μ : Measure G) (K : ℕ → Set G) (n : ℕ) (x : G) : ℝ≥0∞ :=
  μ ((fun s => s * x) ⁻¹' K n)

def Eset (μ : Measure G) (K : ℕ → Set G) (n : ℕ) : Set G :=
  {x | gf μ K n x ≠ 0 ∧ ∀ k < n, gf μ K k x = 0}

def bf (μ : Measure G) (K : ℕ → Set G) (x : G) : ℝ≥0∞ :=
  ∑' n, (Eset μ K n).indicator (fun y => (K n).indicator 1 y * (gf μ K n y)⁻¹) x

/- English proof (translation)
Establish `hs : MeasurableSet ((fun p : G × G => p.2 * p.1) ⁻¹' K n)` using `(hK n).measurableSet.preimage (measurable_snd.mul measurable_fst)`. Use `first`. Consider the case `exact measurable_measure_prodMk_left hs`. Consider the case `exact measurable_measure_prod_mk_left hs`.
-/
theorem gf_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (n : ℕ) :
    Measurable (gf μ K n) := by
  have hs : MeasurableSet ((fun p : G × G => p.2 * p.1) ⁻¹' K n) :=
    (hK n).measurableSet.preimage (measurable_snd.mul measurable_fst)
  first
  | exact measurable_measure_prodMk_left hs
  | exact measurable_measure_prod_mk_left hs

/- English proof (translation)
Establish `h : IsCompact ((fun s => s * x) ⁻¹' K n)` using `(Homeomorph.mulRight x).isCompact_preimage.2 (hK n)`. Conclude with `h.measure_lt_top`.
-/
theorem gf_lt_top (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : ℕ → Set G)
    (hK : ∀ n, IsCompact (K n)) (n : ℕ) (x : G) : gf μ K n x < ⊤ := by
  have h : IsCompact ((fun s => s * x) ⁻¹' K n) :=
    (Homeomorph.mulRight x).isCompact_preimage.2 (hK n)
  exact h.measure_lt_top

/- English proof (translation)
Establish `hm : MeasurableSet ((fun s => s * x) ⁻¹' K n)` using `(hK n).measurableSet.preimage (measurable_mul_const x)`. Use `show μ ((fun s => s * (t * x)) ⁻¹' K n) = μ ((fun s => s * x) ⁻¹' K n)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.map_apply (measurable_mul_const t) hm]`. Use `congr 1`.

Use extensionality with `s`. Simplify using `[mul_assoc]`. Use `_ = μ ((fun s => s * x) ⁻¹' K n) := by rw [hr t ht]`.
-/
theorem gf_inv (μ : Measure G) (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (S : Set G)
    (hr : ∀ s ∈ S, μ.map (fun x => x * s) = μ) (n : ℕ) {t : G} (ht : t ∈ S) (x : G) :
    gf μ K n (t * x) = gf μ K n x := by
  have hm : MeasurableSet ((fun s => s * x) ⁻¹' K n) :=
    (hK n).measurableSet.preimage (measurable_mul_const x)
  show μ ((fun s => s * (t * x)) ⁻¹' K n) = μ ((fun s => s * x) ⁻¹' K n)
  calc μ ((fun s => s * (t * x)) ⁻¹' K n)
      = μ.map (fun s => s * t) ((fun s => s * x) ⁻¹' K n) := by
        rw [Measure.map_apply (measurable_mul_const t) hm]
        congr 1
        ext s
        simp [mul_assoc]
    _ = μ ((fun s => s * x) ⁻¹' K n) := by rw [hr t ht]

/- English proof (translation)
Introduce `h0`. Establish `hU : IsOpen ((fun s => s * x) ⁻¹' interior (K n))` using `isOpen_interior.preimage (continuous_mul_right x)`. Establish `hne` using `hpos _ hU ⟨1, by simpa using hx, h1⟩`. Conclude with `hne (measure_mono_null (Set.preimage_mono interior_subset) h0)`.
-/
theorem gf_pos (μ : Measure G) (K : ℕ → Set G) (S : Set G) (h1 : (1 : G) ∈ S)
    (hpos : PosOn μ S) (n : ℕ) {x : G} (hx : x ∈ interior (K n)) : gf μ K n x ≠ 0 := by
  intro h0
  have hU : IsOpen ((fun s => s * x) ⁻¹' interior (K n)) :=
    isOpen_interior.preimage (continuous_mul_right x)
  have hne := hpos _ hU ⟨1, by simpa using hx, h1⟩
  exact hne (measure_mono_null (Set.preimage_mono interior_subset) h0)

/- English proof (translation)
Establish `h1 : MeasurableSet {x | gf μ K n x ≠ 0}` using `(gf_meas μ K hK n) (measurableSet_singleton 0).compl`. Establish `h2 : MeasurableSet {x | ∀ k < n, gf μ K k x = 0}`. Simplify using `only [Set.setOf_forall]`. Conclude with `MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (gf_meas μ K hK k) (measurableSet_singleton 0)`. Conclude with `h1.inter h2`.
-/
theorem Eset_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n))
    (n : ℕ) : MeasurableSet (Eset μ K n) := by
  have h1 : MeasurableSet {x | gf μ K n x ≠ 0} :=
    (gf_meas μ K hK n) (measurableSet_singleton 0).compl
  have h2 : MeasurableSet {x | ∀ k < n, gf μ K k x = 0} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (gf_meas μ K hK k) (measurableSet_singleton 0)
  exact h1.inter h2

/- English proof (translation)
Break down `lt_trichotomy n m with h | h | h` into its components or cases. Conclude with `absurd (hm.2 n h) hn.1`. Conclude with `h`. Conclude with `absurd (hn.2 m h) hm.1`.
-/
theorem Eset_unique {μ : Measure G} {K : ℕ → Set G} {x : G} {n m : ℕ}
    (hn : x ∈ Eset μ K n) (hm : x ∈ Eset μ K m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact absurd (hm.2 n h) hn.1
  · exact h
  · exact absurd (hn.2 m h) hm.1

/- English proof (translation)
Use `⟨Nat.find h, Nat.find_spec h, fun k hk => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `Nat.find_min h hk hc`.
-/
theorem Eset_exists (μ : Measure G) (K : ℕ → Set G) (x : G) (h : ∃ n, gf μ K n x ≠ 0) :
    ∃ n, x ∈ Eset μ K n := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun k hk => ?_⟩
  by_contra hc
  exact Nat.find_min h hk hc

/- English proof (translation)
Establish `h : ∀ k, gf μ K k (t * x) = gf μ K k x` using `fun k => gf_inv μ K hK S hr k ht x`. Simplify using `only [Eset, Set.mem_setOf_eq, h]`.
-/
theorem Eset_inv (μ : Measure G) (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (S : Set G)
    (hr : ∀ s ∈ S, μ.map (fun x => x * s) = μ) (n : ℕ) {t : G} (ht : t ∈ S) (x : G) :
    t * x ∈ Eset μ K n ↔ x ∈ Eset μ K n := by
  have h : ∀ k, gf μ K k (t * x) = gf μ K k x := fun k => gf_inv μ K hK S hr k ht x
  simp only [Eset, Set.mem_setOf_eq, h]

/- English proof (translation)
Unfold `bf`. Use `Measurable.ennreal_tsum fun n => ?_` and prove the remaining obligations. Use `Measurable.indicator ?_ (Eset_meas μ K hK n)` and prove the remaining obligations. Conclude with `(measurable_one.indicator (hK n).measurableSet).mul (gf_meas μ K hK n).inv`.
-/
theorem bf_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) :
    Measurable (bf μ K) := by
  unfold bf
  refine Measurable.ennreal_tsum fun n => ?_
  refine Measurable.indicator ?_ (Eset_meas μ K hK n)
  exact (measurable_one.indicator (hK n).measurableSet).mul (gf_meas μ K hK n).inv

end Bru

open Bru in
/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ S hS hG μ hinv hfin hpos hr`. Take `⟨hsf, -, hSc, -⟩` from `hinv`. Use `haveI := hsf`. Use `haveI := hfin`. Take `⟨K, hKc, hKx⟩` from `exists_cover (G := G)`.

Establish `hKcl : ∀ n, IsClosed (K n)` using `fun n => (hKc n).isClosed`. Use `⟨bf μ K, bf_meas μ K hKcl, fun x => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `hKx x`. Take `⟨n, hn⟩` from `Eset_exists μ K x ⟨m, gf_pos μ K S hG.1 hpos m hm⟩`. Establish `hS' : ∀ᵐ s ∂μ, s ∈ S` using `ae_iff.2 hSc`.

Establish `hae : ∀ᵐ s ∂μ, bf μ K (s * x) = (K n).indicator 1 (s * x) * (gf μ K n x)⁻¹` using `by filter_upwards [hS'] with s hs`. Unfold `bf`. Rewrite using `[tsum_eq_single n]`. Rewrite using `[Set.indicator_of_mem ((Eset_inv μ K hKcl S hr n hs x).2 hn)]`. Simplify using `only [gf_inv μ K hKcl S hr n hs x]`.

Introduce `k hk`. Establish `hk' : s * x ∉ Eset μ K k` using `fun hk' => hk (Eset_unique ((Eset_inv μ K hKcl S hr k hs x).1 hk') hn)`. Use `first`. Consider the case `exact Set.indicator_of_notMem hk' _`. Consider the case `exact Set.indicator_of_not_mem hk' _`.

Establish `hmeas : Measurable fun s => (K n).indicator (1 : G → ℝ≥0∞) (s * x)` using `(measurable_one.indicator (hKcl n).measurableSet).comp (measurable_mul_const x)`. Establish `e1 : (fun s => (K n).indicator (1 : G → ℝ≥0∞) (s * x)) = ((fun s => s * x) ⁻¹' K n).indicator 1`. Use extensionality with `s`. Use `first`. Consider the case `rfl`.

Consider the case `simp [Set.indicator_apply]`. Rewrite using `[lintegral_congr_ae hae, lintegral_mul_const _ hmeas, e1, lintegral_indicator_one ((hKcl n).measurableSet.preimage (measurable_mul_const x))]`. Conclude with `ENNReal.mul_inv_cancel hn.1 (gf_lt_top μ K hKc n x).ne`.
-/
theorem bruhat_decomposition' : Bruhat := by
  intro G _ _ _ _ _ _ _ _ S hS hG μ hinv hfin hpos hr
  obtain ⟨hsf, -, hSc, -⟩ := hinv
  haveI := hsf
  haveI := hfin
  obtain ⟨K, hKc, hKx⟩ := exists_cover (G := G)
  have hKcl : ∀ n, IsClosed (K n) := fun n => (hKc n).isClosed
  refine ⟨bf μ K, bf_meas μ K hKcl, fun x => ?_⟩
  obtain ⟨m, hm⟩ := hKx x
  obtain ⟨n, hn⟩ := Eset_exists μ K x ⟨m, gf_pos μ K S hG.1 hpos m hm⟩
  have hS' : ∀ᵐ s ∂μ, s ∈ S := ae_iff.2 hSc
  have hae : ∀ᵐ s ∂μ, bf μ K (s * x) = (K n).indicator 1 (s * x) * (gf μ K n x)⁻¹ := by
    filter_upwards [hS'] with s hs
    unfold bf
    rw [tsum_eq_single n]
    · rw [Set.indicator_of_mem ((Eset_inv μ K hKcl S hr n hs x).2 hn)]
      simp only [gf_inv μ K hKcl S hr n hs x]
    · intro k hk
      have hk' : s * x ∉ Eset μ K k := fun hk' =>
        hk (Eset_unique ((Eset_inv μ K hKcl S hr k hs x).1 hk') hn)
      first
      | exact Set.indicator_of_notMem hk' _
      | exact Set.indicator_of_not_mem hk' _
  have hmeas : Measurable fun s => (K n).indicator (1 : G → ℝ≥0∞) (s * x) :=
    (measurable_one.indicator (hKcl n).measurableSet).comp (measurable_mul_const x)
  have e1 : (fun s => (K n).indicator (1 : G → ℝ≥0∞) (s * x)) =
      ((fun s => s * x) ⁻¹' K n).indicator 1 := by
    ext s
    first
    | rfl
    | simp [Set.indicator_apply]
  rw [lintegral_congr_ae hae, lintegral_mul_const _ hmeas, e1,
    lintegral_indicator_one ((hKcl n).measurableSet.preimage (measurable_mul_const x))]
  exact ENNReal.mul_inv_cancel hn.1 (gf_lt_top μ K hKc n x).ne

end QPK
