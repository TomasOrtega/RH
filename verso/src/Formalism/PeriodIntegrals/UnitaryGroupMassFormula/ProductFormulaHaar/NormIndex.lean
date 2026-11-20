import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormMod

noncomputable section

open MeasureTheory ValuativeRel
open scoped Pointwise ENNReal NNReal

namespace PI.ProdFormulaE

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
Conclude with `Valuation.isOpen_integer`.
-/
theorem isOpen_integers : IsOpen ((𝒪[K] : Subring K) : Set K) := by
  exact Valuation.isOpen_integer

/- English proof (translation)
Conclude with `isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[K]))`.
-/
theorem isCompact_integers : IsCompact ((𝒪[K] : Subring K) : Set K) := by
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[K]))

/- English proof (translation)
The claim follows from `MeasurableEmbedding.subtype_coe isOpen_integers.measurableSet`.
-/
private theorem measurableEmbedding_coe_integers :
    MeasurableEmbedding (Subtype.val : 𝒪[K] → K) :=
  MeasurableEmbedding.subtype_coe isOpen_integers.measurableSet

/- English proof (translation)
Conclude with `Measurable.subtype_mk ((measurable_const_add (c : K)).comp measurable_subtype_coe)`.
-/
private theorem measurable_integers_const_add (c : 𝒪[K]) :
    Measurable (fun x : 𝒪[K] => c + x) := by
  exact Measurable.subtype_mk ((measurable_const_add (c : K)).comp measurable_subtype_coe)

/- English proof (translation)
Conclude with `Measurable.subtype_mk ((measurable_add_const (c : K)).comp measurable_subtype_coe)`.
-/
private theorem measurable_integers_add_const (c : 𝒪[K]) :
    Measurable (fun x : 𝒪[K] => x + c) := by
  exact Measurable.subtype_mk ((measurable_add_const (c : K)).comp measurable_subtype_coe)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun c => measurable_integers_const_add c, fun c => measurable_integers_add_const c⟩`.
-/
private theorem measurableAdd_integers : MeasurableAdd 𝒪[K] :=
  ⟨fun c => measurable_integers_const_add c, fun c => measurable_integers_add_const c⟩

/- English proof (translation)
Establish `he : MeasurableEmbedding (Subtype.val : 𝒪[K] → K)` using `measurableEmbedding_coe_integers`. Prove the components needed by the constructor for the conclusion. Introduce `g`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply (measurable_integers_const_add g) hs, he.comap_apply, he.comap_apply]`.

Establish `hset : Subtype.val '' ((fun x : 𝒪[K] => g + x) ⁻¹' s) = (fun y : K => (g : K) + y) ⁻¹' (Subtype.val '' s)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ show (g : K) + x ∈ Subtype.val '' s`. Conclude with `⟨g + x, hx, rfl⟩`.

Introduce and unpack `⟨z, hz, hzy⟩`. Establish `hy : y ∈ 𝒪[K]`. Establish `hyz : y = (z : K) - g` using `by rw [hzy]; ring`. Rewrite using `[hyz]`. Conclude with `sub_mem z.2 g.2`.

Use `⟨⟨y, hy⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show g + ⟨y, hy⟩ ∈ s`. Establish `hgz : g + ⟨y, hy⟩ = z`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hzy]`.

Apply the tactic sequence `try rfl`. Rewrite using `[hgz]`. Conclude with `hz`. Rewrite using `[hset, measure_preimage_add]`.
-/
theorem comap_isAddLeftInvariant (μ : Measure K) [μ.IsAddLeftInvariant] :
    (μ.comap (Subtype.val : 𝒪[K] → K)).IsAddLeftInvariant := by
  have he : MeasurableEmbedding (Subtype.val : 𝒪[K] → K) := measurableEmbedding_coe_integers
  constructor
  intro g
  ext s hs
  rw [Measure.map_apply (measurable_integers_const_add g) hs, he.comap_apply, he.comap_apply]
  have hset : Subtype.val '' ((fun x : 𝒪[K] => g + x) ⁻¹' s) =
      (fun y : K => (g : K) + y) ⁻¹' (Subtype.val '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show (g : K) + x ∈ Subtype.val '' s
      exact ⟨g + x, hx, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hy : y ∈ 𝒪[K] := by
        have hyz : y = (z : K) - g := by rw [hzy]; ring
        rw [hyz]
        exact sub_mem z.2 g.2
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      show g + ⟨y, hy⟩ ∈ s
      have hgz : g + ⟨y, hy⟩ = z := by
        apply Subtype.ext
        rw [hzy]
        try rfl
      rw [hgz]
      exact hz
  rw [hset, measure_preimage_add]

end

/- English proof (translation)
Take `⟨u, hu⟩ : ∃ u : Kˣ, u = Units.mk0 (t : K) htK` from `⟨_, rfl⟩`. Rewrite using `[← hu]`. Establish `hut : (u : K) = t` using `by rw [hu, Units.val_mk0]`. Establish `hsmul : ∀ x : K, u • x = (t : K) * x` using `fun x => by`. Rewrite using `[Units.smul_def, hut, smul_eq_mul]`.

Establish `hSo : IsOpen ((𝒪[K] : Subring K) : Set K)` using `isOpen_integers`. Establish `hSc : IsCompact ((𝒪[K] : Subring K) : Set K)` using `isCompact_integers`. Establish `huS : IsOpen (u • ((𝒪[K] : Subring K) : Set K))` using `hSo.smul u`. Establish `hsub : u • ((𝒪[K] : Subring K) : Set K) ⊆ ((𝒪[K] : Subring K) : Set K)`. Introduce and unpack `x ⟨s, hs, rfl⟩`.

Establish `h1 : (t : K) * s ∈ ((𝒪[K] : Subring K) : Set K)` using `(𝒪[K]).mul_mem t.2 hs`. Rewrite `h1` using `[← hsmul]`. Conclude with `h1`. Establish `hrange : u • ((𝒪[K] : Subring K) : Set K) ⊆ Set.range (Subtype.val : 𝒪[K] → K)`. Introduce `x hx`.

Conclude with `⟨⟨x, hsub hx⟩, rfl⟩`. Establish `hR : Set.range (Subtype.val : 𝒪[K] → K) = ((𝒪[K] : Subring K) : Set K)`. Conclude with `Subtype.range_coe`. Establish `hmem : ∀ y : 𝒪[K], y ∈ Ideal.span {t} ↔ (y : K) ∈ u • ((𝒪[K] : Subring K) : Set K)`. Introduce `y`.

Rewrite using `[Ideal.mem_span_singleton', Set.mem_smul_set]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Use `⟨(a : K), a.2, ?_⟩` and prove the remaining obligations. Rewrite using `[hsmul]`.

Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Introduce and unpack `⟨s, hs, hy⟩`. Use `⟨⟨s, hs⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hy, hsmul]`. Use `show s * (t : K) = (t : K) * s`. Expand and normalize the polynomial expressions, which then agree. Take `⟨H, hHdef⟩ : ∃ H : AddSubgroup 𝒪[K], H = (Ideal.span {t}).toAddSubgroup` from `⟨_, rfl⟩`. Rewrite using `[← hHdef]`.

Establish `hH : (H : Set 𝒪[K]) = Subtype.val ⁻¹' (u • ((𝒪[K] : Subring K) : Set K))`. Use extensionality with `y`. Rewrite using `[hHdef]`. Conclude with `hmem y`. Establish `hHo : IsOpen (H : Set 𝒪[K])`.

Rewrite using `[hH]`. Conclude with `huS.preimage continuous_subtype_val`. Establish `hHm : MeasurableSet (H : Set 𝒪[K])`. Rewrite using `[hH]`. Conclude with `measurable_subtype_coe huS.measurableSet`.

Establish `: Finite (𝒪[K] ⧸ H)` using `AddSubgroup.quotient_finite_of_isOpen H hHo`. Establish `: H.FiniteIndex` using `AddSubgroup.finiteIndex_of_finite_quotient`. Establish `: MeasurableAdd 𝒪[K]` using `measurableAdd_integers`. Use `comap_isAddLeftInvariant (K := K) μ` as an intermediate fact. Establish `he : MeasurableEmbedding (Subtype.val : 𝒪[K] → K)` using `measurableEmbedding_coe_integers`.

Establish `key` using `AddSubgroup.index_mul_measure H hHm (μ.comap (Subtype.val : 𝒪[K] → K))`. Rewrite `key` using `[he.comap_apply, he.comap_apply, hH, Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hrange, Set.image_univ, hR, ← distribHaarChar_mul μ u ((𝒪[K] : Subring K) : Set K), ← mul_assoc]`. Establish `hpos : μ ((𝒪[K] : Subring K) : Set K) ≠ 0` using `(hSo.measure_pos μ ⟨0, (𝒪[K]).zero_mem⟩).ne'`. Establish `hfin : μ ((𝒪[K] : Subring K) : Set K) ≠ ∞` using `(hSc.measure_lt_top (μ := μ)).ne`. Establish `hdiv` using `ENNReal.mul_div_cancel_right (a := (H.index : ℝ≥0∞) * (distribHaarChar K u : ℝ≥0∞)) hpos hfin`.

Rewrite `hdiv` using `[key, ENNReal.div_self hpos hfin]`. Conclude with `hdiv.symm`.
-/
private theorem index_span_mul_distribHaarChar_eq_one {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (t : 𝒪[K]) (htK : (t : K) ≠ 0) :
    ((Ideal.span {t}).toAddSubgroup.index : ℝ≥0∞) *
      (distribHaarChar K (Units.mk0 (t : K) htK) : ℝ≥0∞) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, u = Units.mk0 (t : K) htK := ⟨_, rfl⟩
  rw [← hu]
  have hut : (u : K) = t := by rw [hu, Units.val_mk0]
  have hsmul : ∀ x : K, u • x = (t : K) * x := fun x => by
    rw [Units.smul_def, hut, smul_eq_mul]
  have hSo : IsOpen ((𝒪[K] : Subring K) : Set K) := isOpen_integers
  have hSc : IsCompact ((𝒪[K] : Subring K) : Set K) := isCompact_integers
  have huS : IsOpen (u • ((𝒪[K] : Subring K) : Set K)) := hSo.smul u
  have hsub : u • ((𝒪[K] : Subring K) : Set K) ⊆ ((𝒪[K] : Subring K) : Set K) := by
    rintro x ⟨s, hs, rfl⟩
    have h1 : (t : K) * s ∈ ((𝒪[K] : Subring K) : Set K) := (𝒪[K]).mul_mem t.2 hs
    rw [← hsmul] at h1
    exact h1
  have hrange : u • ((𝒪[K] : Subring K) : Set K) ⊆ Set.range (Subtype.val : 𝒪[K] → K) := by
    intro x hx
    exact ⟨⟨x, hsub hx⟩, rfl⟩
  have hR : Set.range (Subtype.val : 𝒪[K] → K) = ((𝒪[K] : Subring K) : Set K) := by
    exact Subtype.range_coe
  have hmem : ∀ y : 𝒪[K], y ∈ Ideal.span {t} ↔ (y : K) ∈ u • ((𝒪[K] : Subring K) : Set K) := by
    intro y
    rw [Ideal.mem_span_singleton', Set.mem_smul_set]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨(a : K), a.2, ?_⟩
      rw [hsmul]
      rw [mul_comm]
      rfl
    · rintro ⟨s, hs, hy⟩
      refine ⟨⟨s, hs⟩, ?_⟩
      apply Subtype.ext
      rw [← hy, hsmul]
      show s * (t : K) = (t : K) * s
      ring
  obtain ⟨H, hHdef⟩ : ∃ H : AddSubgroup 𝒪[K], H = (Ideal.span {t}).toAddSubgroup := ⟨_, rfl⟩
  rw [← hHdef]
  have hH : (H : Set 𝒪[K]) = Subtype.val ⁻¹' (u • ((𝒪[K] : Subring K) : Set K)) := by
    ext y
    rw [hHdef]
    exact hmem y
  have hHo : IsOpen (H : Set 𝒪[K]) := by
    rw [hH]
    exact huS.preimage continuous_subtype_val
  have hHm : MeasurableSet (H : Set 𝒪[K]) := by
    rw [hH]
    exact measurable_subtype_coe huS.measurableSet
  have : Finite (𝒪[K] ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hHo
  have : H.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have : MeasurableAdd 𝒪[K] := measurableAdd_integers
  have := comap_isAddLeftInvariant (K := K) μ
  have he : MeasurableEmbedding (Subtype.val : 𝒪[K] → K) := measurableEmbedding_coe_integers
  have key := AddSubgroup.index_mul_measure H hHm (μ.comap (Subtype.val : 𝒪[K] → K))
  rw [he.comap_apply, he.comap_apply, hH, Set.image_preimage_eq_inter_range,
    Set.inter_eq_left.mpr hrange, Set.image_univ, hR,
    ← distribHaarChar_mul μ u ((𝒪[K] : Subring K) : Set K), ← mul_assoc] at key
  have hpos : μ ((𝒪[K] : Subring K) : Set K) ≠ 0 :=
    (hSo.measure_pos μ ⟨0, (𝒪[K]).zero_mem⟩).ne'
  have hfin : μ ((𝒪[K] : Subring K) : Set K) ≠ ∞ := (hSc.measure_lt_top (μ := μ)).ne
  have hdiv := ENNReal.mul_div_cancel_right
    (a := (H.index : ℝ≥0∞) * (distribHaarChar K u : ℝ≥0∞)) hpos hfin
  rw [key, ENNReal.div_self hpos hfin] at hdiv
  exact hdiv.symm

/- English proof (translation)
Unfold `IndexFormula`. Introduce `K _ _ _ _ t ht`. Set `_ : MeasurableSpace K` to `borel K`. Establish `: BorelSpace K` using `⟨rfl⟩`. Establish `htK : (t : K) ≠ 0` using `by simpa using ht`.

Establish `key` using `index_span_mul_distribHaarChar_eq_one (K := K) (Measure.addHaar : Measure K) t htK`. Rewrite using `[modF_of_ne htK]`. Use `show ((distribHaarChar K (Units.mk0 (t : K) htK) : ℝ≥0) : ℝ) * ((Ideal.span {t}).toAddSubgroup.index : ℝ) = 1`. Establish `key' : ((Ideal.span {t}).toAddSubgroup.index : ℝ≥0) * distribHaarChar K (Units.mk0 (t : K) htK) = 1`. Conclude with `key` after adjusting the coercions.

Rewrite using `[mul_comm]`. Conclude with `key'` after adjusting the coercions.
-/
theorem modulus_mul_card_quotient : IndexFormula := by
  unfold IndexFormula
  intro K _ _ _ _ t ht
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have htK : (t : K) ≠ 0 := by simpa using ht
  have key := index_span_mul_distribHaarChar_eq_one (K := K) (Measure.addHaar : Measure K) t htK
  rw [modF_of_ne htK]
  show ((distribHaarChar K (Units.mk0 (t : K) htK) : ℝ≥0) : ℝ) *
    ((Ideal.span {t}).toAddSubgroup.index : ℝ) = 1
  have key' : ((Ideal.span {t}).toAddSubgroup.index : ℝ≥0) *
      distribHaarChar K (Units.mk0 (t : K) htK) = 1 := by
    exact_mod_cast key
  rw [mul_comm]
  exact_mod_cast key'

end PI.ProdFormulaE
