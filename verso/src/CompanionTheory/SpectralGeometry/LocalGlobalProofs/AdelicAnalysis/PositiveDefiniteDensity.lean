import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierInversionSchwartzBruhatStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Density

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]

/- English proof (translation)
Establish `hne : ∀ x y, χ x y ≠ 0` using `fun x y h => by simpa [h] using hn x y`. Establish `h0 : ∀ y, χ 0 y = 1` using `fun y => by`. Establish `h` using `ha 0 0 y`. Rewrite `h` using `[add_zero]`. Establish `h' : χ 0 y * χ 0 y = χ 0 y * 1` using `by rw [mul_one]; exact h.symm`.

Conclude with `mul_left_cancel₀ (hne 0 y) h'`. Establish `hi : ∀ x y, χ (-x) y * χ x y = 1` using `fun x y => by`. Rewrite using `[← ha, neg_add_cancel, h0]`. Establish `h1` using `hi x y`. Establish `h2` using `hi y x`.

Rewrite `h2` using `[hs (-y) x, hs y x]`. Conclude with `mul_right_cancel₀ (hne x y) (h1.trans h2.symm)`.
-/
theorem chi_neg_left {χ : V → V → ℂ} (hs : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1)
    (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (x y : V) : χ (-x) y = χ x (-y) := by
  have hne : ∀ x y, χ x y ≠ 0 := fun x y h => by simpa [h] using hn x y
  have h0 : ∀ y, χ 0 y = 1 := fun y => by
    have h := ha 0 0 y
    rw [add_zero] at h
    have h' : χ 0 y * χ 0 y = χ 0 y * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ (hne 0 y) h'
  have hi : ∀ x y, χ (-x) y * χ x y = 1 := fun x y => by
    rw [← ha, neg_add_cancel, h0]
  have h1 := hi x y
  have h2 := hi y x
  rw [hs (-y) x, hs y x] at h2
  exact mul_right_cancel₀ (hne x y) (h1.trans h2.symm)

def mhat (χ : V → V → ℂ) (m : Measure V) (y : V) : ℂ := ∫ z, χ z y ∂m

def dens (χ : V → V → ℂ) (μ m : Measure V) (x : V) : ℂ := ∫ y, mhat χ m y * χ (-x) y ∂μ

def coset (L : AddSubgroup V) (a : V) : Set V := {x | x - a ∈ L}

section Top

variable [IsTopologicalAddGroup V]

/- English proof (translation)
Use `continuous_of_dominated (bound := fun y => ‖mhat χ m y‖) ?_ ?_ hint.norm ?_` and prove the remaining obligations. Introduce `x`. Conclude with `hint.aestronglyMeasurable.mul (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable`. Introduce `x`. Conclude with `Filter.Eventually.of_forall fun y => by simp [hn]`.

Conclude with `Filter.Eventually.of_forall fun y => continuous_const.mul (hc.comp (continuous_neg.prodMk continuous_const))`.
-/
theorem dens_continuous [SecondCountableTopology V] [BorelSpace V] {χ : V → V → ℂ} {μ m : Measure V}
    (hc : Continuous (fun p : V × V => χ p.1 p.2)) (hn : ∀ x y, ‖χ x y‖ = 1)
    (hint : Integrable (mhat χ m) μ) : Continuous (dens χ μ m) := by
  refine continuous_of_dominated (bound := fun y => ‖mhat χ m y‖) ?_ ?_ hint.norm ?_
  · intro x
    exact hint.aestronglyMeasurable.mul
      (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun y => by simp [hn]
  · exact Filter.Eventually.of_forall fun y =>
      continuous_const.mul (hc.comp (continuous_neg.prodMk continuous_const))

/- English proof (translation)
The claim follows from `hL.preimage (continuous_id.sub continuous_const)`.
-/
theorem coset_isOpen {L : AddSubgroup V} (hL : IsOpen (L : Set V)) (a : V) : IsOpen (coset L a) :=
  hL.preimage (continuous_id.sub continuous_const)

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨x - a, h, by simp⟩`. Introduce and unpack `⟨l, hl, rfl⟩`.

Simplify `hl` using `[coset]`.
-/
theorem coset_eq_image (L : AddSubgroup V) (a : V) : coset L a = (fun x => x + a) '' (L : Set V) := by
  ext x
  constructor
  · intro h
    exact ⟨x - a, h, by simp⟩
  · rintro ⟨l, hl, rfl⟩
    simpa [coset] using hl

/- English proof (translation)
Rewrite using `[coset_eq_image]`. Conclude with `hL.image (continuous_id.add continuous_const)`.
-/
theorem coset_isCompact {L : AddSubgroup V} (hL : IsCompact (L : Set V)) (a : V) :
    IsCompact (coset L a) := by
  rw [coset_eq_image]
  exact hL.image (continuous_id.add continuous_const)

/- English proof (translation)
Establish `hc` using `coset_isCompact hK a`. Establish `ho` using `coset_isOpen hO a`. Use `⟨?_, .intro hc fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Conclude with `(LocallyConstant.indicator (1 : LocallyConstant V ℂ) ⟨hc.isClosed, ho⟩).isLocallyConstant`.
-/
theorem coset_sb [T2Space V] {L : AddSubgroup V} (hK : IsCompact (L : Set V)) (hO : IsOpen (L : Set V))
    (a : V) : SB (Set.indicator (coset L a) (fun _ => (1 : ℂ))) := by
  have hc := coset_isCompact hK a
  have ho := coset_isOpen hO a
  refine ⟨?_, .intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (1 : LocallyConstant V ℂ) ⟨hc.isClosed, ho⟩).isLocallyConstant

end Top

section Main

variable [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [BorelSpace V]

/- English proof (translation)
Take `⟨hsb, hinv⟩` from `GlobalTheory.T.fourier_inversion_schwartz_bruhat V χ μ h φ hφ`. Establish `hφi : Integrable φ μ` using `hφ.1.continuous.integrable_of_hasCompactSupport hφ.2`. Establish `hfi : Integrable (fou χ μ φ) μ` using `hsb.1.continuous.integrable_of_hasCompactSupport hsb.2`. Establish `hfni : Integrable (fun y => fou χ μ φ (-y)) μ` using `hfi.comp_neg`. Establish `hF : Integrable (Function.uncurry fun x y => φ x * (mhat χ m y * χ (-x) y)) (μ.prod μ)`.

Establish `h1 : Integrable (fun p : V × V => φ p.1 * mhat χ m p.2) (μ.prod μ)` using `hφi.mul_prod hint`. Establish `h2` using `h1.mul_bdd (c := 1) (g := fun p : V × V => χ (-p.1) p.2) (hc.comp ((continuous_neg.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable (Filter.Eventually.of_forall fun p => by simp [hn])`. Use `h2.congr (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `[Function.uncurry, mul_assoc]`. Establish `hH : Integrable (Function.uncurry fun y z => fou χ μ φ (-y) * χ z y) (μ.prod m)`.

Establish `h1 : Integrable (fun p : V × V => fou χ μ φ (-p.1) * (1 : ℂ)) (μ.prod m)` using `hfni.mul_prod (integrable_const (1 : ℂ))`. Establish `h2` using `h1.mul_bdd (c := 1) (g := fun p : V × V => χ p.2 p.1) (hc.comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable (Filter.Eventually.of_forall fun p => by simp [hn])`. Use `h2.congr (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `[Function.uncurry]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [dens, integral_const_mul]`. Use `_ = ∫ y, ∫ x, φ x * (mhat χ m y * χ (-x) y) ∂μ ∂μ := integral_integral_swap hF`. Use `_ = ∫ y, ∫ z, fou χ μ φ (-y) * χ z y ∂m ∂μ := by`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `e1 : ∀ x, φ x * (mhat χ m y * χ (-x) y) = mhat χ m y * (φ x * χ x (-y))` using `fun x => by`.

Rewrite using `[chi_neg_left hs hn ha]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1]`. Rewrite using `[integral_const_mul, integral_const_mul, mul_comm]`. Both sides reduce to the same expression.

Use `_ = ∫ z, ∫ y, fou χ μ φ (-y) * χ z y ∂μ ∂m := integral_integral_swap hH`. Use `_ = ∫ z, φ z ∂m := by`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Establish `e2 : ∫ y, fou χ μ φ (-y) * χ z y ∂μ = ∫ y, fou χ μ φ y * χ z (-y) ∂μ`. Rewrite using `[← integral_neg_eq_self (fun y => fou χ μ φ y * χ z (-y)) μ]`.

Simplify using the standard rewrite rules. Establish `e3 : ∀ y, χ z (-y) = χ y (-z)` using `fun y => by`. Rewrite using `[← chi_neg_left hs hn ha, hs]`. Simplify using `only [e2, e3]`. Use `hinv (-z)` as an intermediate fact.

Simplify `this` using `[fou]`.
-/
theorem integral_mul_dens {χ : V → V → ℂ} {μ m : Measure V} [μ.IsAddHaarMeasure] [IsFiniteMeasure m]
    (h : NADual V χ μ) (hc : Continuous (fun p : V × V => χ p.1 p.2)) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (hint : Integrable (mhat χ m) μ) {φ : V → ℂ} (hφ : SB φ) :
    ∫ x, φ x * dens χ μ m x ∂μ = ∫ z, φ z ∂m := by
  obtain ⟨hsb, hinv⟩ := GlobalTheory.T.fourier_inversion_schwartz_bruhat V χ μ h φ hφ
  have hφi : Integrable φ μ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
  have hfi : Integrable (fou χ μ φ) μ := hsb.1.continuous.integrable_of_hasCompactSupport hsb.2
  have hfni : Integrable (fun y => fou χ μ φ (-y)) μ := hfi.comp_neg
  have hF : Integrable (Function.uncurry fun x y => φ x * (mhat χ m y * χ (-x) y)) (μ.prod μ) := by
    have h1 : Integrable (fun p : V × V => φ p.1 * mhat χ m p.2) (μ.prod μ) := hφi.mul_prod hint
    have h2 := h1.mul_bdd (c := 1) (g := fun p : V × V => χ (-p.1) p.2)
      (hc.comp ((continuous_neg.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simp [hn])
    refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, mul_assoc]
  have hH : Integrable (Function.uncurry fun y z => fou χ μ φ (-y) * χ z y) (μ.prod m) := by
    have h1 : Integrable (fun p : V × V => fou χ μ φ (-p.1) * (1 : ℂ)) (μ.prod m) :=
      hfni.mul_prod (integrable_const (1 : ℂ))
    have h2 := h1.mul_bdd (c := 1) (g := fun p : V × V => χ p.2 p.1)
      (hc.comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simp [hn])
    refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [Function.uncurry]
  calc ∫ x, φ x * dens χ μ m x ∂μ
      = ∫ x, ∫ y, φ x * (mhat χ m y * χ (-x) y) ∂μ ∂μ := by
        simp only [dens, integral_const_mul]
    _ = ∫ y, ∫ x, φ x * (mhat χ m y * χ (-x) y) ∂μ ∂μ := integral_integral_swap hF
    _ = ∫ y, ∫ z, fou χ μ φ (-y) * χ z y ∂m ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        have e1 : ∀ x, φ x * (mhat χ m y * χ (-x) y) = mhat χ m y * (φ x * χ x (-y)) := fun x => by
          rw [chi_neg_left hs hn ha]; ring
        simp only [e1]
        rw [integral_const_mul, integral_const_mul, mul_comm]
        rfl
    _ = ∫ z, ∫ y, fou χ μ φ (-y) * χ z y ∂μ ∂m := integral_integral_swap hH
    _ = ∫ z, φ z ∂m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have e2 : ∫ y, fou χ μ φ (-y) * χ z y ∂μ = ∫ y, fou χ μ φ y * χ z (-y) ∂μ := by
          rw [← integral_neg_eq_self (fun y => fou χ μ φ y * χ z (-y)) μ]
          simp
        have e3 : ∀ y, χ z (-y) = χ y (-z) := fun y => by
          rw [← chi_neg_left hs hn ha, hs]
        simp only [e2, e3]
        have := hinv (-z)
        simpa [fou] using this

/- English proof (translation)
Establish `hm : MeasurableSet (coset L a)` using `(coset_isOpen hO a).measurableSet`. Establish `key` using `integral_mul_dens h hc hs hn ha hint (coset_sb hK hO a)`. Establish `e : ∀ x, Set.indicator (coset L a) (fun _ => (1 : ℂ)) x * dens χ μ m x = Set.indicator (coset L a) (dens χ μ m) x` using `fun x => by`. Apply the tactic sequence `by_cases hx : x ∈ coset L a <;> simp [hx]`. Simplify using `only [e] at key`.

Rewrite `key` using `[integral_indicator hm, integral_indicator_const _ hm]`. Rewrite using `[key]`. Simplify using `[Measure.real]`.
-/
theorem setIntegral_dens {χ : V → V → ℂ} {μ m : Measure V} [μ.IsAddHaarMeasure] [IsFiniteMeasure m]
    (h : NADual V χ μ) (hc : Continuous (fun p : V × V => χ p.1 p.2)) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (hint : Integrable (mhat χ m) μ) {L : AddSubgroup V} (hK : IsCompact (L : Set V))
    (hO : IsOpen (L : Set V)) (a : V) :
    ∫ x in coset L a, dens χ μ m x ∂μ = ((m (coset L a)).toReal : ℂ) := by
  have hm : MeasurableSet (coset L a) := (coset_isOpen hO a).measurableSet
  have key := integral_mul_dens h hc hs hn ha hint (coset_sb hK hO a)
  have e : ∀ x, Set.indicator (coset L a) (fun _ => (1 : ℂ)) x * dens χ μ m x =
      Set.indicator (coset L a) (dens χ μ m) x := fun x => by
    by_cases hx : x ∈ coset L a <;> simp [hx]
  simp only [e] at key
  rw [integral_indicator hm, integral_indicator_const _ hm] at key
  rw [key]
  simp [Measure.real]

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Use `push_neg at hx`. Establish `hU : (fun t => f (t + x)) ⁻¹' Set.Iio 0 ∈ 𝓝 (0 : V)` using `((isOpen_Iio.preimage (hf.comp (continuous_id.add continuous_const))).mem_nhds (by simpa using hx))`. Take `⟨L, hK, hO, hLU⟩` from `hb _ hU`. Establish `hneg : ∀ y ∈ coset L x, f y < 0` using `fun y hy => by`.

Use `hLU hy` as an intermediate fact. Simplify using `using this`. Establish `hmeas : MeasurableSet (coset L x)` using `(coset_isOpen hO x).measurableSet`. Establish `hnon : (coset L x).Nonempty` using `⟨x, by simp [coset, L.zero_mem]⟩`. Establish `hpos : 0 < μ (coset L x)` using `(coset_isOpen hO x).measure_pos μ hnon`.

Establish `hfi : IntegrableOn (fun y => -f y) (coset L x) μ` using `(hf.neg.continuousOn).integrableOn_compact (coset_isCompact hK x)`. Establish `h0 : 0 ≤ᵐ[μ.restrict (coset L x)] fun y => -f y`. Use `(ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun y hy => ?_)` and prove the remaining obligations. Simplify using `using (hneg y hy).le`. Establish `hsup : Function.support (fun y => -f y) ∩ coset L x = coset L x`.

Use `Set.inter_eq_right.2 fun y hy => ?_` and prove the remaining obligations. Simplify using `using (hneg y hy).ne`. Use `(setIntegral_pos_iff_support_of_nonneg_ae h0 hfi).2 (by rw [hsup]; exact hpos)` as an intermediate fact. Rewrite `this` using `[integral_neg]`. Combine the linear relations using `[hi L x hK hO]`.
-/
theorem nonneg_of_cosets {μ : Measure V} [μ.IsAddHaarMeasure] {f : V → ℝ} (hf : Continuous f)
    (hb : ∀ U ∈ 𝓝 (0 : V), ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
      (L : Set V) ⊆ U)
    (hi : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      0 ≤ ∫ x in coset L a, f x ∂μ) (x : V) : 0 ≤ f x := by
  by_contra hx
  push_neg at hx
  have hU : (fun t => f (t + x)) ⁻¹' Set.Iio 0 ∈ 𝓝 (0 : V) :=
    ((isOpen_Iio.preimage (hf.comp (continuous_id.add continuous_const))).mem_nhds (by simpa using hx))
  obtain ⟨L, hK, hO, hLU⟩ := hb _ hU
  have hneg : ∀ y ∈ coset L x, f y < 0 := fun y hy => by
    have := hLU hy
    simpa using this
  have hmeas : MeasurableSet (coset L x) := (coset_isOpen hO x).measurableSet
  have hnon : (coset L x).Nonempty := ⟨x, by simp [coset, L.zero_mem]⟩
  have hpos : 0 < μ (coset L x) := (coset_isOpen hO x).measure_pos μ hnon
  have hfi : IntegrableOn (fun y => -f y) (coset L x) μ :=
    (hf.neg.continuousOn).integrableOn_compact (coset_isCompact hK x)
  have h0 : 0 ≤ᵐ[μ.restrict (coset L x)] fun y => -f y := by
    refine (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun y hy => ?_)
    simpa using (hneg y hy).le
  have hsup : Function.support (fun y => -f y) ∩ coset L x = coset L x := by
    refine Set.inter_eq_right.2 fun y hy => ?_
    simpa using (hneg y hy).ne
  have := (setIntegral_pos_iff_support_of_nonneg_ae h0 hfi).2 (by rw [hsup]; exact hpos)
  rw [integral_neg] at this
  linarith [hi L x hK hO]

end Main

section Ext

variable [IsTopologicalAddGroup V] [T2Space V] [SecondCountableTopology V] [BorelSpace V]

/- English proof (translation)
Set `S : Set (Set V)` to `{C | C = ∅ ∨ ∃ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ C = coset L a}`. Establish `hbasis : TopologicalSpace.IsTopologicalBasis S`. Use `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ (rfl | ⟨L, a, -, hO, rfl⟩)`. Conclude with `isOpen_empty`.

Conclude with `coset_isOpen hO a`. Introduce `a u hau hu`. Establish `hU : (fun t => t + a) ⁻¹' u ∈ 𝓝 (0 : V)` using `(hu.preimage (continuous_id.add continuous_const)).mem_nhds (by simpa using hau)`. Take `⟨L, hK, hO, hLU⟩` from `hb _ hU`. Use `⟨coset L a, Or.inr ⟨L, a, hK, hO, rfl⟩, by simp [coset, L.zero_mem], fun x hx => ?_⟩` and prove the remaining obligations.

Simplify using `using hLU hx`. Establish `hgen : ‹MeasurableSpace V› = MeasurableSpace.generateFrom S` using `(BorelSpace.measurable_eq).trans hbasis.borel_eq_generateFrom`. Establish `hpi : IsPiSystem S`. Introduce and unpack `s hs t ht ⟨c, hcs, hct⟩`. Break down `hs with rfl | ⟨L, a, hK, hO, rfl⟩` into its components or cases.

Simplify using `at hcs`. Break down `ht with rfl | ⟨L', b, hK', hO', rfl⟩` into its components or cases. Simplify using `at hct`. Use `Or.inr ⟨L ⊓ L', c, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.coe_inf]`.

Conclude with `hK.inter_right hK'.isClosed`. Rewrite using `[AddSubgroup.coe_inf]`. Conclude with `hO.inter hO'`. Use extensionality with `x`. Establish `e1 : x - c = (x - a) - (c - a)` using `by abel`.

Establish `e2 : x - c = (x - b) - (c - b)` using `by abel`. Establish `e3 : x - a = (x - c) + (c - a)` using `by abel`. Establish `e4 : x - b = (x - c) + (c - b)` using `by abel`. Establish `hca : c - a ∈ L` using `hcs`. Establish `hcb : c - b ∈ L'` using `hct`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : x - a ∈ L` using `h1`. Establish `h2' : x - b ∈ L'` using `h2`. Conclude with `⟨e1 ▸ L.sub_mem h1' hca, e2 ▸ L'.sub_mem h2' hcb⟩`.

Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : x - c ∈ L` using `h1`. Establish `h2' : x - c ∈ L'` using `h2`. Conclude with `⟨show x - a ∈ L from e3 ▸ L.add_mem h1' hca, show x - b ∈ L' from e4 ▸ L'.add_mem h2' hcb⟩`. Set `T : Set (Set V)` to `{C | ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ C = coset L 0}`.

Take `⟨T', hT'c, hT'T, hT'u⟩` from `TopologicalSpace.isOpen_sUnion_countable T (by`. Introduce and unpack `_ ⟨L, -, hO, rfl⟩`. Conclude with `coset_isOpen hO 0)`. Establish `huniv : ⋃₀ T' = Set.univ`. Rewrite using `[hT'u]`.

Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Take `⟨L, hK, hO, hx⟩` from `hcov x`. Conclude with `⟨coset L 0, ⟨L, hK, hO, rfl⟩, by simpa [coset] using hx⟩`. Establish `hne : T'.Nonempty`. Establish `: (0 : V) ∈ ⋃₀ T'` using `huniv ▸ Set.mem_univ _`.

Take `⟨C, hC, -⟩` from `this`. Conclude with `⟨C, hC⟩`. Take `⟨B, hB⟩` from `hT'c.exists_eq_range hne`. Establish `hBS : ∀ i, B i ∈ S` using `fun i => by`. Take `⟨L, hK, hO, hL⟩` from `hT'T (hB ▸ Set.mem_range_self i : B i ∈ T')`.

Conclude with `Or.inr ⟨L, 0, hK, hO, hL⟩`. Use `MeasureTheory.Measure.ext_of_generateFrom_of_iUnion S B hgen hpi ?_ hBS (fun i => measure_ne_top _ _) ?_` and prove the remaining obligations. Rewrite using `[← Set.sUnion_range, ← hB, huniv]`. Introduce and unpack `_ (rfl | ⟨L, a, hK, hO, rfl⟩)`. Simplify using the standard rewrite rules.

Conclude with `heq L a hK hO`.
-/
theorem eq_of_cosets {m m' : Measure V} [IsFiniteMeasure m]
    (hb : ∀ U ∈ 𝓝 (0 : V), ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
      (L : Set V) ⊆ U)
    (hcov : ∀ x : V, ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ x ∈ L)
    (heq : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      m (coset L a) = m' (coset L a)) : m = m' := by
  let S : Set (Set V) := {C | C = ∅ ∨ ∃ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) ∧
    IsOpen (L : Set V) ∧ C = coset L a}
  have hbasis : TopologicalSpace.IsTopologicalBasis S := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ (rfl | ⟨L, a, -, hO, rfl⟩)
      · exact isOpen_empty
      · exact coset_isOpen hO a
    · intro a u hau hu
      have hU : (fun t => t + a) ⁻¹' u ∈ 𝓝 (0 : V) :=
        (hu.preimage (continuous_id.add continuous_const)).mem_nhds (by simpa using hau)
      obtain ⟨L, hK, hO, hLU⟩ := hb _ hU
      refine ⟨coset L a, Or.inr ⟨L, a, hK, hO, rfl⟩, by simp [coset, L.zero_mem], fun x hx => ?_⟩
      simpa using hLU hx
  have hgen : ‹MeasurableSpace V› = MeasurableSpace.generateFrom S :=
    (BorelSpace.measurable_eq).trans hbasis.borel_eq_generateFrom
  have hpi : IsPiSystem S := by
    rintro s hs t ht ⟨c, hcs, hct⟩
    rcases hs with rfl | ⟨L, a, hK, hO, rfl⟩
    · simp at hcs
    rcases ht with rfl | ⟨L', b, hK', hO', rfl⟩
    · simp at hct
    refine Or.inr ⟨L ⊓ L', c, ?_, ?_, ?_⟩
    · rw [AddSubgroup.coe_inf]
      exact hK.inter_right hK'.isClosed
    · rw [AddSubgroup.coe_inf]
      exact hO.inter hO'
    · ext x
      have e1 : x - c = (x - a) - (c - a) := by abel
      have e2 : x - c = (x - b) - (c - b) := by abel
      have e3 : x - a = (x - c) + (c - a) := by abel
      have e4 : x - b = (x - c) + (c - b) := by abel
      have hca : c - a ∈ L := hcs
      have hcb : c - b ∈ L' := hct
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : x - a ∈ L := h1
        have h2' : x - b ∈ L' := h2
        exact ⟨e1 ▸ L.sub_mem h1' hca, e2 ▸ L'.sub_mem h2' hcb⟩
      · rintro ⟨h1, h2⟩
        have h1' : x - c ∈ L := h1
        have h2' : x - c ∈ L' := h2
        exact ⟨show x - a ∈ L from e3 ▸ L.add_mem h1' hca, show x - b ∈ L' from e4 ▸ L'.add_mem h2' hcb⟩
  let T : Set (Set V) := {C | ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    C = coset L 0}
  obtain ⟨T', hT'c, hT'T, hT'u⟩ := TopologicalSpace.isOpen_sUnion_countable T (by
    rintro _ ⟨L, -, hO, rfl⟩
    exact coset_isOpen hO 0)
  have huniv : ⋃₀ T' = Set.univ := by
    rw [hT'u]
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨L, hK, hO, hx⟩ := hcov x
    exact ⟨coset L 0, ⟨L, hK, hO, rfl⟩, by simpa [coset] using hx⟩
  have hne : T'.Nonempty := by
    have : (0 : V) ∈ ⋃₀ T' := huniv ▸ Set.mem_univ _
    obtain ⟨C, hC, -⟩ := this
    exact ⟨C, hC⟩
  obtain ⟨B, hB⟩ := hT'c.exists_eq_range hne
  have hBS : ∀ i, B i ∈ S := fun i => by
    obtain ⟨L, hK, hO, hL⟩ := hT'T (hB ▸ Set.mem_range_self i : B i ∈ T')
    exact Or.inr ⟨L, 0, hK, hO, hL⟩
  refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion S B hgen hpi ?_ hBS
    (fun i => measure_ne_top _ _) ?_
  · rw [← Set.sUnion_range, ← hB, huniv]
  · rintro _ (rfl | ⟨L, a, hK, hO, rfl⟩)
    · simp
    · exact heq L a hK hO

end Ext

/- English proof (translation)
Introduce `V _ _ _ χ μ h m hm hint`. Take `⟨i1, i2, i3, i4, i5, i6, hb, hcov, hc, hs, hn, ha, -⟩` from `id h`. Establish `hmi : Integrable (mhat χ m) μ` using `hint`. Establish `hG : Continuous (dens χ μ m)` using `dens_continuous hc hn hmi`. Establish `hcos` using `fun (L : AddSubgroup V) (hK : IsCompact (L : Set V)) (hO : IsOpen (L : Set V)) (a : V) => setIntegral_dens h hc hs hn ha hmi hK hO a`.

Establish `hGi : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IntegrableOn (dens χ μ m) (coset L a) μ` using `fun L a hK => hG.continuousOn.integrableOn_compact (coset_isCompact hK a)`. Establish `hrei : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) → ∫ x in coset L a, (dens χ μ m x).re ∂μ = (m (coset L a)).toReal` using `fun L a hK hO => by`. Use `Complex.reCLM.integral_comp_comm (hGi L a hK)` as an intermediate fact. Simplify using `only [Complex.reCLM_apply] at this`. Rewrite using `[this, hcos L hK hO a]`.

Simplify using the standard rewrite rules. Establish `himi : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) → ∫ x in coset L a, (dens χ μ m x).im ∂μ = 0` using `fun L a hK hO => by`. Use `Complex.imCLM.integral_comp_comm (hGi L a hK)` as an intermediate fact. Simplify using `only [Complex.imCLM_apply] at this`. Rewrite using `[this, hcos L hK hO a]`.

Simplify using the standard rewrite rules. Establish `hre : ∀ x, 0 ≤ (dens χ μ m x).re` using `nonneg_of_cosets (μ := μ) (Complex.continuous_re.comp hG) hb fun L a hK hO => by`. Simplify `ENNReal.toReal_nonneg` using `[hrei L a hK hO]`. Establish `him1 : ∀ x, 0 ≤ (dens χ μ m x).im` using `nonneg_of_cosets (μ := μ) (Complex.continuous_im.comp hG) hb fun L a hK hO => by`. Simplify using `[himi L a hK hO]`.

Establish `him2 : ∀ x, 0 ≤ -(dens χ μ m x).im` using `nonneg_of_cosets (μ := μ) (Complex.continuous_im.comp hG).neg hb fun L a hK hO => by`. Simplify using `[integral_neg, himi L a hK hO]`. Establish `hD : Continuous fun x => (dens χ μ m x).re` using `Complex.continuous_re.comp hG`. Establish `hmeq : m = μ.withDensity fun x => ENNReal.ofReal (dens χ μ m x).re`. Use `eq_of_cosets hb hcov fun L a hK hO => ?_` and prove the remaining obligations.

Establish `hmeas : MeasurableSet (coset L a)` using `(coset_isOpen hO a).measurableSet`. Rewrite using `[withDensity_apply _ hmeas, ← ofReal_integral_eq_lintegral_ofReal (hD.continuousOn.integrableOn_compact (coset_isCompact hK a)) (Filter.Eventually.of_forall fun x => hre x), hrei L a hK hO, ENNReal.ofReal_toReal (measure_ne_top _ _)]`. Use `⟨fun x => (dens χ μ m x).re, hD, hre, fun x => ?_, fun U hU => ?_⟩` and prove the remaining obligations. Establish `him : (dens χ μ m x).im = 0` using `le_antisymm (by linarith [him2 x]) (him1 x)`. Express the relevant statement in the definitionally equal form `(((dens χ μ m x).re : ℝ) : ℂ) = dens χ μ m x`.

Conclude with `Complex.ext (by simp) (by simp [him])`. Use `conv_lhs => rw [hmeq]`. Conclude with `withDensity_apply _ hU`.
-/
theorem exists_density : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ (m : Measure V), IsFiniteMeasure m →
    Integrable (fun y => ∫ x, χ x y ∂m) μ → ∃ D : V → ℝ, Continuous D ∧ (∀ x, 0 ≤ D x) ∧
    (∀ x, (D x : ℂ) = ∫ y, (∫ z, χ z y ∂m) * χ (-x) y ∂μ) ∧
    ∀ U : Set V, MeasurableSet U → m U = ∫⁻ x in U, ENNReal.ofReal (D x) ∂μ := by
  intro V _ _ _ χ μ h m hm hint
  obtain ⟨i1, i2, i3, i4, i5, i6, hb, hcov, hc, hs, hn, ha, -⟩ := id h
  have hmi : Integrable (mhat χ m) μ := hint
  have hG : Continuous (dens χ μ m) := dens_continuous hc hn hmi
  have hcos := fun (L : AddSubgroup V) (hK : IsCompact (L : Set V)) (hO : IsOpen (L : Set V)) (a : V) =>
    setIntegral_dens h hc hs hn ha hmi hK hO a
  have hGi : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) →
      IntegrableOn (dens χ μ m) (coset L a) μ := fun L a hK =>
    hG.continuousOn.integrableOn_compact (coset_isCompact hK a)
  have hrei : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      ∫ x in coset L a, (dens χ μ m x).re ∂μ = (m (coset L a)).toReal := fun L a hK hO => by
    have := Complex.reCLM.integral_comp_comm (hGi L a hK)
    simp only [Complex.reCLM_apply] at this
    rw [this, hcos L hK hO a]
    simp
  have himi : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      ∫ x in coset L a, (dens χ μ m x).im ∂μ = 0 := fun L a hK hO => by
    have := Complex.imCLM.integral_comp_comm (hGi L a hK)
    simp only [Complex.imCLM_apply] at this
    rw [this, hcos L hK hO a]
    simp
  have hre : ∀ x, 0 ≤ (dens χ μ m x).re :=
    nonneg_of_cosets (μ := μ) (Complex.continuous_re.comp hG) hb fun L a hK hO => by
      simpa [hrei L a hK hO] using ENNReal.toReal_nonneg
  have him1 : ∀ x, 0 ≤ (dens χ μ m x).im :=
    nonneg_of_cosets (μ := μ) (Complex.continuous_im.comp hG) hb fun L a hK hO => by
      simp [himi L a hK hO]
  have him2 : ∀ x, 0 ≤ -(dens χ μ m x).im :=
    nonneg_of_cosets (μ := μ) (Complex.continuous_im.comp hG).neg hb fun L a hK hO => by
      simp [integral_neg, himi L a hK hO]
  have hD : Continuous fun x => (dens χ μ m x).re := Complex.continuous_re.comp hG
  have hmeq : m = μ.withDensity fun x => ENNReal.ofReal (dens χ μ m x).re := by
    refine eq_of_cosets hb hcov fun L a hK hO => ?_
    have hmeas : MeasurableSet (coset L a) := (coset_isOpen hO a).measurableSet
    rw [withDensity_apply _ hmeas, ← ofReal_integral_eq_lintegral_ofReal
      (hD.continuousOn.integrableOn_compact (coset_isCompact hK a))
      (Filter.Eventually.of_forall fun x => hre x), hrei L a hK hO,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨fun x => (dens χ μ m x).re, hD, hre, fun x => ?_, fun U hU => ?_⟩
  · have him : (dens χ μ m x).im = 0 := le_antisymm (by linarith [him2 x]) (him1 x)
    change (((dens χ μ m x).re : ℝ) : ℂ) = dens χ μ m x
    exact Complex.ext (by simp) (by simp [him])
  · conv_lhs => rw [hmeq]
    exact withDensity_apply _ hU

end GlobalTheory.CompanionTheory.SW.Core.Density
