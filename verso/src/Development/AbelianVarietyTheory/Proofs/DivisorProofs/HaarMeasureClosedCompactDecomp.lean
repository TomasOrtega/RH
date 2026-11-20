import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

open MeasureTheory MeasureTheory.Measure Topology Pointwise
open scoped ENNReal NNReal

namespace GlobalTheory.HaarQK

/- English proof (translation)
Rewrite using `[← lintegral_map hf (measurable_mul_const h), map_right_mul_eq_modularCharacterFun_smul, lintegral_smul_measure]`. Both sides reduce to the same expression.
-/
theorem lintegral_mul_right_modular {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] {f : H → ℝ≥0∞} (hf : Measurable f) (h : H) :
    ∫⁻ x, f (x * h) ∂ν = (modularCharacterFun h : ℝ≥0∞) * ∫⁻ x, f x ∂ν := by
  rw [← lintegral_map hf (measurable_mul_const h), map_right_mul_eq_modularCharacterFun_smul,
    lintegral_smul_measure]
  rfl

/- English proof (translation)
The claim follows from `TopologicalSpace.Subtype.secondCountableTopology (Q : Set G)`.
-/
theorem secondCountable_subgroup {G : Type} [Group G] [TopologicalSpace G]
    [SecondCountableTopology G] (Q : Subgroup G) : SecondCountableTopology Q :=
  TopologicalSpace.Subtype.secondCountableTopology (Q : Set G)

attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

/- English proof (translation)
Establish `e1 : ∀ k : K, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν = (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ q, u (q.1 * (k₀ * k).1) ∂ν`. Introduce `k`. Establish `hf : Measurable fun q : Q => u (q.1 * (k₀ * k).1)` using `hu.comp ((continuous_subtype_val.mul continuous_const).measurable)`. Rewrite using `[← lintegral_mul_right_modular ν hf q₀]`. Use `congr 1`.

Use extensionality with `q`. Use `congr 1`. Simplify using `only [Subgroup.coe_mul]`. Use `group`. Repeatedly rewrite using `[e1]`.

Rewrite using `[lintegral_const_mul' _ _ ENNReal.coe_ne_top]`. Use `congr 1`. Conclude with `lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, u (q.1 * k.1) ∂ν) k₀`.
-/
theorem iter_right (u : G → ℝ≥0∞) (hu : Measurable u) (q₀ : Q) (k₀ : K) :
    ∫⁻ k, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν ∂κ =
      (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
  have e1 : ∀ k : K, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν =
      (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ q, u (q.1 * (k₀ * k).1) ∂ν := by
    intro k
    have hf : Measurable fun q : Q => u (q.1 * (k₀ * k).1) :=
      hu.comp ((continuous_subtype_val.mul continuous_const).measurable)
    rw [← lintegral_mul_right_modular ν hf q₀]
    congr 1
    ext q
    congr 1
    simp only [Subgroup.coe_mul]
    group
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  congr 1
  exact lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, u (q.1 * k.1) ∂ν) k₀

/- English proof (translation)
Use `haveI := GlobalTheory.isInvInvariant_of_compactSpace κ`. Establish `e1 : ∀ k : K, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν = ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k⁻¹).1) ∂ν`. Introduce `k`. Use `lintegral_mul_left_eq_self (μ := ν) (fun q : Q => v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹)) q₀` as an intermediate fact. Rewrite using `[← this]`.

Use `congr 1`. Use extensionality with `q`. Use `congr 1`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`.

Repeatedly rewrite using `[e1]`. Establish `e2` using `lintegral_inv_eq_self (μ := κ) (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k).1) ∂ν)`. Rewrite using `[e2]`. Conclude with `lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν) k₀`.
-/
theorem iter_left (v : G → ℝ≥0∞) (q₀ : Q) (k₀ : K) :
    ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν ∂κ =
      ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν ∂κ := by
  haveI := GlobalTheory.isInvInvariant_of_compactSpace κ
  have e1 : ∀ k : K, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν =
      ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k⁻¹).1) ∂ν := by
    intro k
    have := lintegral_mul_left_eq_self
      (μ := ν) (fun q : Q => v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹)) q₀
    rw [← this]
    congr 1
    ext q
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  simp_rw [e1]
  have e2 := lintegral_inv_eq_self (μ := κ) (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k).1) ∂ν)
  rw [e2]
  exact lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν) k₀

end GlobalTheory.HaarQK

namespace GlobalTheory.HaarQK
attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

/- English proof (translation)
Establish `cF : Continuous fun x : G × (Q × K) => (x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹` using `by fun_prop`. Establish `cH : Continuous fun x : G × (Q × K) => x.2.1.1 * x.1 * x.2.2.1` using `by fun_prop`. Establish `mF : Measurable fun x : G × (Q × K) => u x.1 * v ((x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹)` using `(hu.comp measurable_fst).mul (hv.comp cF.measurable)`. Establish `mH : Measurable fun x : G × (Q × K) => u (x.2.1.1 * x.1 * x.2.2.1) * v x.1` using `(hu.comp cH.measurable).mul (hv.comp measurable_fst)`. Establish `mv : ∀ g : G, Measurable fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹)` using `fun g => hv.comp (Continuous.measurable (by fun_prop))`.

Establish `mu : ∀ g : G, Measurable fun p : Q × K => u (p.1.1 * g * p.2.1)` using `fun g => hu.comp (Continuous.measurable (by fun_prop))`. Establish `p1 : ∀ g : G, ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ = ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ)` using `fun g => (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹)) (mv g).aemeasurable).symm`. Establish `p2 : ∀ g : G, ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ = ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ)` using `fun g => (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => u (p.1.1 * g * p.2.1)) (mu g).aemeasurable).symm`. Repeatedly rewrite using `[p1, p2]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use extensionality with `g`. Conclude with `(lintegral_const_mul _ (mv g)).symm`. Use `_ = ∫⁻ p : Q × K, ∫⁻ g, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ ∂(ν.prod κ) := lintegral_lintegral_swap mF.aemeasurable`. Use `_ = ∫⁻ p : Q × K, ∫⁻ g, u (p.1.1 * g * p.2.1) * v g ∂μ ∂(ν.prod κ) := by`.

Use `congr 1`. Use extensionality with `p`. Use `set F : G → ℝ≥0∞ := fun g => u (p.1.1 * g * p.2.1) * v g with hF`. Establish `h1 : ∫⁻ g, F ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ` using `lintegral_mul_left_eq_self (fun g => F (g * (p.2.1)⁻¹)) _`. Establish `h2 : ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F g ∂μ` using `lintegral_mul_right_eq_self F _`.

Rewrite using `[← h2, ← h1]`. Use `congr 1`. Use extensionality with `g`. Simplify using `only [hF]`. Use `congr 1`.

Use `congr 1`. Use `group`. Use `_ = ∫⁻ g, ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) * v g ∂(ν.prod κ) ∂μ := lintegral_lintegral_swap (mH.comp measurable_swap).aemeasurable`. Use `_ = ∫⁻ g, v g * ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) ∂μ := by`. Use `congr 1`.

Use extensionality with `g`. Rewrite using `[lintegral_mul_const _ (mu g), mul_comm]`.
-/
theorem weil_exchange (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (u v : G → ℝ≥0∞) (hu : Measurable u) (hv : Measurable v) :
    ∫⁻ g, u g * ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ ∂μ =
      ∫⁻ g, v g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ := by
  have cF : Continuous fun x : G × (Q × K) => (x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹ := by fun_prop
  have cH : Continuous fun x : G × (Q × K) => x.2.1.1 * x.1 * x.2.2.1 := by fun_prop
  have mF : Measurable fun x : G × (Q × K) => u x.1 * v ((x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹) :=
    (hu.comp measurable_fst).mul (hv.comp cF.measurable)
  have mH : Measurable fun x : G × (Q × K) => u (x.2.1.1 * x.1 * x.2.2.1) * v x.1 :=
    (hu.comp cH.measurable).mul (hv.comp measurable_fst)
  have mv : ∀ g : G, Measurable fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) := fun g =>
    hv.comp (Continuous.measurable (by fun_prop))
  have mu : ∀ g : G, Measurable fun p : Q × K => u (p.1.1 * g * p.2.1) := fun g =>
    hu.comp (Continuous.measurable (by fun_prop))
  have p1 : ∀ g : G, ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ =
      ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) := fun g =>
    (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹))
      (mv g).aemeasurable).symm
  have p2 : ∀ g : G, ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ =
      ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) := fun g =>
    (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => u (p.1.1 * g * p.2.1))
      (mu g).aemeasurable).symm
  simp_rw [p1, p2]
  calc ∫⁻ g, u g * ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) ∂μ
      = ∫⁻ g, ∫⁻ p : Q × K, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) ∂μ := by
        congr 1; ext g
        exact (lintegral_const_mul _ (mv g)).symm
    _ = ∫⁻ p : Q × K, ∫⁻ g, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ ∂(ν.prod κ) :=
        lintegral_lintegral_swap mF.aemeasurable
    _ = ∫⁻ p : Q × K, ∫⁻ g, u (p.1.1 * g * p.2.1) * v g ∂μ ∂(ν.prod κ) := by
        congr 1; ext p
        set F : G → ℝ≥0∞ := fun g => u (p.1.1 * g * p.2.1) * v g with hF
        have h1 : ∫⁻ g, F ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ :=
          lintegral_mul_left_eq_self (fun g => F (g * (p.2.1)⁻¹)) _
        have h2 : ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F g ∂μ := lintegral_mul_right_eq_self F _
        rw [← h2, ← h1]
        congr 1; ext g
        simp only [hF]
        congr 1
        congr 1; group
    _ = ∫⁻ g, ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) * v g ∂(ν.prod κ) ∂μ :=
        lintegral_lintegral_swap (mH.comp measurable_swap).aemeasurable
    _ = ∫⁻ g, v g * ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) ∂μ := by
        congr 1; ext g
        rw [lintegral_mul_const _ (mu g), mul_comm]

end GlobalTheory.HaarQK

namespace GlobalTheory.HaarQK
attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

/- English proof (translation)
Establish `hmeas : Measurable fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p)` using `(measurable_one.indicator hS.measurableSet).comp hm.measurable`. Rewrite using `[← lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p)) hmeas.aemeasurable]`. Establish `e : (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p)) = (m ⁻¹' S).indicator 1`. Apply the tactic sequence `ext p; by_cases hp : m p ∈ S <;> simp [Set.indicator, hp]`. Rewrite using `[e, lintegral_indicator_one (hm.measurable hS.measurableSet)]`.

Prove the components needed by the constructor for the conclusion. Use `(lt_of_lt_of_le ?_ (measure_mono (Set.preimage_mono interior_subset))).ne'` and prove the remaining obligations. Conclude with `(hm.isOpen_preimage _ isOpen_interior).measure_pos (ν.prod κ) ⟨1, h1⟩`. Establish `hcpt : IsCompact ((Subtype.val ⁻¹' C : Set Q) ×ˢ (Set.univ : Set K))` using `(hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hC).prod isCompact_univ`. Use `(lt_of_le_of_lt (measure_mono ?_) hcpt.measure_lt_top).ne` and prove the remaining obligations.

Introduce `p hp`. Conclude with `⟨hmC p hp, trivial⟩`.
-/
theorem iter_indicator_pos_finite (hQ : IsClosed (Q : Set G)) {S : Set G} (hS : IsCompact S)
    (m : Q × K → G) (hm : Continuous m) (h1 : m 1 ∈ interior S) {C : Set G} (hC : IsCompact C)
    (hmC : ∀ p, m p ∈ S → (p.1 : G) ∈ C) :
    ∫⁻ k, ∫⁻ q, S.indicator 1 (m (q, k)) ∂ν ∂κ ≠ 0 ∧
      ∫⁻ k, ∫⁻ q, S.indicator 1 (m (q, k)) ∂ν ∂κ ≠ ⊤ := by
  have hmeas : Measurable fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p) :=
    (measurable_one.indicator hS.measurableSet).comp hm.measurable
  rw [← lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p))
    hmeas.aemeasurable]
  have e : (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p)) = (m ⁻¹' S).indicator 1 := by
    ext p; by_cases hp : m p ∈ S <;> simp [Set.indicator, hp]
  rw [e, lintegral_indicator_one (hm.measurable hS.measurableSet)]
  constructor
  · refine (lt_of_lt_of_le ?_ (measure_mono (Set.preimage_mono interior_subset))).ne'
    exact (hm.isOpen_preimage _ isOpen_interior).measure_pos (ν.prod κ) ⟨1, h1⟩
  · have hcpt : IsCompact ((Subtype.val ⁻¹' C : Set Q) ×ˢ (Set.univ : Set K)) :=
      (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hC).prod isCompact_univ
    refine (lt_of_le_of_lt (measure_mono ?_) hcpt.measure_lt_top).ne
    intro p hp
    exact ⟨hmC p hp, trivial⟩

end GlobalTheory.HaarQK

namespace GlobalTheory

open GlobalTheory.HaarQK in
attribute [local instance] secondCountable_subgroup in

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec ν κ _ _`. Use `haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Take `⟨S, hS, hS1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `hS1' : (1 : G) ∈ interior S` using `mem_interior_iff_mem_nhds.mpr hS1`.

Use `set w : G → ℝ≥0∞ := S.indicator 1 with hw_def`. Establish `hw : Measurable w` using `measurable_one.indicator hS.measurableSet`. Take `⟨hσ0, hσT⟩` from `iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => p.1.1 * p.2.1) (by fun_prop) (by simpa using hS1') (hS.mul hK) (by`. Introduce `p hp`. Establish `: (p.1 : G) = (p.1.1 * p.2.1) * (p.2.1)⁻¹` using `by group`.

Rewrite using `[this]`. Conclude with `Set.mul_mem_mul hp (K.inv_mem p.2.2))`. Take `⟨hE0, hET⟩` from `iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => (p.1.1)⁻¹ * p.2.1) (by fun_prop) (by simpa using hS1') (hK.mul hS.inv) (by`. Introduce `p hp`. Establish `: (p.1 : G) = p.2.1 * ((p.1.1)⁻¹ * p.2.1)⁻¹` using `by group`.

Rewrite using `[this]; exact Set.mul_mem_mul p.2.2 (by simpa using hp))`. Express the relevant statement in the definitionally equal form `∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ 0 at hσ0`. Express the relevant statement in the definitionally equal form `∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ ⊤ at hσT`. Express the relevant statement in the definitionally equal form `∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ 0 at hE0`. Express the relevant statement in the definitionally equal form `∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ ⊤ at hET`.

Use `set σw := ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ with hσw`. Use `set E := ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ with hE`. Establish `hμw0 : ∫⁻ g, w g ∂μ ≠ 0`. Rewrite using `[hw_def, lintegral_indicator_one hS.measurableSet]`. Conclude with `(measure_pos_of_mem_nhds μ hS1).ne'`.

Establish `hμwT : ∫⁻ g, w g ∂μ ≠ ⊤`. Rewrite using `[hw_def, lintegral_indicator_one hS.measurableSet]`. Conclude with `hS.measure_lt_top.ne`. Establish `key1 : ∀ u : G → ℝ≥0∞, Measurable u → (∫⁻ g, u g ∂μ) * E = ∫⁻ g, w g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ`. Introduce `u hu`.

Rewrite using `[← weil_exchange ν κ μ u w hu hw, ← lintegral_mul_const _ hu]`. Use `congr 1`. Use extensionality with `g`. Take `⟨q₀, hq₀, k₀, hk₀, rfl⟩` from `hdec g`. Rewrite using `[iter_left ν κ w ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]`.

Establish `key2 : ∀ u : G → ℝ≥0∞, Measurable u → ∀ g : G, (∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ) * σw = (∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ`. Introduce `u hu g`. Take `⟨q₀, hq₀, k₀, hk₀, rfl⟩` from `hdec g`. Rewrite using `[iter_right ν κ u hu ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩, iter_right ν κ w hw ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]`. Expand and normalize the polynomial expressions, which then agree.

Establish `mA : Measurable fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ`. Establish `mf : Measurable fun x : G × (Q × K) => w (x.2.1.1 * x.1 * x.2.2.1)` using `hw.comp (Continuous.measurable (by fun_prop))`. Establish `e : (fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) = fun g => ∫⁻ p : Q × K, w (p.1.1 * g * p.2.1) ∂(ν.prod κ)`. Use function extensionality and compare the values at `g`. Conclude with `(lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => w (p.1.1 * g * p.2.1)) (mf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm`.

Rewrite using `[e]`. Conclude with `mf.lintegral_prod_right'`. Establish `key : ∀ u : G → ℝ≥0∞, Measurable u → (∫⁻ g, u g ∂μ) * σw = (∫⁻ g, w g ∂μ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ`. Introduce `u hu`. Establish `mwA : Measurable fun g => w g * ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ` using `hw.mul mA`.

Establish `h : (∫⁻ g, u g ∂μ) * E * σw = (∫⁻ g, w g ∂μ) * E * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ`. Rewrite using `[key1 u hu, key1 w hw, ← lintegral_mul_const' _ _ hσT, ← lintegral_mul_const _ mwA]`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[mul_assoc, key2 u hu g, ← mul_assoc]`.

Rewrite `h` using `[mul_right_comm, mul_right_comm (∫⁻ g, w g ∂μ)]`. Conclude with `(ENNReal.mul_left_inj hE0 hET).mp h`. Use `⟨(∫⁻ g, w g ∂μ) / σw, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `ENNReal.div_ne_zero.mpr ⟨hμw0, hσT⟩`. Conclude with `ENNReal.div_ne_top hμwT hσ0`.

Introduce `φ hφ`. Rewrite using `[← ENNReal.mul_div_cancel_right (a := ∫⁻ g, φ g ∂μ) hσ0 hσT, key φ hφ, ENNReal.mul_div_right_comm]`.
-/
theorem lintegral_haar_eq_mul_iterated_closed_compact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Q K : Subgroup G), IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) →
    ∀ (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ φ : G → ENNReal, Measurable φ → ∫⁻ g, φ g ∂μ = c * ∫⁻ k, ∫⁻ q, φ (q.1 * k.1) ∂ν ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec ν κ _ _
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨S, hS, hS1⟩ := exists_compact_mem_nhds (1 : G)
  have hS1' : (1 : G) ∈ interior S := mem_interior_iff_mem_nhds.mpr hS1
  set w : G → ℝ≥0∞ := S.indicator 1 with hw_def
  have hw : Measurable w := measurable_one.indicator hS.measurableSet

  obtain ⟨hσ0, hσT⟩ := iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => p.1.1 * p.2.1)
    (by fun_prop) (by simpa using hS1') (hS.mul hK) (by
      intro p hp
      have : (p.1 : G) = (p.1.1 * p.2.1) * (p.2.1)⁻¹ := by group
      rw [this]; exact Set.mul_mem_mul hp (K.inv_mem p.2.2))

  obtain ⟨hE0, hET⟩ := iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => (p.1.1)⁻¹ * p.2.1)
    (by fun_prop) (by simpa using hS1') (hK.mul hS.inv) (by
      intro p hp
      have : (p.1 : G) = p.2.1 * ((p.1.1)⁻¹ * p.2.1)⁻¹ := by group
      rw [this]; exact Set.mul_mem_mul p.2.2 (by simpa using hp))
  change ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ 0 at hσ0
  change ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ ⊤ at hσT
  change ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ 0 at hE0
  change ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ ⊤ at hET
  set σw := ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ with hσw
  set E := ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ with hE
  have hμw0 : ∫⁻ g, w g ∂μ ≠ 0 := by
    rw [hw_def, lintegral_indicator_one hS.measurableSet]
    exact (measure_pos_of_mem_nhds μ hS1).ne'
  have hμwT : ∫⁻ g, w g ∂μ ≠ ⊤ := by
    rw [hw_def, lintegral_indicator_one hS.measurableSet]
    exact hS.measure_lt_top.ne

  have key1 : ∀ u : G → ℝ≥0∞, Measurable u →
      (∫⁻ g, u g ∂μ) * E = ∫⁻ g, w g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ := by
    intro u hu
    rw [← weil_exchange ν κ μ u w hu hw, ← lintegral_mul_const _ hu]
    congr 1; ext g
    obtain ⟨q₀, hq₀, k₀, hk₀, rfl⟩ := hdec g
    rw [iter_left ν κ w ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]
  have key2 : ∀ u : G → ℝ≥0∞, Measurable u → ∀ g : G,
      (∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ) * σw =
        (∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
    intro u hu g
    obtain ⟨q₀, hq₀, k₀, hk₀, rfl⟩ := hdec g
    rw [iter_right ν κ u hu ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩, iter_right ν κ w hw ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]
    ring
  have mA : Measurable fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ := by
    have mf : Measurable fun x : G × (Q × K) => w (x.2.1.1 * x.1 * x.2.2.1) :=
      hw.comp (Continuous.measurable (by fun_prop))
    have e : (fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) =
        fun g => ∫⁻ p : Q × K, w (p.1.1 * g * p.2.1) ∂(ν.prod κ) := by
      funext g
      exact (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => w (p.1.1 * g * p.2.1))
        (mf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    rw [e]
    exact mf.lintegral_prod_right'
  have key : ∀ u : G → ℝ≥0∞, Measurable u →
      (∫⁻ g, u g ∂μ) * σw = (∫⁻ g, w g ∂μ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
    intro u hu
    have mwA : Measurable fun g => w g * ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ := hw.mul mA
    have h : (∫⁻ g, u g ∂μ) * E * σw = (∫⁻ g, w g ∂μ) * E * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
      rw [key1 u hu, key1 w hw, ← lintegral_mul_const' _ _ hσT,
        ← lintegral_mul_const _ mwA]
      congr 1; ext g
      rw [mul_assoc, key2 u hu g, ← mul_assoc]
    rw [mul_right_comm, mul_right_comm (∫⁻ g, w g ∂μ)] at h
    exact (ENNReal.mul_left_inj hE0 hET).mp h
  refine ⟨(∫⁻ g, w g ∂μ) / σw, ?_, ?_, ?_⟩
  · exact ENNReal.div_ne_zero.mpr ⟨hμw0, hσT⟩
  · exact ENNReal.div_ne_top hμwT hσ0
  · intro φ hφ
    rw [← ENNReal.mul_div_cancel_right (a := ∫⁻ g, φ g ∂μ) hσ0 hσT, key φ hφ, ENNReal.mul_div_right_comm]

end GlobalTheory
