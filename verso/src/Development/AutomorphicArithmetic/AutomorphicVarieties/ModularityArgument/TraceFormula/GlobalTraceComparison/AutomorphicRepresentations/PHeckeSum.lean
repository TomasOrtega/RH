import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT PositivityTheory.Rg.BcB
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Set `c : G ⧸ K → Set G` to `fun q => {y | q.out⁻¹ * y ∈ K}`. Establish `hcm : ∀ q y, y ∈ c q ↔ (QuotientGroup.mk y : G ⧸ K) = q`. Introduce `q y`. Express the relevant statement in the definitionally equal form `q.out⁻¹ * y ∈ K ↔ _`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq']`.

Conclude with `eq_comm`. Establish `hco : ∀ q, IsOpen (c q)` using `fun q => hK.preimage (continuous_const.mul continuous_id)`. Establish `hmeas : ∀ q, μ (c q) = μ (K : Set G)` using `fun q => measure_preimage_mul μ q.out⁻¹ (K : Set G)`. Take `⟨t, -, ht⟩` from `hc.isCompact.elim_nhds_subcover (fun g => c (QuotientGroup.mk g)) (fun g _ => (hco _).mem_nhds ((hcm _ g).2 rfl))`. Set `T : Finset (G ⧸ K)` to `t.image fun g => (QuotientGroup.mk g : G ⧸ K)`.

Establish `hT : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ K) ∈ T`. Introduce `y hy`. Take `⟨g, hg, hyg⟩` from `Set.mem_iUnion₂.1 (ht (subset_tsupport h hy))`. Rewrite using `[(hcm _ y).1 hyg]`. Conclude with `Finset.mem_image_of_mem _ hg`.

Use `⟨T, fun q hq => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Simplify `hT _ hq` using `[QuotientGroup.out_eq']`. Establish `hval : ∀ q y, y ∈ c q → h y * f y = h q.out * f q.out`. Introduce `q y hy`. Establish `e : y = q.out * (q.out⁻¹ * y)` using `by group`.

Rewrite using `[e, hinv _ _ hy, hf _ _ hy]`. Establish `hsum : (fun y => h y * f y) = fun y => ∑ q ∈ T, (c q).indicator (fun _ => h q.out * f q.out) y`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : (QuotientGroup.mk y : G ⧸ K) ∈ T`. Establish `hyc : y ∈ c (QuotientGroup.mk y)` using `(hcm _ y).2 rfl`.

Rewrite using `[Finset.sum_eq_single (QuotientGroup.mk y : G ⧸ K), Set.indicator_of_mem hyc, hval _ y hyc]`. Introduce `q _ hq`. Conclude with `Set.indicator_of_notMem (fun hyq => hq ((hcm q y).1 hyq).symm) _`. Conclude with `fun h' => (h' hy).elim`. Establish `hy0 : h y = 0`.

Assume the negation of the conclusion as `h'`. Conclude with `hy (hT y h')`. Rewrite using `[hy0, zero_mul]`. Use `(Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (fun hyq => hy ?_) _).symm` and prove the remaining obligations. Rewrite using `[(hcm q y).1 hyq]` and apply the resulting hypothesis.

Rewrite using `[hsum, integral_finset_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (hco q).measurableSet]`. Simplify using `only [Measure.real, hmeas q, Complex.real_smul]`. Introduce `q _`.

Use `(integrable_indicator_iff (hco q).measurableSet).2 ?_` and prove the remaining obligations. Conclude with `integrableOn_const (by rw [hmeas q]; exact hfin)`.
-/
private theorem coset_integral (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G} (hK : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ K, h (g * k) = h g) :
    ∃ T : Finset (G ⧸ K), (∀ q : G ⧸ K, h q.out ≠ 0 → q ∈ T) ∧ ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ q ∈ T, (μ.real (K : Set G) : ℂ) * (h q.out * f q.out) := by
  let c : G ⧸ K → Set G := fun q => {y | q.out⁻¹ * y ∈ K}
  have hcm : ∀ q y, y ∈ c q ↔ (QuotientGroup.mk y : G ⧸ K) = q := by
    intro q y
    change q.out⁻¹ * y ∈ K ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hco : ∀ q, IsOpen (c q) := fun q => hK.preimage (continuous_const.mul continuous_id)
  have hmeas : ∀ q, μ (c q) = μ (K : Set G) := fun q => measure_preimage_mul μ q.out⁻¹ (K : Set G)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun g => c (QuotientGroup.mk g))
    (fun g _ => (hco _).mem_nhds ((hcm _ g).2 rfl))
  let T : Finset (G ⧸ K) := t.image fun g => (QuotientGroup.mk g : G ⧸ K)
  have hT : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ K) ∈ T := by
    intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport h hy))
    rw [(hcm _ y).1 hyg]
    exact Finset.mem_image_of_mem _ hg
  refine ⟨T, fun q hq => ?_, fun f hf => ?_⟩
  · simpa [QuotientGroup.out_eq'] using hT _ hq
  have hval : ∀ q y, y ∈ c q → h y * f y = h q.out * f q.out := by
    intro q y hy
    have e : y = q.out * (q.out⁻¹ * y) := by group
    rw [e, hinv _ _ hy, hf _ _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ q ∈ T, (c q).indicator (fun _ => h q.out * f q.out) y := by
    funext y
    by_cases hy : (QuotientGroup.mk y : G ⧸ K) ∈ T
    · have hyc : y ∈ c (QuotientGroup.mk y) := (hcm _ y).2 rfl
      rw [Finset.sum_eq_single (QuotientGroup.mk y : G ⧸ K), Set.indicator_of_mem hyc, hval _ y hyc]
      · intro q _ hq
        exact Set.indicator_of_notMem (fun hyq => hq ((hcm q y).1 hyq).symm) _
      · exact fun h' => (h' hy).elim
    · have hy0 : h y = 0 := by
        by_contra h'
        exact hy (hT y h')
      rw [hy0, zero_mul]
      refine (Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (fun hyq => hy ?_) _).symm
      rwa [(hcm q y).1 hyq]
  rw [hsum, integral_finset_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hco q).measurableSet]
    simp only [Measure.real, hmeas q, Complex.real_smul]
  · intro q _
    refine (integrable_indicator_iff (hco q).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas q]; exact hfin)

end Abs

/- English proof (translation)
Introduce `E _ _ _ n K hKo hKc μf _ h hh y hy`. Establish `hfix : ∀ k ∈ K, finRep E n k y = y` using `fun k hk => by`. Simplify using `using hy ⟨k, hk⟩`. Take `⟨T, hT, hI⟩` from `coset_integral μf hKo hKc.measure_lt_top.ne hh.1 (fun g k hk => (hh.2 k hk g).2)`. Use function extensionality and compare the values at `x`.

Establish `hf` using `hI (fun g => y.1 (x * finGL E n g)) (fun g k hk => by`. Establish `e` using `congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hfix k hk)`. Establish `e' : y.1 (x * finGL E n g * finGL E n k) = y.1 (x * finGL E n g)` using `e`. Simplify `e')` using `[mul_assoc]`. Establish `hL : Lv (finRep E n) K h = ∑ q ∈ T, h q.out • finRep E n q.out`.

Establish `hs : (Function.support fun q : GF E n ⧸ K => h q.out • (finRep E n q.out ∘ₗ LinearMap.id)) ⊆ T`. Introduce `q hq`. Use `hT q fun h0 => hq ?_` and prove the remaining obligations. Simplify using `[h0]`. Simplify using `only [Lv, levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]`.

Rewrite using `[finsum_eq_sum_of_support_subset _ hs]`. Both sides reduce to the same expression. Establish `hv : (∑ q ∈ T, (h q.out • finRep E n q.out) y : Sm E n).1 x = ∑ q ∈ T, h q.out * y.1 (x * finGL E n q.out)`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Both sides reduce to the same expression.

Rewrite using `[hL, heckeOp, hf, LinearMap.sum_apply, hv, Finset.mul_sum]`. Both sides reduce to the same expression.
-/
theorem heckeSum_pf : HeckeSum := by
  intro E _ _ _ n K hKo hKc μf _ h hh y hy
  have hfix : ∀ k ∈ K, finRep E n k y = y := fun k hk => by
    simpa using hy ⟨k, hk⟩
  obtain ⟨T, hT, hI⟩ := coset_integral μf hKo hKc.measure_lt_top.ne hh.1 (fun g k hk => (hh.2 k hk g).2)
  funext x
  have hf := hI (fun g => y.1 (x * finGL E n g)) (fun g k hk => by
    have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hfix k hk)
    have e' : y.1 (x * finGL E n g * finGL E n k) = y.1 (x * finGL E n g) := e
    simpa [mul_assoc] using e')
  have hL : Lv (finRep E n) K h = ∑ q ∈ T, h q.out • finRep E n q.out := by
    have hs : (Function.support fun q : GF E n ⧸ K => h q.out • (finRep E n q.out ∘ₗ LinearMap.id)) ⊆ T := by
      intro q hq
      refine hT q fun h0 => hq ?_
      simp [h0]
    simp only [Lv, levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    rw [finsum_eq_sum_of_support_subset _ hs]
    rfl
  have hv : (∑ q ∈ T, (h q.out • finRep E n q.out) y : Sm E n).1 x =
      ∑ q ∈ T, h q.out * y.1 (x * finGL E n q.out) := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hL, heckeOp, hf, LinearMap.sum_apply, hv, Finset.mul_sum]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
