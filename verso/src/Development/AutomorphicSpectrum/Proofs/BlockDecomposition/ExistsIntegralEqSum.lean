import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace GlobalTheory.CompanionTheory.HeckeStabY

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : Finset G, tsupport h ⊆ ⋃ g ∈ t, (fun x => g⁻¹ * x) ⁻¹' (K : Set G) := by`. Use `(show IsCompact (tsupport h) from hc).elim_nhds_subcover (fun g => (fun x => g⁻¹ * x) ⁻¹' (K : Set G)) (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using K.one_mem))` as an intermediate fact. Take `⟨t, -, ht⟩` from `this`. Conclude with `⟨t, ht⟩`. Set `Q : Finset (G ⧸ K)` to `t.image (QuotientGroup.mk : G → G ⧸ K)`.

Use `⟨Q.image Quotient.out, fun F hF hz => ?_⟩` and prove the remaining obligations. Establish `hinj : Set.InjOn (Quotient.out : G ⧸ K → G) (Q : Set (G ⧸ K))` using `fun a _ b _ e => by simpa using congrArg (QuotientGroup.mk : G → G ⧸ K) e`. Rewrite using `[Finset.sum_image hinj]`. Establish `hfib : ∀ q : G ⧸ K, {g : G | (QuotientGroup.mk g : G ⧸ K) = q} = (fun x => (Quotient.out q)⁻¹ * x) ⁻¹' (K : Set G)` using `fun q => by`. Use extensionality with `g`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]`. Rewrite using `[← QuotientGroup.out_eq' q, eq_comm, QuotientGroup.eq]`. Simplify using the standard rewrite rules. Establish `hmeas : ∀ q : G ⧸ K, MeasurableSet {g : G | (QuotientGroup.mk g : G ⧸ K) = q}` using `fun q => by`. Rewrite using `[hfib]`.

Conclude with `(hKo.preimage (continuous_const.mul continuous_id)).measurableSet`. Establish `hvol : ∀ q : G ⧸ K, μ {g : G | (QuotientGroup.mk g : G ⧸ K) = q} = μ (K : Set G)` using `fun q => by`. Rewrite using `[hfib]`. Conclude with `measure_preimage_mul μ _ _`. Establish `hfin : μ (K : Set G) ≠ ⊤` using `hKc.measure_lt_top.ne`.

Establish `hval : ∀ g : G, F g = F (Quotient.out (QuotientGroup.mk g : G ⧸ K))` using `fun g => by`. Establish `hm : (Quotient.out (QuotientGroup.mk g : G ⧸ K))⁻¹ * g ∈ K`. Rewrite using `[← QuotientGroup.eq]`. Simplify using the standard rewrite rules. Establish `e` using `hF (Quotient.out (QuotientGroup.mk g : G ⧸ K)) _ hm`.

Rewrite `e` using `[mul_inv_cancel_left]`. Conclude with `e`. Establish `hsum : ∀ g, F g = ∑ q ∈ Q, ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g`. Introduce `g`. Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq]`.

Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hq`. Conclude with `hval g`. Use `hz g ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `hg : g ∈ tsupport h` using `subset_tsupport h hne`. Take `⟨g₀, hg₀, hm⟩` from `Set.mem_iUnion₂.1 (ht hg)`. Use `hq (Finset.mem_image.2 ⟨g₀, hg₀, ?_⟩)` and prove the remaining obligations. Conclude with `QuotientGroup.eq.2 hm`. Establish `hint : ∀ q ∈ Q, Integrable (({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q))) μ` using `fun q _ => (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hvol]; exact hfin))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (hmeas q), Measure.real, Measure.real, hvol, Complex.real_smul]`.
-/
theorem exists_integral_eq_sum {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (h : G → ℂ) (hc : HasCompactSupport h) :
    ∃ S : Finset G, ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → (∀ g, h g = 0 → F g = 0) →
      ∫ g, F g ∂μ = ((μ.real (K : Set G) : ℝ) : ℂ) * ∑ s ∈ S, F s := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : Finset G, tsupport h ⊆ ⋃ g ∈ t, (fun x => g⁻¹ * x) ⁻¹' (K : Set G) := by
    have := (show IsCompact (tsupport h) from hc).elim_nhds_subcover
      (fun g => (fun x => g⁻¹ * x) ⁻¹' (K : Set G))
      (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds
        (by simpa using K.one_mem))
    obtain ⟨t, -, ht⟩ := this
    exact ⟨t, ht⟩
  let Q : Finset (G ⧸ K) := t.image (QuotientGroup.mk : G → G ⧸ K)
  refine ⟨Q.image Quotient.out, fun F hF hz => ?_⟩
  have hinj : Set.InjOn (Quotient.out : G ⧸ K → G) (Q : Set (G ⧸ K)) :=
    fun a _ b _ e => by simpa using congrArg (QuotientGroup.mk : G → G ⧸ K) e
  rw [Finset.sum_image hinj]
  have hfib : ∀ q : G ⧸ K, {g : G | (QuotientGroup.mk g : G ⧸ K) = q} =
      (fun x => (Quotient.out q)⁻¹ * x) ⁻¹' (K : Set G) := fun q => by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [← QuotientGroup.out_eq' q, eq_comm, QuotientGroup.eq]
    simp
  have hmeas : ∀ q : G ⧸ K, MeasurableSet {g : G | (QuotientGroup.mk g : G ⧸ K) = q} := fun q => by
    rw [hfib]
    exact (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hvol : ∀ q : G ⧸ K, μ {g : G | (QuotientGroup.mk g : G ⧸ K) = q} = μ (K : Set G) := fun q => by
    rw [hfib]
    exact measure_preimage_mul μ _ _
  have hfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hval : ∀ g : G, F g = F (Quotient.out (QuotientGroup.mk g : G ⧸ K)) := fun g => by
    have hm : (Quotient.out (QuotientGroup.mk g : G ⧸ K))⁻¹ * g ∈ K := by
      rw [← QuotientGroup.eq]
      simp
    have e := hF (Quotient.out (QuotientGroup.mk g : G ⧸ K)) _ hm
    rw [mul_inv_cancel_left] at e
    exact e
  have hsum : ∀ g, F g = ∑ q ∈ Q,
      ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g := by
    intro g
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    split_ifs with hq
    · exact hval g
    · refine hz g ?_
      by_contra hne
      have hg : g ∈ tsupport h := subset_tsupport h hne
      obtain ⟨g₀, hg₀, hm⟩ := Set.mem_iUnion₂.1 (ht hg)
      refine hq (Finset.mem_image.2 ⟨g₀, hg₀, ?_⟩)
      exact QuotientGroup.eq.2 hm
  have hint : ∀ q ∈ Q, Integrable
      (({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q))) μ := fun q _ =>
    (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hvol]; exact hfin))
  calc ∫ g, F g ∂μ = ∫ g, ∑ q ∈ Q,
        ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hsum)
    _ = ∑ q ∈ Q, ∫ g,
        ({g : G | (QuotientGroup.mk g : G ⧸ K) = q}).indicator (fun _ => F (Quotient.out q)) g ∂μ :=
        integral_finset_sum Q hint
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hmeas q), Measure.real, Measure.real, hvol, Complex.real_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def transOp (S : Finset (GL (Fin n) (Af E))) (c : GL (Fin n) (Af E) → ℂ) : Module.End ℂ (Sm E n) :=
  ∑ s ∈ S, c s • finRep E n s

end GlobalTheory.CompanionTheory.HeckeStabY

end
