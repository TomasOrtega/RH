import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.CosetSum

variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

def fib (H : AddSubgroup G) (c : G ⧸ H) : Set G := (QuotientAddGroup.mk : G → G ⧸ H) ⁻¹' {c}

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [fib, mem_preimage, mem_singleton_iff]`. Conclude with `QuotientAddGroup.eq_iff_sub_mem`.
-/
theorem fib_mk (H : AddSubgroup G) (g : G) :
    fib H (g : G ⧸ H) = {x | x - g ∈ H} := by
  ext x
  simp only [fib, mem_preimage, mem_singleton_iff]
  exact QuotientAddGroup.eq_iff_sub_mem

/- English proof (translation)
Take `⟨g, rfl⟩` from `QuotientAddGroup.mk_surjective c`. Rewrite using `[fib_mk]`. Conclude with `hm g`.
-/
theorem fib_meas (H : AddSubgroup G) (hm : ∀ g : G, MeasurableSet {x | x - g ∈ H})
    (c : G ⧸ H) : MeasurableSet (fib H c) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [fib_mk]
  exact hm g

/- English proof (translation)
Take `⟨g, rfl⟩` from `QuotientAddGroup.mk_surjective c`. Establish `hpre : fib H (g : G ⧸ H) = (fun x => -g + x) ⁻¹' (H : Set G)`. Rewrite using `[fib_mk]`. Use extensionality with `x`. Simplify using `[neg_add_eq_sub]`.

Rewrite using `[hpre, measure_preimage_add, h1]`.
-/
theorem fib_measure (ν : Measure G) [ν.IsAddLeftInvariant] (H : AddSubgroup G)
    (h1 : ν (H : Set G) = 1) (c : G ⧸ H) : ν (fib H c) = 1 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hpre : fib H (g : G ⧸ H) = (fun x => -g + x) ⁻¹' (H : Set G) := by
    rw [fib_mk]
    ext x
    simp [neg_add_eq_sub]
  rw [hpre, measure_preimage_add, h1]

/- English proof (translation)
Introduce `_ _ hcd` and use `(Set.disjoint_singleton.mpr hcd).preimage _`.
-/
theorem fib_disj (H : AddSubgroup G) : Pairwise (Function.onFun Disjoint (fib H)) :=
  fun _ _ hcd => (Set.disjoint_singleton.mpr hcd).preimage _

/- English proof (translation)
The claim follows from `eq_univ_of_forall fun x => mem_iUnion.mpr ⟨(x : G ⧸ H), rfl⟩`.
-/
theorem fib_union (H : AddSubgroup G) : ⋃ c, fib H c = univ :=
  eq_univ_of_forall fun x => mem_iUnion.mpr ⟨(x : G ⧸ H), rfl⟩

/- English proof (translation)
Establish `hmeas : Measurable f`. Introduce `s _`. Establish `hs : f ⁻¹' s = ⋃ c ∈ fbar ⁻¹' s, fib H c`. Use extensionality with `x`. Simplify using `[fib, hf]`.

Rewrite using `[hs]`. Conclude with `MeasurableSet.biUnion (to_countable _) fun c _ => fib_meas H hm c`. Establish `hlin : ∫⁻ g, ‖f g‖ₑ ∂ν = ∑' c, ‖fbar c‖ₑ`. Rewrite using `[← setLIntegral_univ, ← fib_union H, lintegral_iUnion (fib_meas H hm) (fib_disj H)]`. Use `tsum_congr fun c => ?_` and prove the remaining obligations.

Rewrite using `[setLIntegral_congr_fun (fib_meas H hm c) (g := fun _ => ‖fbar c‖ₑ), setLIntegral_const, fib_measure ν H h1 c, mul_one]`. Introduce `x hx`. Simplify using `only [fib, mem_preimage, mem_singleton_iff] at hx`. Simplify using `[hf, hx]`. Establish `hiff : (Integrable f ν ↔ Summable fun c => ‖fbar c‖)`.

Rewrite using `[Integrable, hasFiniteIntegral_iff_enorm, hlin]`. Simplify using `only [hmeas.aestronglyMeasurable, true_and]`. Rewrite using `[lt_top_iff_ne_top]`. Simplify using `only [← ofReal_norm]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : (∑' c, ((‖fbar c‖₊ : ℝ≥0) : ℝ≥0∞)) ≠ ⊤`. Simplify `h` using `[ofReal_norm, enorm_eq_nnnorm]`. Use `ENNReal.tsum_coe_ne_top_iff_summable.mp h'` as an intermediate fact. Conclude with `NNReal.summable_coe.mpr this |>.congr fun c => by simp`.

Introduce `h`. Establish `h' : Summable fun c => ‖fbar c‖₊` using `NNReal.summable_coe.mp (by simpa using h)`. Simplify `ENNReal.tsum_coe_ne_top_iff_summable.mpr h'` using `[ofReal_norm, enorm_eq_nnnorm]`. Use `⟨hiff, fun hs => ?_⟩` and prove the remaining obligations. Establish `hint : Integrable f ν` using `hiff.mpr hs`.

Rewrite using `[← setIntegral_univ, ← fib_union H, integral_iUnion (fib_meas H hm) (fib_disj H) hint.integrableOn]`. Use `tsum_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[setIntegral_congr_fun (fib_meas H hm c) (g := fun _ => fbar c), setIntegral_const]`. Simplify using `[Measure.real, fib_measure ν H h1 c]`. Introduce `x hx`.

Simplify using `only [fib, mem_preimage, mem_singleton_iff] at hx`. Simplify using `[hf, hx]`.
-/
theorem integrable_iff_and_integral_eq (G : Type) [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (ν : Measure G) [ν.IsAddLeftInvariant] (H : AddSubgroup G)
    (hm : ∀ g : G, MeasurableSet {x | x - g ∈ H}) (h1 : ν (H : Set G) = 1)
    (hc : Countable (G ⧸ H)) (f : G → ℂ) (fbar : G ⧸ H → ℂ)
    (hf : ∀ g : G, f g = fbar (g : G ⧸ H)) :
    (Integrable f ν ↔ Summable fun c => ‖fbar c‖) ∧
      ((Summable fun c => ‖fbar c‖) → ∫ g, f g ∂ν = ∑' c, fbar c) := by
  have hmeas : Measurable f := by
    intro s _
    have hs : f ⁻¹' s = ⋃ c ∈ fbar ⁻¹' s, fib H c := by
      ext x
      simp [fib, hf]
    rw [hs]
    exact MeasurableSet.biUnion (to_countable _) fun c _ => fib_meas H hm c
  have hlin : ∫⁻ g, ‖f g‖ₑ ∂ν = ∑' c, ‖fbar c‖ₑ := by
    rw [← setLIntegral_univ, ← fib_union H, lintegral_iUnion (fib_meas H hm) (fib_disj H)]
    refine tsum_congr fun c => ?_
    rw [setLIntegral_congr_fun (fib_meas H hm c) (g := fun _ => ‖fbar c‖ₑ), setLIntegral_const,
      fib_measure ν H h1 c, mul_one]
    intro x hx
    simp only [fib, mem_preimage, mem_singleton_iff] at hx
    simp [hf, hx]
  have hiff : (Integrable f ν ↔ Summable fun c => ‖fbar c‖) := by
    rw [Integrable, hasFiniteIntegral_iff_enorm, hlin]
    simp only [hmeas.aestronglyMeasurable, true_and]
    rw [lt_top_iff_ne_top]
    simp only [← ofReal_norm]
    constructor
    · intro h
      have h' : (∑' c, ((‖fbar c‖₊ : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := by
        simpa [ofReal_norm, enorm_eq_nnnorm] using h
      have := ENNReal.tsum_coe_ne_top_iff_summable.mp h'
      exact NNReal.summable_coe.mpr this |>.congr fun c => by simp
    · intro h
      have h' : Summable fun c => ‖fbar c‖₊ := NNReal.summable_coe.mp (by simpa using h)
      simpa [ofReal_norm, enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.mpr h'
  refine ⟨hiff, fun hs => ?_⟩
  have hint : Integrable f ν := hiff.mpr hs
  rw [← setIntegral_univ, ← fib_union H, integral_iUnion (fib_meas H hm) (fib_disj H) hint.integrableOn]
  refine tsum_congr fun c => ?_
  rw [setIntegral_congr_fun (fib_meas H hm c) (g := fun _ => fbar c), setIntegral_const]
  · simp [Measure.real, fib_measure ν H h1 c]
  · intro x hx
    simp only [fib, mem_preimage, mem_singleton_iff] at hx
    simp [hf, hx]

end GlobalTheory.CompanionTheory.CosetSum
