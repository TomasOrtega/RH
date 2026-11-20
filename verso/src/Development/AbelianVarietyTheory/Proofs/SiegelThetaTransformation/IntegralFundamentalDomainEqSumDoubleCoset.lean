import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

section DoubleCoset
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in

/- English proof (translation)
Establish `hunion : {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} = ⋃ γ ∈ Γ, (fun k => γ * a * k) '' (K : Set G)`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hγ, k, hk, rfl⟩`.

Conclude with `⟨γ, hγ, k, hk, rfl⟩`. Introduce and unpack `⟨γ, hγ, k, hk, rfl⟩`. Conclude with `⟨γ, hγ, k, hk, rfl⟩`. Rewrite using `[hunion]`. Conclude with `isOpen_biUnion fun γ _ => isOpenMap_mul_left (γ * a) _ hK`.
-/
theorem _root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen (Γ K : Subgroup G) (hK : IsOpen (K : Set G)) (a : G) :
    IsOpen {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} := by
  have hunion : {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} =
      ⋃ γ ∈ Γ, (fun k => γ * a * k) '' (K : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
  rw [hunion]
  exact isOpen_biUnion fun γ _ => isOpenMap_mul_left (γ * a) _ hK

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
omit [TopologicalSpace G] [IsTopologicalGroup G] in

/- English proof (translation)
Distinguish the cases in `hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}`. Rewrite using `[Set.indicator_of_mem hx, Pi.one_apply, mul_one]`. Take `⟨γ₀, hγ₀, k₀, hk₀, rfl⟩` from `hx`. Use `set T : Set Γ := {γ | a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K} with hT`. Establish `hterm : ∀ γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • (γ₀ * a * k₀)) = T.indicator (1 : Γ → ENNReal) γ`.

Introduce `γ`. Distinguish the cases in `hγ : γ ∈ T`. Rewrite using `[Set.indicator_of_mem hγ, Set.indicator_of_mem]`. Both sides reduce to the same expression. Conclude with `hγ`.

Rewrite using `[Set.indicator_of_notMem hγ, Set.indicator_of_notMem]`. Conclude with `hγ`. Repeatedly rewrite using `[hterm]`. Rewrite using `[← tsum_subtype T (1 : Γ → ENNReal)]`. Simplify using `only [Pi.one_apply]`.

Rewrite using `[ENNReal.tsum_set_one]`. Establish `hinj : Function.Injective (fun γ : Γ => (γ : G) * γ₀)` using `fun γ δ hγδ => Subtype.ext (mul_right_cancel hγδ)`. Establish `himg : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K} = (fun γ : Γ => (γ : G) * γ₀) '' T`. Use extensionality with `δ`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hδ, hδK⟩`. Use `⟨⟨δ * γ₀⁻¹, Γ.mul_mem hδ (Γ.inv_mem hγ₀)⟩, ?_, by simp⟩` and prove the remaining obligations. Use `show a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) ∈ K`. Establish `heq : a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) = a⁻¹ * δ * a * k₀` using `by group`. Rewrite using `[heq]`.

Conclude with `K.mul_mem hδK hk₀`. Introduce and unpack `⟨γ, hγ, rfl⟩`. Use `⟨Γ.mul_mem γ.2 hγ₀, ?_⟩` and prove the remaining obligations. Establish `hγ' : a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K` using `hγ`. Establish `heq : a⁻¹ * ((γ : G) * γ₀) * a = a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) * k₀⁻¹` using `by group`.

Rewrite using `[heq]`. Conclude with `K.mul_mem hγ' (K.inv_mem hk₀)`. Rewrite using `[← hinj.encard_image, ← himg, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]`. Rewrite using `[Set.indicator_of_notMem hx, mul_zero]`. Use `ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem ?_ _` and prove the remaining obligations.

Introduce `hmem`. Establish `hk : a⁻¹ * ((γ : G) * x) ∈ K` using `hmem`. Conclude with `hx ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hk, by group⟩`.
-/
theorem _root_.GlobalTheory.Ker.tsum_indicator_coset (Γ K : Subgroup G) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (x : G) :
    ∑' γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x)
      = ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) *
        {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}.indicator 1 x := by
  by_cases hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨γ₀, hγ₀, k₀, hk₀, rfl⟩ := hx
    set T : Set Γ := {γ | a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K} with hT
    have hterm : ∀ γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)
        (γ • (γ₀ * a * k₀)) = T.indicator (1 : Γ → ENNReal) γ := by
      intro γ
      by_cases hγ : γ ∈ T
      · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem]
        · rfl
        · exact hγ
      · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem]
        exact hγ
    simp_rw [hterm]
    rw [← tsum_subtype T (1 : Γ → ENNReal)]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hinj : Function.Injective (fun γ : Γ => (γ : G) * γ₀) :=
      fun γ δ hγδ => Subtype.ext (mul_right_cancel hγδ)
    have himg : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K} = (fun γ : Γ => (γ : G) * γ₀) '' T := by
      ext δ
      constructor
      · rintro ⟨hδ, hδK⟩
        refine ⟨⟨δ * γ₀⁻¹, Γ.mul_mem hδ (Γ.inv_mem hγ₀)⟩, ?_, by simp⟩
        show a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) ∈ K
        have heq : a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) = a⁻¹ * δ * a * k₀ := by group
        rw [heq]
        exact K.mul_mem hδK hk₀
      · rintro ⟨γ, hγ, rfl⟩
        refine ⟨Γ.mul_mem γ.2 hγ₀, ?_⟩
        have hγ' : a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K := hγ
        have heq : a⁻¹ * ((γ : G) * γ₀) * a = a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) * k₀⁻¹ := by group
        rw [heq]
        exact K.mul_mem hγ' (K.inv_mem hk₀)
    rw [← hinj.encard_image, ← himg, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem ?_ _
    intro hmem
    have hk : a⁻¹ * ((γ : G) * x) ∈ K := hmem
    exact hx ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hk, by group⟩

variable [MeasurableSpace G] [BorelSpace G]

end DoubleCoset

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
/- English proof (translation)
Establish `hC : MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}` using `(_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet`. Establish `hmeasK : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' (K : Set G))` using `hK.measurableSet.preimage (measurable_const_mul _)`. Establish `hwhole : ∫⁻ x, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator 1 x ∂ν = ν K`. Rewrite using `[lintegral_indicator_one hmeasK, measure_preimage_mul]`. Establish `hinv` using `(Equiv.inv Γ).tsum_eq (fun γ : Γ => ∫⁻ x in D, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ⁻¹ • x) ∂ν)`.

Simplify using `only [Equiv.inv_apply, inv_inv] at hinv`. Rewrite using `[← hwhole, hD.lintegral_eq_tsum', ← hinv, ← lintegral_tsum]`. Repeatedly rewrite using `[_root_.GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin]`. Rewrite using `[lintegral_const_mul _ (measurable_one.indicator hC), lintegral_indicator_one hC, Measure.restrict_apply hC, mul_comm]`. Introduce `γ`.

Conclude with `((measurable_one.indicator hmeasK).comp (measurable_const_smul γ)).aemeasurable`.
-/
private theorem measure_fd_inter_doubleCoset_mul_ncard_eq {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (D : Set G)
    (hD : IsFundamentalDomain Γ D ν) (hK : IsOpen (K : Set G)) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) :
    ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} ∩ D) *
      ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) = ν K := by
  have hC : MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} :=
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet
  have hmeasK : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)) :=
    hK.measurableSet.preimage (measurable_const_mul _)
  have hwhole : ∫⁻ x, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator 1 x ∂ν = ν K := by
    rw [lintegral_indicator_one hmeasK, measure_preimage_mul]
  have hinv := (Equiv.inv Γ).tsum_eq (fun γ : Γ =>
    ∫⁻ x in D, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ⁻¹ • x) ∂ν)
  simp only [Equiv.inv_apply, inv_inv] at hinv
  rw [← hwhole, hD.lintegral_eq_tsum', ← hinv, ← lintegral_tsum]
  · simp_rw [_root_.GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin]
    rw [lintegral_const_mul _ (measurable_one.indicator hC), lintegral_indicator_one hC,
      Measure.restrict_apply hC, mul_comm]
  · intro γ
    exact ((measurable_one.indicator hmeasK).comp (measurable_const_smul γ)).aemeasurable

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in

/- English proof (translation)
Introduce `G _ _ _ _ _ ν _ Γ K _ 𝓖 h𝓖 hK hKtop ι _ h huniq hfin F hFΓ hFK`. Establish `hCmeas : ∀ i, MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}` using `fun i => (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK (h i)).measurableSet`. Establish `hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard ≠ 0` using `fun i => ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simpa using K.one_mem⟩).ne'`. Establish `hCG : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) = ν K / ({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ENNReal)`. Introduce `i`.

Rewrite using `[ENNReal.eq_div_iff (by exact_mod_cast hpos i) (ENNReal.natCast_ne_top _), mul_comm]`. Conclude with `measure_fd_inter_doubleCoset_mul_ncard_eq ν Γ K 𝓖 h𝓖 hK (h i) (hfin i)`. Establish `hCGtop : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) ≠ ⊤`. Introduce `i`. Rewrite using `[hCG i]`.

Conclude with `(ENNReal.div_lt_top hKtop (by exact_mod_cast hpos i)).ne`. Establish `h𝓖top : ν 𝓖 ≠ ⊤`. Establish `hsub : 𝓖 ⊆ ⋃ i, ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖)` using `fun x hx => Set.mem_iUnion.2 ⟨(huniq x).exists.choose, (huniq x).exists.choose_spec, hx⟩`. Use `ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (measure_iUnion_fintype_le _ _))` and prove the remaining obligations. Conclude with `ENNReal.sum_ne_top.2 fun i _ => hCGtop i`.

Establish `hdecomp : ∀ x, F x = ∑ i, {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i)) x`. Introduce `x`. Take `⟨i, hi, hiuniq⟩` from `huniq x`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} from hi)]`.

Take `⟨γ, hγ, k, hk, rfl⟩` from `hi`. Rewrite using `[hFK k hk, hFΓ γ hγ]`. Introduce `j _ hj`. Conclude with `Set.indicator_of_notMem (show x ∉ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h j * k} from fun hx => hj (hiuniq j hx)) _`. Introduce `hi'`.

Conclude with `absurd (Finset.mem_univ i) hi'`. Establish `hint : ∀ i, IntegrableOn ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i))) 𝓖 ν`. Introduce `i`. Use `(integrable_indicator_iff (hCmeas i)).2 ?_` and prove the remaining obligations. Use `integrableOn_const ?_` and prove the remaining obligations.

Rewrite using `[Measure.restrict_apply (hCmeas i)]`. Conclude with `hCGtop i`. Use `⟨h𝓖top, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(integrable_finset_sum _ fun i _ => hint i).congr (ae_of_all _ fun x => (hdecomp x).symm)`. Use `(congrArg (fun f : G → ℂ => ∫ x in 𝓖, f x ∂ν) (funext hdecomp)).trans ?_` and prove the remaining obligations.

Rewrite using `[integral_finset_sum _ fun i _ => hint i, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (hCmeas i), measureReal_def, Measure.restrict_apply (hCmeas i), hCG i, ENNReal.toReal_div, ENNReal.toReal_natCast, Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (K : Set G) → ν K ≠ ⊤ → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) → ∀ F : G → ℂ, (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) → ν 𝓖 ≠ ⊤ ∧ IntegrableOn F 𝓖 ν ∧ ∫ x in 𝓖, F x ∂ν = ((ν K).toReal : ℂ) * ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * F (h i) := by
  intro G _ _ _ _ _ ν _ Γ K _ 𝓖 h𝓖 hK hKtop ι _ h huniq hfin F hFΓ hFK
  have hCmeas : ∀ i, MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} := fun i =>
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK (h i)).measurableSet
  have hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard ≠ 0 := fun i =>
    ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simpa using K.one_mem⟩).ne'
  have hCG : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) =
      ν K / ({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ENNReal) := by
    intro i
    rw [ENNReal.eq_div_iff (by exact_mod_cast hpos i) (ENNReal.natCast_ne_top _), mul_comm]
    exact measure_fd_inter_doubleCoset_mul_ncard_eq ν Γ K 𝓖 h𝓖 hK (h i) (hfin i)
  have hCGtop : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) ≠ ⊤ := by
    intro i
    rw [hCG i]
    exact (ENNReal.div_lt_top hKtop (by exact_mod_cast hpos i)).ne
  have h𝓖top : ν 𝓖 ≠ ⊤ := by
    have hsub : 𝓖 ⊆ ⋃ i, ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) := fun x hx =>
      Set.mem_iUnion.2 ⟨(huniq x).exists.choose, (huniq x).exists.choose_spec, hx⟩
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (measure_iUnion_fintype_le _ _))
    exact ENNReal.sum_ne_top.2 fun i _ => hCGtop i
  have hdecomp : ∀ x, F x =
      ∑ i, {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i)) x := by
    intro x
    obtain ⟨i, hi, hiuniq⟩ := huniq x
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} from hi)]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hi
      rw [hFK k hk, hFΓ γ hγ]
    · intro j _ hj
      exact Set.indicator_of_notMem
        (show x ∉ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h j * k} from fun hx => hj (hiuniq j hx)) _
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  have hint : ∀ i, IntegrableOn
      ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i))) 𝓖 ν := by
    intro i
    refine (integrable_indicator_iff (hCmeas i)).2 ?_
    refine integrableOn_const ?_
    rw [Measure.restrict_apply (hCmeas i)]
    exact hCGtop i
  refine ⟨h𝓖top, ?_, ?_⟩
  · exact (integrable_finset_sum _ fun i _ => hint i).congr
      (ae_of_all _ fun x => (hdecomp x).symm)
  · refine (congrArg (fun f : G → ℂ => ∫ x in 𝓖, f x ∂ν) (funext hdecomp)).trans ?_
    rw [integral_finset_sum _ fun i _ => hint i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (hCmeas i), measureReal_def, Measure.restrict_apply (hCmeas i),
      hCG i, ENNReal.toReal_div, ENNReal.toReal_natCast, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.Ker
