import Formalism.SuccessiveMinima.DefsMink

open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN
namespace GjScaling

def Zv (ι : Type*) : Set (ι → ℝ) := {k | ∀ i, ∃ m : ℤ, k i = m}

def Qv (ι : Type*) : Set (ι → ℝ) := {u | ∀ i, 0 ≤ u i ∧ u i < 1}

def tm {ι : Type*} [Fintype ι] (B : Set (ι → ℝ)) : ℝ≥0∞ := volume (Qv ι ∩ (B + Zv ι))

variable {ι : Type*} [Fintype ι]

/- English proof (translation)
Unfold `tm`. Conclude with `measure_mono (Set.inter_subset_inter subset_rfl (Set.add_subset_add h subset_rfl))`.
-/
lemma tm_mono {B B' : Set (ι → ℝ)} (h : B ⊆ B') : tm B ≤ tm B' := by
  unfold tm
  exact measure_mono (Set.inter_subset_inter subset_rfl (Set.add_subset_add h subset_rfl))

/- English proof (translation)
Simplify using `[tm]`.
-/
lemma tm_empty : tm (∅ : Set (ι → ℝ)) = 0 := by
  simp [tm]

/- English proof (translation)
Introduce `i` and use `by obtain ⟨m, hm⟩ := ha i obtain ⟨m', hm'⟩ := hb i exact ⟨m + m', by rw [Pi.add_apply, hm, hm', Int.cast_add]⟩`.
-/
lemma Zv_add {a b : ι → ℝ} (ha : a ∈ Zv ι) (hb : b ∈ Zv ι) : a + b ∈ Zv ι := fun i => by
  obtain ⟨m, hm⟩ := ha i
  obtain ⟨m', hm'⟩ := hb i
  exact ⟨m + m', by rw [Pi.add_apply, hm, hm', Int.cast_add]⟩

/- English proof (translation)
Introduce `i` and use `by obtain ⟨m, hm⟩ := ha i exact ⟨-m, by rw [Pi.neg_apply, hm, Int.cast_neg]⟩`.
-/
lemma Zv_neg {a : ι → ℝ} (ha : a ∈ Zv ι) : -a ∈ Zv ι := fun i => by
  obtain ⟨m, hm⟩ := ha i
  exact ⟨-m, by rw [Pi.neg_apply, hm, Int.cast_neg]⟩

/- English proof (translation)
Rewrite using `[Basis.mem_span_iff_repr_mem]`. Simplify using `only [Pi.basisFun_repr, Set.mem_range, algebraMap_int_eq, Int.coe_castRingHom, Zv, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Take `⟨m, hm⟩` from `h i`.

Conclude with `⟨m, hm.symm⟩`. Introduce `h i`. Take `⟨m, hm⟩` from `h i`. Conclude with `⟨m, hm.symm⟩`.
-/
lemma mem_span_basisFun_iff (x : ι → ℝ) :
    x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ x ∈ Zv ι := by
  rw [Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, Set.mem_range, algebraMap_int_eq, Int.coe_castRingHom, Zv,
    Set.mem_setOf_eq]
  constructor
  · intro h i
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, hm.symm⟩
  · intro h i
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, hm.symm⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [ZSpan.mem_fundamentalDomain, Pi.basisFun_repr, Set.mem_Ico, Qv, Set.mem_setOf_eq]`.
-/
lemma fundamentalDomain_eq : ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) = Qv ι := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, Pi.basisFun_repr, Set.mem_Ico, Qv, Set.mem_setOf_eq]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Establish `hab' : a + b = z + x` using `hab`. Use `⟨a, ha, b + -z, Zv_add hb (Zv_neg hz), ?_⟩` and prove the remaining obligations. Use `show a + (b + -z) = x`.

Rewrite using `[← add_assoc, hab', add_neg_cancel_comm]`. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨a, ha, z + b, Zv_add hz hb, by show a + (z + b) = z + (a + b)`. Conclude with `add_left_comm a z b⟩`.
-/
private theorem add_mem_add_intVectors_iff {T : Set (ι → ℝ)} {z : ι → ℝ} (hz : z ∈ Zv ι)
    (x : ι → ℝ) : z + x ∈ T + Zv ι ↔ x ∈ T + Zv ι := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have hab' : a + b = z + x := hab
    refine ⟨a, ha, b + -z, Zv_add hb (Zv_neg hz), ?_⟩
    show a + (b + -z) = x
    rw [← add_assoc, hab', add_neg_cancel_comm]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, z + b, Zv_add hz hb, by
      show a + (z + b) = z + (a + b)
      exact add_left_comm a z b⟩

/- English proof (translation)
Establish `hF : IsAddFundamentalDomain (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) (Qv ι) volume`. Rewrite using `[← fundamentalDomain_eq]`. Conclude with `ZSpan.isAddFundamentalDomain _ _`. Establish `hF'` using `hF.vadd_of_comm c`. Establish `hW : MeasurableSet (B + {c} + Zv ι)` using `hB.add_right.add_right.measurableSet`.

Establish `hinv : ∀ g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)), (fun x => g +ᵥ x) ⁻¹' (B + {c} + Zv ι) = B + {c} + Zv ι` using `fun g => by`. Use extensionality with `x`. Conclude with `add_mem_add_intVectors_iff ((mem_span_basisFun_iff _).1 g.2) x`. Establish `: VAddInvariantMeasure (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) (ι → ℝ) volume`. Use `⟨?_⟩` and prove the remaining obligations.

Introduce `g s _`. Conclude with `measure_preimage_add volume (g : ι → ℝ) s`. Establish `: Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))`. Use `Function.Injective.countable (f := fun g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) => fun i => ⌊(g : ι → ℝ) i⌋) ?_` and prove the remaining obligations. Introduce `g g' hgg`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Take `⟨m, hm⟩` from `(mem_span_basisFun_iff _).1 g.2 i`. Take `⟨m', hm'⟩` from `(mem_span_basisFun_iff _).1 g'.2 i`. Use `congrFun hgg i` as an intermediate fact.

Simplify using `only [hm, hm', Int.floor_intCast] at this`. Rewrite using `[hm, hm', this]`. Establish `h1` using `hF.measure_set_eq hF' hW hinv`. Establish `hshift : B + {c} + Zv ι = (fun x => c + x) '' (B + Zv ι)`. Rewrite using `[add_comm B, add_assoc, Set.singleton_add]`.

Establish `h2 : (B + {c} + Zv ι) ∩ (c +ᵥ Qv ι) = (fun x => c + x) '' ((B + Zv ι) ∩ Qv ι)`. Rewrite using `[Set.image_inter (add_right_injective c), ← hshift]`. Both sides reduce to the same expression. Unfold `tm`. Rewrite using `[Set.inter_comm (Qv ι) (B + {c} + Zv ι), h1, h2, Set.image_add_left, measure_preimage_add, Set.inter_comm (B + Zv ι)]`.
-/
lemma tm_add_singleton {B : Set (ι → ℝ)} (hB : IsOpen B) (c : ι → ℝ) :
    tm (B + {c}) = tm B := by
  have hF : IsAddFundamentalDomain (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) (Qv ι)
      volume := by
    rw [← fundamentalDomain_eq]
    exact ZSpan.isAddFundamentalDomain _ _
  have hF' := hF.vadd_of_comm c
  have hW : MeasurableSet (B + {c} + Zv ι) := hB.add_right.add_right.measurableSet
  have hinv : ∀ g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)),
      (fun x => g +ᵥ x) ⁻¹' (B + {c} + Zv ι) = B + {c} + Zv ι := fun g => by
    ext x
    exact add_mem_add_intVectors_iff ((mem_span_basisFun_iff _).1 g.2) x
  have : VAddInvariantMeasure (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) (ι → ℝ) volume := by
    refine ⟨?_⟩
    intro g s _
    exact measure_preimage_add volume (g : ι → ℝ) s
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
    refine Function.Injective.countable
      (f := fun g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) => fun i => ⌊(g : ι → ℝ) i⌋) ?_
    intro g g' hgg
    apply Subtype.ext
    funext i
    obtain ⟨m, hm⟩ := (mem_span_basisFun_iff _).1 g.2 i
    obtain ⟨m', hm'⟩ := (mem_span_basisFun_iff _).1 g'.2 i
    have := congrFun hgg i
    simp only [hm, hm', Int.floor_intCast] at this
    rw [hm, hm', this]
  have h1 := hF.measure_set_eq hF' hW hinv
  have hshift : B + {c} + Zv ι = (fun x => c + x) '' (B + Zv ι) := by
    rw [add_comm B, add_assoc, Set.singleton_add]
  have h2 : (B + {c} + Zv ι) ∩ (c +ᵥ Qv ι) =
      (fun x => c + x) '' ((B + Zv ι) ∩ Qv ι) := by
    rw [Set.image_inter (add_right_injective c), ← hshift]
    rfl
  unfold tm
  rw [Set.inter_comm (Qv ι) (B + {c} + Zv ι), h1, h2, Set.image_add_left,
    measure_preimage_add, Set.inter_comm (B + Zv ι)]

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `hs.ne'`. Establish `e1 : ∫⁻ y, h (s • y) = ∫⁻ y, h y ∂(Measure.map (fun x : κ → ℝ => s • x) volume)` using `(lintegral_map_equiv h (Homeomorph.smulOfNeZero s hs0).toMeasurableEquiv).symm`. Rewrite `e1` using `[Measure.map_addHaar_smul (μ := volume) hs0, lintegral_smul_measure, smul_eq_mul, Module.finrank_fintype_fun_eq_card]`. Rewrite using `[e1, ← mul_assoc, ← ENNReal.ofReal_mul (pow_pos hs _).le, abs_of_pos (inv_pos.2 (pow_pos hs _)), mul_inv_cancel₀ (pow_ne_zero _ hs0), ENNReal.ofReal_one, one_mul]`.
-/
lemma lintegral_scale {κ : Type*} [Fintype κ] (h : (κ → ℝ) → ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, h y = ENNReal.ofReal (s ^ Fintype.card κ) * ∫⁻ y, h (s • y) := by
  have hs0 : s ≠ 0 := hs.ne'
  have e1 : ∫⁻ y, h (s • y) = ∫⁻ y, h y ∂(Measure.map (fun x : κ → ℝ => s • x) volume) :=
    (lintegral_map_equiv h (Homeomorph.smulOfNeZero s hs0).toMeasurableEquiv).symm
  rw [Measure.map_addHaar_smul (μ := volume) hs0, lintegral_smul_measure, smul_eq_mul,
    Module.finrank_fintype_fun_eq_card] at e1
  rw [e1, ← mul_assoc, ← ENNReal.ofReal_mul (pow_pos hs _).le, abs_of_pos (inv_pos.2 (pow_pos hs _)),
    mul_inv_cancel₀ (pow_ne_zero _ hs0), ENNReal.ofReal_one, one_mul]

section decomp
variable (n j : ℕ)

def emb (u : {i : Fin n // (i : ℕ) < j} → ℝ) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Fin n → ℝ :=
  fun i => if h : (i : ℕ) < j then u ⟨i, h⟩ else y ⟨i, h⟩

def fib (A : Set (Fin n → ℝ)) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Set ({i : Fin n // (i : ℕ) < j} → ℝ) :=
  {u | emb n j u y ∈ A}

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Distinguish the cases in `h : (i : ℕ) < j`. Simplify using `only [emb, dif_pos h]`. Conclude with `continuous_apply _`. Simplify using `only [emb, dif_neg h]`.

Conclude with `continuous_const`.
-/
lemma continuous_emb_left (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Continuous fun u => emb n j u y := by
  refine continuous_pi fun i => ?_
  by_cases h : (i : ℕ) < j
  · simp only [emb, dif_pos h]
    exact continuous_apply _
  · simp only [emb, dif_neg h]
    exact continuous_const

/- English proof (translation)
Establish `: Formalism.FN.boxJ n j = ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j), (fun u : Fin n → ℝ => u i) ⁻¹' Set.Ico 0 1`. Use extensionality with `u`. Simplify using `[Formalism.FN.boxJ]`. Rewrite using `[this]`. Conclude with `MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurable_pi_apply i measurableSet_Ico`.
-/
lemma measurableSet_boxJ : MeasurableSet (boxJ n j) := by
  have : Formalism.FN.boxJ n j =
      ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j), (fun u : Fin n → ℝ => u i) ⁻¹' Set.Ico 0 1 := by
    ext u
    simp [Formalism.FN.boxJ]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurable_pi_apply i measurableSet_Ico

/- English proof (translation)
Use extensionality with `u`. Simplify using `only [Set.mem_setOf_eq, Set.mem_inter_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hbox, a, ha, k, hk, hak⟩`. Use `⟨fun i => ?_, fun i => a i, ?_, fun i => k i, fun i => hk.1 i, ?_⟩` and prove the remaining obligations.

Simplify `hbox i.1 i.2` using `only [emb, dif_pos i.2, Subtype.coe_eta]`. Use `show emb n j (fun i => a i) y ∈ A`. Use `ha using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : (i : ℕ) < j`.

Simplify using `only [emb, dif_pos hi]`. Establish `h` using `congrFun hak i`. Simplify using `only [emb, dif_neg hi, Pi.add_apply, hk.2 i (not_lt.mp hi), add_zero] at h`. Simplify using `only [emb, dif_neg hi, h]`. Use function extensionality and compare the values at `i`.

Establish `h` using `congrFun hak i.1`. Simplify using `only [emb, dif_pos i.2, Pi.add_apply, Subtype.coe_eta] at h`. Simplify `h` using `only [Pi.add_apply]`. Introduce and unpack `⟨hcube, v, hv, w, hw, rfl⟩`. Use `⟨fun i hi => ?_, emb n j v y, hv, emb n j w 0, ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [emb, dif_pos hi]`. Conclude with `hcube ⟨i, hi⟩`. Distinguish the cases in `hi : (i : ℕ) < j`. Simplify using `only [emb, dif_pos hi]`. Conclude with `hw ⟨i, hi⟩`.

Conclude with `⟨0, by simp only [emb, dif_neg hi, Pi.zero_apply, Int.cast_zero]⟩`. Simplify using `only [emb, dif_neg (not_lt.mpr hi), Pi.zero_apply]`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : (i : ℕ) < j`. Simplify using `only [emb, dif_pos hi, Pi.add_apply]`.

Simplify using `only [emb, dif_neg hi, Pi.add_apply, Pi.zero_apply, add_zero]`.
-/
lemma fib_set_eq (A : Set (Fin n → ℝ)) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    {u | emb n j u y ∈ boxJ n j ∩ (A + latJ n j)} = Qv _ ∩ (fib n j A y + Zv _) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hbox, a, ha, k, hk, hak⟩
    refine ⟨fun i => ?_, fun i => a i, ?_, fun i => k i, fun i => hk.1 i, ?_⟩
    · simpa only [emb, dif_pos i.2, Subtype.coe_eta] using hbox i.1 i.2
    · show emb n j (fun i => a i) y ∈ A
      convert ha using 1
      funext i
      by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi]
      · have h := congrFun hak i
        simp only [emb, dif_neg hi, Pi.add_apply, hk.2 i (not_lt.mp hi), add_zero] at h
        simp only [emb, dif_neg hi, h]
    · funext i
      have h := congrFun hak i.1
      simp only [emb, dif_pos i.2, Pi.add_apply, Subtype.coe_eta] at h
      simpa only [Pi.add_apply] using h
  · rintro ⟨hcube, v, hv, w, hw, rfl⟩
    refine ⟨fun i hi => ?_, emb n j v y, hv, emb n j w 0,
      ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
    · simp only [emb, dif_pos hi]
      exact hcube ⟨i, hi⟩
    · by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi]
        exact hw ⟨i, hi⟩
      · exact ⟨0, by simp only [emb, dif_neg hi, Pi.zero_apply, Int.cast_zero]⟩
    · simp only [emb, dif_neg (not_lt.mpr hi), Pi.zero_apply]
    · funext i
      by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi, Pi.add_apply]
      · simp only [emb, dif_neg hi, Pi.add_apply, Pi.zero_apply, add_zero]

/- English proof (translation)
Establish `h : Measure.map e μ (e.symm ⁻¹' S) = μ (e ⁻¹' (e.symm ⁻¹' S))` using `e.map_apply _`. Rewrite `h` using `[he.map_eq]`. Rewrite using `[h]`. Use `congr 1`. Use extensionality with `x`.

Simplify using the standard rewrite rules.
-/
private theorem measure_eq_of_measurePreserving_symm_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (S : Set α) :
    μ S = ν (e.symm ⁻¹' S) := by
  have h : Measure.map e μ (e.symm ⁻¹' S) = μ (e ⁻¹' (e.symm ⁻¹' S)) := e.map_apply _
  rw [he.map_eq] at h
  rw [h]
  congr 1
  ext x
  simp

/- English proof (translation)
Establish `hS : MeasurableSet (Formalism.FN.boxJ n j ∩ (A + Formalism.FN.latJ n j))` using `(measurableSet_boxJ n j).inter hA.add_right.measurableSet`. Establish `hmp` using `measurePreserving_piEquivPiSubtypeProd (μ := fun _ : Fin n => (volume : Measure ℝ)) (p := fun i : Fin n => (i : ℕ) < j)`. Use `(measure_eq_of_measurePreserving_symm_preimage _ hmp (Formalism.FN.boxJ n j ∩ (A + Formalism.FN.latJ n j))).trans ?_` and prove the remaining obligations. Rewrite using `[Measure.prod_apply_symm]`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations.

Rewrite using `[tm, ← fib_set_eq]`. Both sides reduce to the same expression. Conclude with `MeasurableEquiv.measurable _ hS`.
-/
lemma Gj_eq (A : Set (Fin n → ℝ)) (hA : IsOpen A) :
    Gj n j A = ∫⁻ y, tm (fib n j A y) := by
  have hS : MeasurableSet (Formalism.FN.boxJ n j ∩ (A + Formalism.FN.latJ n j)) :=
    (measurableSet_boxJ n j).inter hA.add_right.measurableSet
  have hmp := measurePreserving_piEquivPiSubtypeProd (μ := fun _ : Fin n => (volume : Measure ℝ))
    (p := fun i : Fin n => (i : ℕ) < j)
  refine (measure_eq_of_measurePreserving_symm_preimage _ hmp
    (Formalism.FN.boxJ n j ∩ (A + Formalism.FN.latJ n j))).trans ?_
  rw [Measure.prod_apply_symm]
  · refine lintegral_congr fun y => ?_
    rw [tm, ← fib_set_eq]
    rfl
  · exact MeasurableEquiv.measurable _ hS

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `(lt_of_lt_of_le one_pos hs).ne'`. Break down `(fib n j D y).eq_empty_or_nonempty with h | ⟨w, hw⟩` into its components or cases. Rewrite using `[h, tm_empty]`. Conclude with `zero_le`. Establish `hopen : IsOpen (fib n j D y)` using `hDo.preimage (continuous_emb_left n j y)`.

Rewrite using `[← tm_add_singleton hopen ((s - 1) • w)]`. Apply `tm_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨u, hu, c, hc, rfl⟩`. Rewrite `hc` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality.

Establish `hu' : emb n j u y ∈ D` using `hu`. Establish `hw' : emb n j w y ∈ D` using `hw`. Use `show emb n j (u + (s - 1) • w) (s • y) ∈ s • D`. Rewrite using `[Set.mem_smul_set]`. Use `⟨s⁻¹ • emb n j u y + (1 - s⁻¹) • emb n j w y, hDc hu' hw' (inv_nonneg.2 (by linarith)) ?_ (by ring), ?_⟩` and prove the remaining obligations.

Use polynomial arithmetic with `[mul_nonneg (inv_nonneg.2 (zero_le_one.trans hs)) (sub_nonneg.2 hs), inv_mul_cancel₀ hs0]`. Establish `hinv : s * s⁻¹ = 1` using `mul_inv_cancel₀ hs0`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : (i : ℕ) < j`. Simplify using `only [emb, dif_pos hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Take the linear combination `(u ⟨i, hi⟩ - w ⟨i, hi⟩) * hinv`. Simplify using `only [emb, dif_neg hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem torusImageVolume_fib_le_smul {D : Set (Fin n → ℝ)} (hDo : IsOpen D)
    (hDc : Convex ℝ D) {s : ℝ} (hs : 1 ≤ s) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    tm (fib n j D y) ≤ tm (fib n j (s • D) (s • y)) := by
  have hs0 : s ≠ 0 := (lt_of_lt_of_le one_pos hs).ne'
  rcases (fib n j D y).eq_empty_or_nonempty with h | ⟨w, hw⟩
  · rw [h, tm_empty]
    exact zero_le
  have hopen : IsOpen (fib n j D y) := hDo.preimage (continuous_emb_left n j y)
  rw [← tm_add_singleton hopen ((s - 1) • w)]
  apply tm_mono
  rintro _ ⟨u, hu, c, hc, rfl⟩
  rw [Set.mem_singleton_iff] at hc
  subst hc
  have hu' : emb n j u y ∈ D := hu
  have hw' : emb n j w y ∈ D := hw
  show emb n j (u + (s - 1) • w) (s • y) ∈ s • D
  rw [Set.mem_smul_set]
  refine ⟨s⁻¹ • emb n j u y + (1 - s⁻¹) • emb n j w y,
    hDc hu' hw' (inv_nonneg.2 (by linarith)) ?_ (by ring), ?_⟩
  · nlinarith [mul_nonneg (inv_nonneg.2 (zero_le_one.trans hs)) (sub_nonneg.2 hs),
      inv_mul_cancel₀ hs0]
  · have hinv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    funext i
    by_cases hi : (i : ℕ) < j
    · simp only [emb, dif_pos hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (u ⟨i, hi⟩ - w ⟨i, hi⟩) * hinv
    · simp only [emb, dif_neg hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

/- English proof (translation)
Rewrite using `[← Fintype.card_fin (n - j)]`. Conclude with `Fintype.card_congr { toFun := fun i => ⟨(i.1 : ℕ) - j, by have := i.1.2; have := i.2; omega⟩ invFun := fun k => ⟨⟨(k : ℕ) + j, by have := k.2; omega⟩, by show ¬ ((k : ℕ) + j < j); omega⟩ left_inv := fun i => Subtype.ext (Fin.ext (by show (i.1 : ℕ) - j + j = i.1`. Use `i.2` as an intermediate fact. Use the proof step `omega))`. Use `right_inv := fun k => Fin.ext (by show (k : ℕ) + j - j = k omega) }`.
-/
lemma card_compl (hj : j ≤ n) : Fintype.card {i : Fin n // ¬ (i : ℕ) < j} = n - j := by
  rw [← Fintype.card_fin (n - j)]
  exact Fintype.card_congr
    { toFun := fun i => ⟨(i.1 : ℕ) - j, by have := i.1.2; have := i.2; omega⟩
      invFun := fun k => ⟨⟨(k : ℕ) + j, by have := k.2; omega⟩, by
        show ¬ ((k : ℕ) + j < j); omega⟩
      left_inv := fun i => Subtype.ext (Fin.ext (by
        show (i.1 : ℕ) - j + j = i.1
        have := i.2
        omega))
      right_inv := fun k => Fin.ext (by
        show (k : ℕ) + j - j = k
        omega) }

end decomp
end GjScaling

open GjScaling in
/- English proof (translation)
Introduce `n j C t t' hj hCo hCc _ _ ht htt'`. Establish `ht' : 0 < t'` using `lt_of_lt_of_le ht htt'`. Establish `hs : 0 < t' / t` using `div_pos ht' ht`. Establish `hs1 : 1 ≤ t' / t` using `(le_div_iff₀ ht).2 (by linarith)`. Establish `hD : IsOpen (t • C)` using `hCo.smul₀ ht.ne'`.

Establish `hDc : Convex ℝ (t • C)` using `hCc.smul t`. Establish `hsD : t' • C = (t' / t) • (t • C)`. Rewrite using `[smul_smul, div_mul_eq_mul_div, mul_div_assoc, div_self ht.ne', mul_one]`. Establish `key` using `Formalism.FN.GjScaling.lintegral_scale (fun y => Formalism.FN.GjScaling.tm (Formalism.FN.GjScaling.fib n j ((t' / t) • (t • C)) y)) hs`. Use `beta_reduce at key`.

Rewrite `key` using `[Formalism.FN.GjScaling.card_compl n j hj]`. Rewrite using `[hsD, Formalism.FN.GjScaling.Gj_eq n j _ hD, Formalism.FN.GjScaling.Gj_eq n j _ (hD.smul₀ hs.ne'), key]`. Conclude with `mul_le_mul_of_nonneg_left (lintegral_mono fun y => _root_.Formalism.FN.GjScaling.torusImageVolume_fib_le_smul n j hD hDc hs1 y) (by positivity)`.
-/
theorem partialBoxVolumeScaling : GjScale := by
  intro n j C t t' hj hCo hCc _ _ ht htt'
  have ht' : 0 < t' := lt_of_lt_of_le ht htt'
  have hs : 0 < t' / t := div_pos ht' ht
  have hs1 : 1 ≤ t' / t := (le_div_iff₀ ht).2 (by linarith)
  have hD : IsOpen (t • C) := hCo.smul₀ ht.ne'
  have hDc : Convex ℝ (t • C) := hCc.smul t
  have hsD : t' • C = (t' / t) • (t • C) := by
    rw [smul_smul, div_mul_eq_mul_div, mul_div_assoc, div_self ht.ne', mul_one]
  have key := Formalism.FN.GjScaling.lintegral_scale
    (fun y => Formalism.FN.GjScaling.tm (Formalism.FN.GjScaling.fib n j ((t' / t) • (t • C)) y)) hs
  beta_reduce at key
  rw [Formalism.FN.GjScaling.card_compl n j hj] at key
  rw [hsD, Formalism.FN.GjScaling.Gj_eq n j _ hD,
    Formalism.FN.GjScaling.Gj_eq n j _ (hD.smul₀ hs.ne'), key]
  exact mul_le_mul_of_nonneg_left
    (lintegral_mono fun y => _root_.Formalism.FN.GjScaling.torusImageVolume_fib_le_smul n j hD hDc hs1 y) (by positivity)

end Formalism.FN
