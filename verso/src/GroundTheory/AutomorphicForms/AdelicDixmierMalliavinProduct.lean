import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.GKModules.Garding

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open Set MeasureTheory Measure Topology Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace ProdSmooth

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {A : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
  {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def IsSmooth (h : IsExpLieAlgebra A 𝔤) (e : G ≃ₜ* A × B) (f : G → ℂ) : Prop :=
  (∀ b : B, letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ fun a : A => f (e.symm (a, b))) ∧
  ∃ V : Subgroup B, IsOpen (V : Set B) ∧ IsCompact (V : Set B) ∧
    ∀ x : G, ∀ v ∈ V, f (x * e.symm (1, v)) = f x

def tensorFun (e : G ≃ₜ* A × B) (u : A → ℂ) (w : B → ℂ) (x : G) : ℂ := u (e x).1 * w (e x).2

/- English proof (translation)
Simplify using `[tensorFun]`.
-/
theorem tensorFun_symm (e : G ≃ₜ* A × B) (u : A → ℂ) (w : B → ℂ) (a : A) (b : B) :
    tensorFun e u w (e.symm (a, b)) = u a * w b := by
  simp [tensorFun]

/- English proof (translation)
The claim follows from `(hu.comp (continuous_fst.comp e.continuous)).mul (hw.comp (continuous_snd.comp e.continuous))`.
-/
theorem continuous_tensorFun (e : G ≃ₜ* A × B) {u : A → ℂ} {w : B → ℂ} (hu : Continuous u)
    (hw : Continuous w) : Continuous (tensorFun e u w) :=
  (hu.comp (continuous_fst.comp e.continuous)).mul (hw.comp (continuous_snd.comp e.continuous))

/- English proof (translation)
Use `HasCompactSupport.of_support_subset_isCompact ((hu.prod hw).image e.symm.continuous) ?_` and prove the remaining obligations. Introduce `x hx`. Use `⟨e x, ?_, e.symm_apply_apply x⟩` and prove the remaining obligations. Establish `h1 : u (e x).1 ≠ 0` using `left_ne_zero_of_mul hx`. Establish `h2 : w (e x).2 ≠ 0` using `right_ne_zero_of_mul hx`.

Conclude with `⟨subset_tsupport _ h1, subset_tsupport _ h2⟩`.
-/
theorem hasCompactSupport_tensorFun (e : G ≃ₜ* A × B) {u : A → ℂ} {w : B → ℂ}
    (hu : HasCompactSupport u) (hw : HasCompactSupport w) :
    HasCompactSupport (tensorFun e u w) := by
  refine HasCompactSupport.of_support_subset_isCompact ((hu.prod hw).image e.symm.continuous) ?_
  intro x hx
  refine ⟨e x, ?_, e.symm_apply_apply x⟩
  have h1 : u (e x).1 ≠ 0 := left_ne_zero_of_mul hx
  have h2 : w (e x).2 ≠ 0 := right_ne_zero_of_mul hx
  exact ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩

def tensorCc (e : G ≃ₜ* A × B) (u : A → ℂ) (w : B → ℂ) (hu : Continuous u) (hw : Continuous w)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) :
    CompactlySupportedContinuousMap G ℂ where
  toFun := tensorFun e u w
  continuous_toFun := continuous_tensorFun e hu hw
  hasCompactSupport' := hasCompactSupport_tensorFun e huc hwc

section Cosets

variable (V : Subgroup B)

def cosetInd (b : B) : B → ℂ := (b • (V : Set B)).indicator 1

open scoped Classical in
/- English proof (translation)
Unfold `cosetInd`. Distinguish the cases in `h : b⁻¹ * y ∈ V`. Rewrite using `[indicator_of_mem (mem_leftCoset_iff b |>.2 h), if_pos h]`. Both sides reduce to the same expression. Rewrite using `[indicator_of_notMem (fun h' => h ((mem_leftCoset_iff b).1 h')), if_neg h]`.
-/
theorem cosetInd_apply (b y : B) : cosetInd V b y = if b⁻¹ * y ∈ V then 1 else 0 := by
  unfold cosetInd
  by_cases h : b⁻¹ * y ∈ V
  · rw [indicator_of_mem (mem_leftCoset_iff b |>.2 h), if_pos h]; rfl
  · rw [indicator_of_notMem (fun h' => h ((mem_leftCoset_iff b).1 h')), if_neg h]

/- English proof (translation)
Rewrite using `[cosetInd_apply, cosetInd_apply]`. Establish `: b⁻¹ * (y * v) ∈ V ↔ b⁻¹ * y ∈ V`. Rewrite using `[← mul_assoc]`. Conclude with `Subgroup.mul_mem_cancel_right V hv`. Distinguish the cases in `h : b⁻¹ * y ∈ V`.

Rewrite using `[if_pos (this.2 h), if_pos h]`. Rewrite using `[if_neg (mt this.1 h), if_neg h]`.
-/
theorem cosetInd_mul (b y : B) {v : B} (hv : v ∈ V) : cosetInd V b (y * v) = cosetInd V b y := by
  rw [cosetInd_apply, cosetInd_apply]
  have : b⁻¹ * (y * v) ∈ V ↔ b⁻¹ * y ∈ V := by
    rw [← mul_assoc]; exact Subgroup.mul_mem_cancel_right V hv
  by_cases h : b⁻¹ * y ∈ V
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (mt this.1 h), if_neg h]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(V.isClosed_of_isOpen hVo).smul b, hVo.smul b⟩`.
-/
theorem isClopen_coset (hVo : IsOpen (V : Set B)) (b : B) : IsClopen (b • (V : Set B)) :=
  ⟨(V.isClosed_of_isOpen hVo).smul b, hVo.smul b⟩

/- English proof (translation)
The claim follows from `(isClopen_coset V hVo b).continuous_indicator continuous_const`.
-/
theorem continuous_cosetInd (hVo : IsOpen (V : Set B)) (b : B) : Continuous (cosetInd V b) :=
  (isClopen_coset V hVo b).continuous_indicator continuous_const

/- English proof (translation)
The claim follows from `HasCompactSupport.of_support_subset_isCompact (hVc.smul b) (support_indicator_subset)`.
-/
theorem hasCompactSupport_cosetInd (hVc : IsCompact (V : Set B)) (b : B) :
    HasCompactSupport (cosetInd V b) :=
  HasCompactSupport.of_support_subset_isCompact (hVc.smul b) (support_indicator_subset)

end Cosets

section Factors

variable [T2Space G]

/- English proof (translation)
The claim follows from `(e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (1 : B))).t2Space`.
-/
theorem t2Space_left (e : G ≃ₜ* A × B) : T2Space A :=
  (e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (1 : B))).t2Space

/- English proof (translation)
The claim follows from `(e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : A))).t2Space`.
-/
theorem t2Space_right (e : G ≃ₜ* A × B) : T2Space B :=
  (e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : A))).t2Space

/- English proof (translation)
The claim follows from `(e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : A))).secondCountableTopology`.
-/
theorem secondCountableTopology_right [SecondCountableTopology G] (e : G ≃ₜ* A × B) :
    SecondCountableTopology B :=
  (e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : A))).secondCountableTopology

/- English proof (translation)
Establish `: T2Space B` using `t2Space_right e`. Establish `hce : IsClosedEmbedding (fun a : A => e.symm (a, 1))`. Use `⟨e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (1 : B)), ?_⟩` and prove the remaining obligations. Establish `: range (fun a : A => e.symm (a, 1)) = e.symm '' (univ ×ˢ {1})`. Use extensionality with `x`.

Simplify using `only [mem_range, mem_image, mem_prod, mem_univ, mem_singleton_iff, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨(a, 1), rfl, rfl⟩`. Introduce and unpack `⟨⟨a, b⟩, hb, rfl⟩; exact ⟨a, by simp only at hb; rw [hb]⟩`.

Rewrite using `[this]`. Conclude with `e.symm.toHomeomorph.isClosedMap _ (isClosed_univ.prod isClosed_singleton)`. Conclude with `hce.locallyCompactSpace`.
-/
theorem locallyCompactSpace_left [LocallyCompactSpace G] (e : G ≃ₜ* A × B) :
    LocallyCompactSpace A := by
  have : T2Space B := t2Space_right e
  have hce : IsClosedEmbedding (fun a : A => e.symm (a, 1)) := by
    refine ⟨e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (1 : B)), ?_⟩
    have : range (fun a : A => e.symm (a, 1)) = e.symm '' (univ ×ˢ {1}) := by
      ext x
      simp only [mem_range, mem_image, mem_prod, mem_univ, mem_singleton_iff, true_and]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨(a, 1), rfl, rfl⟩
      · rintro ⟨⟨a, b⟩, hb, rfl⟩; exact ⟨a, by simp only at hb; rw [hb]⟩
    rw [this]
    exact e.symm.toHomeomorph.isClosedMap _ (isClosed_univ.prod isClosed_singleton)
  exact hce.locallyCompactSpace

/- English proof (translation)
Establish `: T2Space A` using `t2Space_left e`. Establish `hce : IsClosedEmbedding (fun b : B => e.symm (1, b))`. Use `⟨e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : A)), ?_⟩` and prove the remaining obligations. Establish `: range (fun b : B => e.symm (1, b)) = e.symm '' ({1} ×ˢ univ)`. Use extensionality with `x`.

Simplify using `only [mem_range, mem_image, mem_prod, mem_univ, mem_singleton_iff, and_true]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, rfl⟩`. Conclude with `⟨(1, b), rfl, rfl⟩`. Introduce and unpack `⟨⟨a, b⟩, ha, rfl⟩; exact ⟨b, by simp only at ha; rw [ha]⟩`.

Rewrite using `[this]`. Conclude with `e.symm.toHomeomorph.isClosedMap _ (isClosed_singleton.prod isClosed_univ)`. Conclude with `hce.locallyCompactSpace`.
-/
theorem locallyCompactSpace_right [LocallyCompactSpace G] (e : G ≃ₜ* A × B) :
    LocallyCompactSpace B := by
  have : T2Space A := t2Space_left e
  have hce : IsClosedEmbedding (fun b : B => e.symm (1, b)) := by
    refine ⟨e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : A)), ?_⟩
    have : range (fun b : B => e.symm (1, b)) = e.symm '' ({1} ×ˢ univ) := by
      ext x
      simp only [mem_range, mem_image, mem_prod, mem_univ, mem_singleton_iff, and_true]
      constructor
      · rintro ⟨b, rfl⟩; exact ⟨(1, b), rfl, rfl⟩
      · rintro ⟨⟨a, b⟩, ha, rfl⟩; exact ⟨b, by simp only at ha; rw [ha]⟩
    rw [this]
    exact e.symm.toHomeomorph.isClosedMap _ (isClosed_singleton.prod isClosed_univ)
  exact hce.locallyCompactSpace

end Factors

section Haar

variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

/- English proof (translation)
Establish `: SecondCountableTopology A` using `secondCountableTopology_subgroup_units A`. Establish `: SecondCountableTopology B` using `secondCountableTopology_right e`. Establish `: LocallyCompactSpace A` using `locallyCompactSpace_left e`. Establish `: LocallyCompactSpace B` using `locallyCompactSpace_right e`. Take `⟨c, hc0, hν⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ.map e = c • μA.prod μB` from `⟨_, (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', isMulLeftInvariant_eq_smul _ _⟩`.

Use `⟨c, hc0, fun F => ?_⟩` and prove the remaining obligations. Establish `h1 : ∫ x, F x ∂μ = ∫ p, F (e.symm p) ∂(μ.map e)`. Use `integral_map_equiv e.toHomeomorph.toMeasurableEquiv (fun p => F (e.symm p)) (μ := μ)` as an intermediate fact. Rewrite `this` using `[show (⇑e.toHomeomorph.toMeasurableEquiv : G → A × B) = ⇑e from rfl]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, hν, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`.
-/
theorem exists_integral_eq_mul_integral_prod (e : G ≃ₜ* A × B) (μ : Measure G) [μ.IsHaarMeasure]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    (μA : Measure A) [μA.IsHaarMeasure] (μB : Measure B) [μB.IsHaarMeasure] :
    ∃ c : NNReal, c ≠ 0 ∧ ∀ F : G → ℂ,
      ∫ x, F x ∂μ = (c : ℂ) * ∫ p, F (e.symm p) ∂(μA.prod μB) := by
  have : SecondCountableTopology A := secondCountableTopology_subgroup_units A
  have : SecondCountableTopology B := secondCountableTopology_right e
  have : LocallyCompactSpace A := locallyCompactSpace_left e
  have : LocallyCompactSpace B := locallyCompactSpace_right e
  obtain ⟨c, hc0, hν⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ.map e = c • μA.prod μB :=
    ⟨_, (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, hc0, fun F => ?_⟩
  have h1 : ∫ x, F x ∂μ = ∫ p, F (e.symm p) ∂(μ.map e) := by
    have := integral_map_equiv e.toHomeomorph.toMeasurableEquiv (fun p => F (e.symm p)) (μ := μ)
    rw [show (⇑e.toHomeomorph.toMeasurableEquiv : G → A × B) = ⇑e from rfl] at this
    rw [this]
    simp
  rw [h1, hν, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end Haar

section SumConv

variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

def IsSumConv (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (P : (G → ℂ) → Prop) (F : G → ℂ) :
    Prop :=
  ∃ (n : ℕ) (φ ψ : Fin n → CompactlySupportedContinuousMap G ℂ), (∀ i, P (φ i) ∧ P (ψ i)) ∧
    ∀ x, F x = ∑ i, conv μ (φ i) (ψ i) x

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (P : (G → ℂ) → Prop)

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x => by simp⟩`.
-/
theorem isSumConv_zero : IsSumConv μ P 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x => by simp⟩

/- English proof (translation)
Take `⟨n₁, φ₁, ψ₁, hP₁, hF₁⟩` from `h₁`. Take `⟨n₂, φ₂, ψ₂, hP₂, hF₂⟩` from `h₂`. Use `⟨n₁ + n₂, Fin.append φ₁ φ₂, Fin.append ψ₁ ψ₂, fun i => ?_, fun x => ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify `hP₁ i` using `only [Fin.append_left]`.

Simplify `hP₂ i` using `only [Fin.append_right]`. Rewrite using `[Fin.sum_univ_add, Pi.add_apply, hF₁ x, hF₂ x]`. Simplify using `only [Fin.append_left, Fin.append_right]`.
-/
theorem IsSumConv.add {F₁ F₂ : G → ℂ} (h₁ : IsSumConv μ P F₁) (h₂ : IsSumConv μ P F₂) :
    IsSumConv μ P (F₁ + F₂) := by
  obtain ⟨n₁, φ₁, ψ₁, hP₁, hF₁⟩ := h₁
  obtain ⟨n₂, φ₂, ψ₂, hP₂, hF₂⟩ := h₂
  refine ⟨n₁ + n₂, Fin.append φ₁ φ₂, Fin.append ψ₁ ψ₂, fun i => ?_, fun x => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hP₁ i
    · simpa only [Fin.append_right] using hP₂ i
  · rw [Fin.sum_univ_add, Pi.add_apply, hF₁ x, hF₂ x]
    simp only [Fin.append_left, Fin.append_right]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isSumConv_zero μ P`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(hF a (Finset.mem_insert_self a s)).add μ P (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))`.
-/
theorem isSumConv_finsetSum {ι : Type*} (s : Finset ι) {F : ι → G → ℂ}
    (hF : ∀ i ∈ s, IsSumConv μ P (F i)) : IsSumConv μ P (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSumConv_zero μ P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add μ P
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end SumConv

section Conv

variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

/- English proof (translation)
Distinguish the cases in `hy : b⁻¹ * y ∈ V`. Establish `h : ∀ b', cosetInd V b b' * cosetInd V 1 (b'⁻¹ * y) = cosetInd V b b'`. Introduce `b'`. Rewrite using `[cosetInd_apply V 1, inv_one, one_mul]`. Distinguish the cases in `hb' : b⁻¹ * b' ∈ V`.

Establish `: b'⁻¹ * y ∈ V`. Use `V.mul_mem (V.inv_mem hb') hy` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Rewrite using `[if_pos this, mul_one]`. Rewrite using `[cosetInd_apply V b, if_neg hb', zero_mul]`.

Repeatedly rewrite using `[h]`. Rewrite using `[cosetInd_apply V b, if_pos hy, mul_one, cosetInd, integral_indicator ((hVo.smul b).measurableSet)]`. Simplify using `only [Pi.one_apply]`. Rewrite using `[setIntegral_const, Complex.real_smul, mul_one, measureReal_def, measureReal_def, measure_smul]`. Establish `h : ∀ b', cosetInd V b b' * cosetInd V 1 (b'⁻¹ * y) = 0`.

Introduce `b'`. Rewrite using `[cosetInd_apply V 1, inv_one, one_mul, cosetInd_apply V b]`. Distinguish the cases in `hb' : b⁻¹ * b' ∈ V`. Establish `: b'⁻¹ * y ∉ V`. Introduce `h'`.

Apply `hy` to reduce the goal to its premises. Use `V.mul_mem hb' h'` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Rewrite using `[if_neg this, mul_zero]`. Rewrite using `[if_neg hb', zero_mul]`.

Repeatedly rewrite using `[h]`. Rewrite using `[integral_zero, cosetInd_apply V b, if_neg hy, mul_zero]`.
-/
theorem integral_cosetInd_mul [MeasurableSpace B] [BorelSpace B] (μB : Measure B)
    [μB.IsMulLeftInvariant] (V : Subgroup B) (hVo : IsOpen (V : Set B)) (b y : B) :
    ∫ b', cosetInd V b b' * cosetInd V 1 (b'⁻¹ * y) ∂μB = (μB.real V : ℂ) * cosetInd V b y := by
  by_cases hy : b⁻¹ * y ∈ V
  · have h : ∀ b', cosetInd V b b' * cosetInd V 1 (b'⁻¹ * y) = cosetInd V b b' := by
      intro b'
      rw [cosetInd_apply V 1, inv_one, one_mul]
      by_cases hb' : b⁻¹ * b' ∈ V
      · have : b'⁻¹ * y ∈ V := by
          have := V.mul_mem (V.inv_mem hb') hy
          simpa [mul_assoc] using this
        rw [if_pos this, mul_one]
      · rw [cosetInd_apply V b, if_neg hb', zero_mul]
    simp_rw [h]
    rw [cosetInd_apply V b, if_pos hy, mul_one, cosetInd,
      integral_indicator ((hVo.smul b).measurableSet)]
    simp only [Pi.one_apply]
    rw [setIntegral_const, Complex.real_smul, mul_one, measureReal_def, measureReal_def,
      measure_smul]
  · have h : ∀ b', cosetInd V b b' * cosetInd V 1 (b'⁻¹ * y) = 0 := by
      intro b'
      rw [cosetInd_apply V 1, inv_one, one_mul, cosetInd_apply V b]
      by_cases hb' : b⁻¹ * b' ∈ V
      · have : b'⁻¹ * y ∉ V := by
          intro h'
          apply hy
          have := V.mul_mem hb' h'
          simpa [mul_assoc] using this
        rw [if_neg this, mul_zero]
      · rw [if_neg hb', zero_mul]
    simp_rw [h]
    rw [integral_zero, cosetInd_apply V b, if_neg hy, mul_zero]

/- English proof (translation)
Establish `: SecondCountableTopology A` using `secondCountableTopology_subgroup_units A`. Establish `: SecondCountableTopology B` using `secondCountableTopology_right e`. Establish `: LocallyCompactSpace A` using `locallyCompactSpace_left e`. Establish `: LocallyCompactSpace B` using `locallyCompactSpace_right e`. Rewrite using `[conv_apply, hc]`.

Use `congr 1`. Establish `h : ∀ p : A × B, tensorCc e u (cosetInd V b) hu (continuous_cosetInd V hVo b) huc (hasCompactSupport_cosetInd V hVc b) (e.symm p) * tensorCc e u' (cosetInd V 1) hu' (continuous_cosetInd V hVo 1) huc' (hasCompactSupport_cosetInd V hVc 1) ((e.symm p)⁻¹ * x) = (u p.1 * u' (p.1⁻¹ * ( …`. Introduce `p`. Express the relevant statement in the definitionally equal form `tensorFun e u (cosetInd V b) (e.symm p) * tensorFun e u' (cosetInd V 1) ((e.symm p)⁻¹ * x) = _`. Establish `hx : e ((e.symm p)⁻¹ * x) = p⁻¹ * e x`.

Rewrite using `[map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]`. Simplify using `only [tensorFun, hx, ContinuousMulEquiv.apply_symm_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[h]`. Rewrite using `[integral_prod_mul (fun a : A => u a * u' (a⁻¹ * (e x).1)) (fun b' : B => cosetInd V b b' * cosetInd V 1 (b'⁻¹ * (e x).2)), integral_cosetInd_mul μB V hVo b (e x).2]`.

Both sides reduce to the same expression.
-/
theorem conv_tensorCc_cosetInd (e : G ≃ₜ* A × B) (μ : Measure G) [μ.IsHaarMeasure]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    (μA : Measure A) [μA.IsHaarMeasure] (μB : Measure B) [μB.IsHaarMeasure] (c : NNReal)
    (hc : ∀ F : G → ℂ, ∫ x, F x ∂μ = (c : ℂ) * ∫ p, F (e.symm p) ∂(μA.prod μB))
    (V : Subgroup B) (hVo : IsOpen (V : Set B)) (hVc : IsCompact (V : Set B)) (b : B)
    {u u' : A → ℂ} (hu : Continuous u) (hu' : Continuous u') (huc : HasCompactSupport u)
    (huc' : HasCompactSupport u') (x : G) :
    conv μ (tensorCc e u (cosetInd V b) hu (continuous_cosetInd V hVo b) huc
        (hasCompactSupport_cosetInd V hVc b))
      (tensorCc e u' (cosetInd V 1) hu' (continuous_cosetInd V hVo 1) huc'
        (hasCompactSupport_cosetInd V hVc 1)) x =
      (c : ℂ) * (groupConv μA u u' (e x).1 * ((μB.real V : ℂ) * cosetInd V b (e x).2)) := by
  have : SecondCountableTopology A := secondCountableTopology_subgroup_units A
  have : SecondCountableTopology B := secondCountableTopology_right e
  have : LocallyCompactSpace A := locallyCompactSpace_left e
  have : LocallyCompactSpace B := locallyCompactSpace_right e
  rw [conv_apply, hc]
  congr 1
  have h : ∀ p : A × B, tensorCc e u (cosetInd V b) hu (continuous_cosetInd V hVo b) huc
        (hasCompactSupport_cosetInd V hVc b) (e.symm p) *
      tensorCc e u' (cosetInd V 1) hu' (continuous_cosetInd V hVo 1) huc'
        (hasCompactSupport_cosetInd V hVc 1) ((e.symm p)⁻¹ * x) =
      (u p.1 * u' (p.1⁻¹ * (e x).1)) * (cosetInd V b p.2 * cosetInd V 1 (p.2⁻¹ * (e x).2)) := by
    intro p
    change tensorFun e u (cosetInd V b) (e.symm p) *
      tensorFun e u' (cosetInd V 1) ((e.symm p)⁻¹ * x) = _
    have hx : e ((e.symm p)⁻¹ * x) = p⁻¹ * e x := by
      rw [map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
    simp only [tensorFun, hx, ContinuousMulEquiv.apply_symm_apply, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_inv, Prod.snd_inv]
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun a : A => u a * u' (a⁻¹ * (e x).1))
    (fun b' : B => cosetInd V b b' * cosetInd V 1 (b'⁻¹ * (e x).2)),
    integral_cosetInd_mul μB V hVo b (e x).2]
  rfl

end Conv

section Main

variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

/- English proof (translation)
Use `⟨fun b' => ?_, V, hVo, hVc, fun x v hv => ?_⟩` and prove the remaining obligations. Set `` to `h.chartedSpace`. Simplify using `only [tensorFun_symm]`. Conclude with `((contDiff_id.mul contDiff_const : ContDiff ℝ ∞ fun z : ℂ => z * cosetInd V b b') ).contMDiff.comp hu`. Simplify using `only [tensorFun, map_mul, ContinuousMulEquiv.apply_symm_apply, Prod.fst_mul, Prod.snd_mul, mul_one]`.

Rewrite using `[cosetInd_mul V b _ hv]`.
-/
theorem isSmooth_tensorFun (h : IsExpLieAlgebra A 𝔤) (e : G ≃ₜ* A × B) {u : A → ℂ}
    (hu : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ u) (V : Subgroup B)
    (hVo : IsOpen (V : Set B)) (hVc : IsCompact (V : Set B)) (b : B) :
    IsSmooth h e (tensorFun e u (cosetInd V b)) := by
  refine ⟨fun b' => ?_, V, hVo, hVc, fun x v hv => ?_⟩
  · let := h.chartedSpace
    simp only [tensorFun_symm]
    exact ((contDiff_id.mul contDiff_const : ContDiff ℝ ∞ fun z : ℂ => z * cosetInd V b b')
      ).contMDiff.comp hu
  · simp only [tensorFun, map_mul, ContinuousMulEquiv.apply_symm_apply, Prod.fst_mul,
      Prod.snd_mul, mul_one]
    rw [cosetInd_mul V b _ hv]

/- English proof (translation)
Establish `: LocallyCompactSpace B` using `locallyCompactSpace_right e`. Establish `: T2Space B` using `t2Space_right e`. Use `borelize B`. Set `μB : Measure B` to `Measure.haar`. Take `⟨c, hc0, hc⟩` from `exists_integral_eq_mul_integral_prod e μ μA μB`.

Establish `hV0 : (μB.real V : ℂ) ≠ 0`. Establish `h1 : μB V ≠ 0` using `(hVo.measure_pos μB ⟨1, V.one_mem⟩).ne'`. Establish `h2 : μB V ≠ ⊤` using `hVc.measure_lt_top.ne`. Rewrite using `[measureReal_def]`. Conclude with `(ENNReal.toReal_pos h1 h2).ne'` after adjusting the coercions.

Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc0`. Use `set s : ℂ := ((c : ℂ) * (μB.real V : ℂ))⁻¹ with hs`. Set `φ' : A → ℂ` to `fun a => s * φ a`. Establish `hφ'c : Continuous φ'` using `continuous_const.mul (by let := h.chartedSpace; exact hφ.continuous)`. Establish `hφ'cs : HasCompactSupport φ'` using `hφc.mul_left`.

Establish `hφ's : letI` using `h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ φ' := by`. Set `` to `h.chartedSpace`. Conclude with `((contDiff_const.mul contDiff_id : ContDiff ℝ ∞ fun z : ℂ => s * z)).contMDiff.comp hφ`. Establish `hψc' : Continuous ψ` using `by let := h.chartedSpace; exact hψ.continuous`. Use `⟨1, fun _ => tensorCc e φ' (cosetInd V b) hφ'c (continuous_cosetInd V hVo b) hφ'cs (hasCompactSupport_cosetInd V hVc b), fun _ => tensorCc e ψ (cosetInd V 1) hψc' (continuous_cosetInd V hVo 1) hψc (hasCompactSupport_cosetInd V hVc 1), fun _ => ⟨isSmooth_tensorFun h e hφ's V hVo h …` and prove the remaining obligations.

Rewrite using `[Fin.sum_univ_one, conv_tensorCc_cosetInd e μ μA μB c hc V hVo hVc b _ _ _ _ x]`. Establish `hg : groupConv μA φ' ψ (e x).1 = s * groupConv μA φ ψ (e x).1`. Simplify using `only [groupConv, φ', mul_assoc]`. Conclude with `integral_const_mul _ _`. Rewrite using `[hg, tensorFun, hs]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem isSumConv_tensorFun_groupConv (h : IsExpLieAlgebra A 𝔤) (e : G ≃ₜ* A × B)
    (μ : Measure G) [μ.IsHaarMeasure] [MeasurableSpace A] [BorelSpace A] (μA : Measure A)
    [μA.IsHaarMeasure] {φ ψ : A → ℂ} (hφ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ φ)
    (hφc : HasCompactSupport φ) (hψ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ ψ)
    (hψc : HasCompactSupport ψ) (V : Subgroup B) (hVo : IsOpen (V : Set B))
    (hVc : IsCompact (V : Set B)) (b : B) :
    IsSumConv μ (IsSmooth h e) (tensorFun e (groupConv μA φ ψ) (cosetInd V b)) := by
  have : LocallyCompactSpace B := locallyCompactSpace_right e
  have : T2Space B := t2Space_right e
  borelize B
  let μB : Measure B := Measure.haar
  obtain ⟨c, hc0, hc⟩ := exists_integral_eq_mul_integral_prod e μ μA μB
  have hV0 : (μB.real V : ℂ) ≠ 0 := by
    have h1 : μB V ≠ 0 := (hVo.measure_pos μB ⟨1, V.one_mem⟩).ne'
    have h2 : μB V ≠ ⊤ := hVc.measure_lt_top.ne
    rw [measureReal_def]
    exact_mod_cast (ENNReal.toReal_pos h1 h2).ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  set s : ℂ := ((c : ℂ) * (μB.real V : ℂ))⁻¹ with hs
  let φ' : A → ℂ := fun a => s * φ a
  have hφ'c : Continuous φ' := continuous_const.mul (by let := h.chartedSpace; exact hφ.continuous)
  have hφ'cs : HasCompactSupport φ' := hφc.mul_left
  have hφ's : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ φ' := by
    let := h.chartedSpace
    exact ((contDiff_const.mul contDiff_id : ContDiff ℝ ∞ fun z : ℂ => s * z)).contMDiff.comp hφ
  have hψc' : Continuous ψ := by let := h.chartedSpace; exact hψ.continuous
  refine ⟨1, fun _ => tensorCc e φ' (cosetInd V b) hφ'c (continuous_cosetInd V hVo b) hφ'cs
      (hasCompactSupport_cosetInd V hVc b),
    fun _ => tensorCc e ψ (cosetInd V 1) hψc' (continuous_cosetInd V hVo 1) hψc
      (hasCompactSupport_cosetInd V hVc 1),
    fun _ => ⟨isSmooth_tensorFun h e hφ's V hVo hVc b, isSmooth_tensorFun h e hψ V hVo hVc 1⟩,
    fun x => ?_⟩
  rw [Fin.sum_univ_one, conv_tensorCc_cosetInd e μ μA μB c hc V hVo hVc b _ _ _ _ x]
  have hg : groupConv μA φ' ψ (e x).1 = s * groupConv μA φ ψ (e x).1 := by
    simp only [groupConv, φ', mul_assoc]
    exact integral_const_mul _ _
  rw [hg, tensorFun, hs]
  field_simp

/- English proof (translation)
Take `⟨hsm, V, hVo, hVc, hinv⟩` from `hf`. Establish `: T2Space A` using `t2Space_left e`. Establish `: LocallyCompactSpace A` using `locallyCompactSpace_left e`. Use `borelize (↥A)`. Set `μA : Measure A` to `Measure.haar`.

Use `set S : Set B := (fun x => (e x).2) '' tsupport f with hSdef`. Establish `hS : IsCompact S` using `f.hasCompactSupport.image (continuous_snd.comp e.continuous)`. Take `⟨t, -, hcov⟩` from `hS.elim_nhds_subcover (fun b => b • (V : Set B)) (fun b _ => (hVo.smul b).mem_nhds ((mem_leftCoset_iff b).2 (by simp)))`. Set `T : Finset (B ⧸ V)` to `t.image (QuotientGroup.mk : B → B ⧸ V)`. Set `r : B ⧸ V → B` to `fun q => q.out`.

Establish `hr : ∀ (q : B ⧸ V) (y : B), (r q)⁻¹ * y ∈ V ↔ (y : B ⧸ V) = q`. Introduce `q y`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]`. Set `fq : B ⧸ V → A → ℂ` to `fun q a => f (e.symm (a, r q))`. Establish `hdec : ∀ x, f x = ∑ q ∈ T, tensorFun e (fq q) (cosetInd V (r q)) x`.

Introduce `x`. Establish `h1 : ∀ q, tensorFun e (fq q) (cosetInd V (r q)) x = if ((e x).2 : B ⧸ V) = q then fq q (e x).1 else 0`. Introduce `q`. Rewrite using `[tensorFun, cosetInd_apply]`. Distinguish the cases in `hq : ((e x).2 : B ⧸ V) = q`.

Rewrite using `[if_pos ((hr q _).2 hq), if_pos hq, mul_one]`. Rewrite using `[if_neg (fun h' => hq ((hr q _).1 h')), if_neg hq, mul_zero]`. Repeatedly rewrite using `[h1]`. Rewrite using `[Finset.sum_ite_eq]`. Distinguish the cases in `hT : ((e x).2 : B ⧸ V) ∈ T`.

Rewrite using `[if_pos hT] set q : B ⧸ V := ((e x).2 : B ⧸ V)`. Establish `hv : (r q)⁻¹ * (e x).2 ∈ V` using `(hr q _).2 rfl`. Establish `hx : x = e.symm ((e x).1, r q) * e.symm (1, (r q)⁻¹ * (e x).2)`. Rewrite using `[← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel_left]`. Conclude with `(e.symm_apply_apply x).symm`.

Express the relevant statement in the definitionally equal form `f x = f (e.symm ((e x).1, r q))`. Use `conv_lhs => rw [hx]`. Conclude with `hinv _ _ hv`. Rewrite using `[if_neg hT]`. Assume the negation of the conclusion as `hfx`.

Establish `hxS : (e x).2 ∈ S` using `⟨x, subset_tsupport _ hfx, rfl⟩`. Take `⟨b, hbt, hb⟩` from `mem_iUnion₂.1 (hcov hxS)`. Apply `hT` to reduce the goal to its premises. Use `Finset.mem_image.2 ⟨b, hbt, ?_⟩` and prove the remaining obligations. Conclude with `QuotientGroup.eq.2 ((mem_leftCoset_iff b).1 hb)`.

Establish `hfq : ∀ q, IsSumConv μ (IsSmooth h e) (tensorFun e (fq q) (cosetInd V (r q)))`. Introduce `q`. Establish `hcs : HasCompactSupport (fq q)`. Use `HasCompactSupport.of_support_subset_isCompact (f.hasCompactSupport.image (continuous_fst.comp e.continuous)) ?_` and prove the remaining obligations. Introduce `a ha`.

Conclude with `⟨e.symm (a, r q), subset_tsupport _ ha, congrArg Prod.fst (e.apply_symm_apply _)⟩`. Take `⟨m, φ, ψ, hφψ, hfeq⟩` from `dixmierMalliavin h μA (fq q) (hsm (r q)) hcs`. Establish `hsum : tensorFun e (fq q) (cosetInd V (r q)) = ∑ i, tensorFun e (groupConv μA (φ i) (ψ i)) (cosetInd V (r q))`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`.

Simplify using `only [tensorFun]`. Rewrite using `[hfeq, Finset.sum_apply, Finset.sum_mul]`. Rewrite using `[hsum]`. Conclude with `isSumConv_finsetSum μ _ _ fun i _ => isSumConv_tensorFun_groupConv h e μ μA (hφψ i).1 (hφψ i).2.1 (hφψ i).2.2.1 (hφψ i).2.2.2 V hVo hVc (r q)`. Take `⟨n, φ, ψ, hP, hF⟩` from `isSumConv_finsetSum μ (IsSmooth h e) T (fun q _ => hfq q)`.

Use `⟨n, φ, ψ, hP, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[CompactlySupportedContinuousMap.sum_apply, hdec x, ← hF x, Finset.sum_apply]`.
-/
theorem exists_sum_conv (h : IsExpLieAlgebra A 𝔤) (e : G ≃ₜ* A × B) (μ : Measure G)
    [μ.IsHaarMeasure] (f : CompactlySupportedContinuousMap G ℂ) (hf : IsSmooth h e f) :
    ∃ (n : ℕ) (φ ψ : Fin n → CompactlySupportedContinuousMap G ℂ),
      (∀ i, IsSmooth h e (φ i) ∧ IsSmooth h e (ψ i)) ∧ f = ∑ i, conv μ (φ i) (ψ i) := by
  classical
  obtain ⟨hsm, V, hVo, hVc, hinv⟩ := hf
  have : T2Space A := t2Space_left e
  have : LocallyCompactSpace A := locallyCompactSpace_left e
  borelize (↥A)
  let μA : Measure A := Measure.haar
  set S : Set B := (fun x => (e x).2) '' tsupport f with hSdef
  have hS : IsCompact S := f.hasCompactSupport.image (continuous_snd.comp e.continuous)
  obtain ⟨t, -, hcov⟩ := hS.elim_nhds_subcover (fun b => b • (V : Set B))
    (fun b _ => (hVo.smul b).mem_nhds ((mem_leftCoset_iff b).2 (by simp)))
  let T : Finset (B ⧸ V) := t.image (QuotientGroup.mk : B → B ⧸ V)
  let r : B ⧸ V → B := fun q => q.out
  have hr : ∀ (q : B ⧸ V) (y : B), (r q)⁻¹ * y ∈ V ↔ (y : B ⧸ V) = q := by
    intro q y
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
  let fq : B ⧸ V → A → ℂ := fun q a => f (e.symm (a, r q))

  have hdec : ∀ x, f x = ∑ q ∈ T, tensorFun e (fq q) (cosetInd V (r q)) x := by
    intro x
    have h1 : ∀ q, tensorFun e (fq q) (cosetInd V (r q)) x =
        if ((e x).2 : B ⧸ V) = q then fq q (e x).1 else 0 := by
      intro q
      rw [tensorFun, cosetInd_apply]
      by_cases hq : ((e x).2 : B ⧸ V) = q
      · rw [if_pos ((hr q _).2 hq), if_pos hq, mul_one]
      · rw [if_neg (fun h' => hq ((hr q _).1 h')), if_neg hq, mul_zero]
    simp_rw [h1]
    rw [Finset.sum_ite_eq]
    by_cases hT : ((e x).2 : B ⧸ V) ∈ T
    · rw [if_pos hT]
      set q : B ⧸ V := ((e x).2 : B ⧸ V)
      have hv : (r q)⁻¹ * (e x).2 ∈ V := (hr q _).2 rfl
      have hx : x = e.symm ((e x).1, r q) * e.symm (1, (r q)⁻¹ * (e x).2) := by
        rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel_left]
        exact (e.symm_apply_apply x).symm
      change f x = f (e.symm ((e x).1, r q))
      conv_lhs => rw [hx]
      exact hinv _ _ hv
    · rw [if_neg hT]
      by_contra hfx
      have hxS : (e x).2 ∈ S := ⟨x, subset_tsupport _ hfx, rfl⟩
      obtain ⟨b, hbt, hb⟩ := mem_iUnion₂.1 (hcov hxS)
      apply hT
      refine Finset.mem_image.2 ⟨b, hbt, ?_⟩
      exact QuotientGroup.eq.2 ((mem_leftCoset_iff b).1 hb)

  have hfq : ∀ q, IsSumConv μ (IsSmooth h e) (tensorFun e (fq q) (cosetInd V (r q))) := by
    intro q
    have hcs : HasCompactSupport (fq q) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (f.hasCompactSupport.image (continuous_fst.comp e.continuous)) ?_
      intro a ha
      exact ⟨e.symm (a, r q), subset_tsupport _ ha, congrArg Prod.fst (e.apply_symm_apply _)⟩
    obtain ⟨m, φ, ψ, hφψ, hfeq⟩ := dixmierMalliavin h μA (fq q) (hsm (r q)) hcs
    have hsum : tensorFun e (fq q) (cosetInd V (r q)) =
        ∑ i, tensorFun e (groupConv μA (φ i) (ψ i)) (cosetInd V (r q)) := by
      funext x
      rw [Finset.sum_apply]
      simp only [tensorFun]
      rw [hfeq, Finset.sum_apply, Finset.sum_mul]
    rw [hsum]
    exact isSumConv_finsetSum μ _ _ fun i _ => isSumConv_tensorFun_groupConv h e μ μA
      (hφψ i).1 (hφψ i).2.1 (hφψ i).2.2.1 (hφψ i).2.2.2 V hVo hVc (r q)
  obtain ⟨n, φ, ψ, hP, hF⟩ := isSumConv_finsetSum μ (IsSmooth h e) T (fun q _ => hfq q)
  refine ⟨n, φ, ψ, hP, ?_⟩
  ext x
  rw [CompactlySupportedContinuousMap.sum_apply, hdec x, ← hF x, Finset.sum_apply]

end Main

end ProdSmooth

end

end GroundTheory.Automorphic
