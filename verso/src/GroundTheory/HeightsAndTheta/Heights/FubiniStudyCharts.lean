import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexProjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ContDiff Manifold
open Topology Set

noncomputable section

variable {N : ℕ}

namespace CP

def chartVec (i : Fin (N + 1)) (z : Fin N → ℂ) : Fin (N + 1) → ℂ := Fin.insertNth i 1 z

/- English proof (translation)
Simplify using `[chartVec]`.
-/
@[simp] lemma chartVec_self (i : Fin (N + 1)) (z : Fin N → ℂ) : chartVec i z i = 1 := by
  simp [chartVec]

/- English proof (translation)
Simplify using `[chartVec]`.
-/
@[simp] lemma chartVec_succAbove (i : Fin (N + 1)) (z : Fin N → ℂ) (j : Fin N) :
    chartVec i z (i.succAbove j) = z j := by
  simp [chartVec]

/- English proof (translation)
Introduce `h`. Use `congr_fun h i` as an intermediate fact. Simplify using `at this`.
-/
lemma chartVec_ne_zero (i : Fin (N + 1)) (z : Fin N → ℂ) : chartVec i z ≠ 0 := by
  intro h
  have := congr_fun h i
  simp at this

/- English proof (translation)
Take `rfl | ⟨k, rfl⟩` from `Fin.eq_self_or_eq_succAbove i m`. Simplify using `only [chartVec_self]`. Conclude with `contDiff_const`. Simplify using `only [chartVec_succAbove]`. Conclude with `(ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin N => ℂ) k).contDiff`.
-/
lemma contDiff_chartVec_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (i m : Fin (N + 1)) : ContDiff 𝕜 ∞ (fun z : Fin N → ℂ => chartVec i z m) := by
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
  · simp only [chartVec_self]; exact contDiff_const
  · simp only [chartVec_succAbove]
    exact (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin N => ℂ) k).contDiff

/- English proof (translation)
The claim follows from `continuous_pi fun m => (contDiff_chartVec_apply ℂ i m).continuous`.
-/
lemma continuous_chartVec (i : Fin (N + 1)) : Continuous (chartVec (N := N) i) :=
  continuous_pi fun m => (contDiff_chartVec_apply ℂ i m).continuous

def chartInv (i : Fin (N + 1)) (z : Fin N → ℂ) : CP N :=
  Projectivization.mk ℂ (chartVec i z) (chartVec_ne_zero i z)

/- English proof (translation)
The claim follows from `ProjTopology.continuous_mk'.comp ((continuous_chartVec i).subtype_mk fun z => chartVec_ne_zero i z)`.
-/
lemma continuous_chartInv (i : Fin (N + 1)) : Continuous (chartInv (N := N) i) :=
  ProjTopology.continuous_mk'.comp
    ((continuous_chartVec i).subtype_mk fun z => chartVec_ne_zero i z)

def chartCoord (i : Fin (N + 1)) : CP N → (Fin N → ℂ) :=
  Projectivization.lift (fun v => fun j => v.1 (i.succAbove j) / v.1 i) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
    funext j
    have ht : t ≠ 0 := by rintro rfl; simp at ha
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hbi : b i = 0
    · simp [hbi]
    · field_simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma chartCoord_mk (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    chartCoord i (Projectivization.mk ℂ v hv) = fun j => v (i.succAbove j) / v i := rfl

def chartDomain (i : Fin (N + 1)) : Set (CP N) :=
  {x | Projectivization.lift (fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => v.1 i ≠ 0) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at ha
    simp [ht]) x}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] lemma mk_mem_chartDomain (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ chartDomain i ↔ v i ≠ 0 := Iff.rfl

/- English proof (translation)
Simplify using `[chartInv]`.
-/
lemma chartInv_mem (i : Fin (N + 1)) (z : Fin N → ℂ) : chartInv i z ∈ chartDomain i := by
  simp [chartInv]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[chartInv]`.
-/
lemma chartCoord_chartInv (i : Fin (N + 1)) (z : Fin N → ℂ) : chartCoord i (chartInv i z) = z := by
  funext j; simp [chartInv]

/- English proof (translation)
Proceed by induction on `x using Projectivization.ind with`. Consider the case `h v hv`. Rewrite `hx` using `[mk_mem_chartDomain]`. Simplify using `only [chartInv, chartCoord_mk]`. Rewrite using `[Projectivization.mk_eq_mk_iff]`.

Use `⟨Units.mk0 (v i)⁻¹ (inv_ne_zero hx), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `m`. Take `rfl | ⟨k, rfl⟩` from `Fin.eq_self_or_eq_succAbove i m`. Simplify using `[hx]`. Simplify using `[div_eq_inv_mul]`.
-/
lemma chartInv_chartCoord (i : Fin (N + 1)) {x : CP N} (hx : x ∈ chartDomain i) :
    chartInv i (chartCoord i x) = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [mk_mem_chartDomain] at hx
    simp only [chartInv, chartCoord_mk]
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (v i)⁻¹ (inv_ne_zero hx), ?_⟩
    funext m
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
    · simp [hx]
    · simp [div_eq_inv_mul]

/- English proof (translation)
Use `⟨⟨rfl⟩, fun x => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using Projectivization.ind with`. Consider the case `h v hv => exact ⟨⟨v, hv⟩, rfl⟩`.
-/
lemma isQuotientMap_mk' : IsQuotientMap (Projectivization.mk' ℂ : {v : Fin (N + 1) → ℂ // v ≠ 0} → CP N) := by
  refine ⟨⟨rfl⟩, fun x => ?_⟩
  induction x using Projectivization.ind with
  | h v hv => exact ⟨⟨v, hv⟩, rfl⟩

/- English proof (translation)
Rewrite using `[ProjTopology.isOpen_iff]`. Establish `: (Projectivization.mk' ℂ) ⁻¹' (chartDomain (N` using `N) i) = {v : {v : Fin (N + 1) → ℂ // v ≠ 0} | v.1 i ≠ 0} := by`. Use extensionality with `⟨v, hv⟩`. Conclude with `Iff.rfl`. Rewrite using `[this]`.

Conclude with `isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const`.
-/
lemma isOpen_chartDomain (i : Fin (N + 1)) : IsOpen (chartDomain (N := N) i) := by
  rw [ProjTopology.isOpen_iff]
  have : (Projectivization.mk' ℂ) ⁻¹' (chartDomain (N := N) i) =
      {v : {v : Fin (N + 1) → ℂ // v ≠ 0} | v.1 i ≠ 0} := by
    ext ⟨v, hv⟩; exact Iff.rfl
  rw [this]
  exact isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const

/- English proof (translation)
Rewrite using `[isQuotientMap_mk'.continuousOn_isOpen_iff (isOpen_chartDomain i)]`. Use `continuousOn_pi.mpr fun j => ?_` and prove the remaining obligations. Introduce `v hv`. Establish `hvi : v.1 i ≠ 0` using `hv`. Establish `hc : ContinuousAt (fun w : {v : Fin (N + 1) → ℂ // v ≠ 0} => w.1 (i.succAbove j) / w.1 i) v` using `(((continuous_apply _).comp continuous_subtype_val).continuousAt).div (((continuous_apply _).comp continuous_subtype_val).continuousAt) hvi`.

Conclude with `hc.continuousWithinAt`.
-/
lemma continuousOn_chartCoord (i : Fin (N + 1)) :
    ContinuousOn (chartCoord (N := N) i) (chartDomain i) := by
  rw [isQuotientMap_mk'.continuousOn_isOpen_iff (isOpen_chartDomain i)]
  refine continuousOn_pi.mpr fun j => ?_
  intro v hv
  have hvi : v.1 i ≠ 0 := hv
  have hc : ContinuousAt (fun w : {v : Fin (N + 1) → ℂ // v ≠ 0} => w.1 (i.succAbove j) / w.1 i) v :=
    (((continuous_apply _).comp continuous_subtype_val).continuousAt).div
      (((continuous_apply _).comp continuous_subtype_val).continuousAt) hvi
  exact hc.continuousWithinAt

def chart (i : Fin (N + 1)) : OpenPartialHomeomorph (CP N) (Fin N → ℂ) where
  toFun := chartCoord i
  invFun := chartInv i
  source := chartDomain i
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := chartInv_mem i z
  left_inv' _ hx := chartInv_chartCoord i hx
  right_inv' z _ := chartCoord_chartInv i z
  open_source := isOpen_chartDomain i
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_chartCoord i
  continuousOn_invFun := (continuous_chartInv i).continuousOn

/- English proof (translation)
Proceed by induction on `x using Projectivization.ind with`. Consider the case `h v hv`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hv`. Conclude with `⟨i, hi⟩`.
-/
lemma exists_mem_chartDomain (x : CP N) : ∃ i, x ∈ chartDomain i := by
  induction x using Projectivization.ind with
  | h v hv =>
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact ⟨i, hi⟩

def chartIndex (x : CP N) : Fin (N + 1) := (exists_mem_chartDomain x).choose

/- English proof (translation)
The claim follows from `(exists_mem_chartDomain x).choose_spec`.
-/
lemma mem_chartDomain_chartIndex (x : CP N) : x ∈ chartDomain (chartIndex x) :=
  (exists_mem_chartDomain x).choose_spec

instance instChartedSpace : ChartedSpace (Fin N → ℂ) (CP N) where
  atlas := range chart
  chartAt x := chart (chartIndex x)
  mem_chart_source x := mem_chartDomain_chartIndex x
  chart_mem_atlas _ := mem_range_self _

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma chartCoord_chartInv_eq (i j : Fin (N + 1)) (z : Fin N → ℂ) :
    chartCoord j (chartInv i z) = fun k => chartVec i z (j.succAbove k) / chartVec i z j := rfl

/- English proof (translation)
Simplify using `only [chartCoord_chartInv_eq]`. Use `contDiffOn_pi.mpr fun k => ?_` and prove the remaining obligations. Conclude with `(contDiff_chartVec_apply ℂ i _).contDiffOn.div (contDiff_chartVec_apply ℂ i _).contDiffOn fun z hz => hz`.
-/
lemma contDiffOn_transition (i j : Fin (N + 1)) :
    ContDiffOn ℂ ∞ (fun z => chartCoord j (chartInv i z)) {z | chartVec i z j ≠ 0} := by
  simp only [chartCoord_chartInv_eq]
  refine contDiffOn_pi.mpr fun k => ?_
  exact (contDiff_chartVec_apply ℂ i _).contDiffOn.div (contDiff_chartVec_apply ℂ i _).contDiffOn
    fun z hz => hz

instance instIsManifold : IsManifold 𝓘(ℂ, Fin N → ℂ) ∞ (CP N) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id_eq, Function.id_comp, Function.comp_id]
  refine (contDiffOn_transition i j).congr_mono ?_ ?_
  · intro _ _; rfl
  · intro z hz
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_toPartialEquiv] at hz
    exact hz.2

end CP

end

end GroundTheory.Heights₂.Heights
