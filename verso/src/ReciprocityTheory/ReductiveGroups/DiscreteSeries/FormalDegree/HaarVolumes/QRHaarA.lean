import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LeftMulMapEqTransposeConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriUniq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QrMapMeasurableSetImage
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DetNull

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.QRH

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def qrDom (N : ℕ) : Set (UNgrp N × TriCo N) := Set.univ ×ˢ triPos N

def glSet (N : ℕ) : Set (Fin N → Fin N → ℂ) := {Z | (Matrix.of Z).det ≠ 0}

/- English proof (translation)
Unfold `triPos`. Simplify using `only [Set.ofPred_forall]`. Conclude with `MeasurableSet.iInter fun j => measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)`.
-/
theorem measurableSet_triPos : MeasurableSet (triPos N) := by
  unfold triPos
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)

/- English proof (translation)
The claim follows from `MeasurableSet.univ.prod measurableSet_triPos`.
-/
theorem measurableSet_qrDom : MeasurableSet (qrDom N) :=
  MeasurableSet.univ.prod measurableSet_triPos

/- English proof (translation)
The claim follows from `show Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => Z.det from continuous_id.matrix_det`.
-/
theorem continuous_det_of : Continuous fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det :=
  show Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => Z.det from continuous_id.matrix_det

/- English proof (translation)
The claim follows from `(isOpen_ne_fun continuous_det_of continuous_const).measurableSet`.
-/
theorem measurableSet_glSet : MeasurableSet (glSet N) :=
  (isOpen_ne_fun continuous_det_of continuous_const).measurableSet

/- English proof (translation)
The claim follows from `qrMap_continuous.measurable`.
-/
theorem measurable_qrMap : Measurable (qrMap (N := N)) := qrMap_continuous.measurable

def qrW (p : qrDom N) : Fin N → Fin N → ℂ := qrMap p.1

/- English proof (translation)
Rewrite using `[show Set.range (qrW (N := N)) = qrMap '' qrDom N by`. Use extensionality with `Z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, rfl⟩`. Conclude with `⟨p.1, p.2, rfl⟩`.

Introduce and unpack `⟨p, hp, rfl⟩`. Conclude with `⟨⟨p, hp⟩, rfl⟩]`. Conclude with `qrMap_image`.
-/
theorem range_qrW : Set.range (qrW (N := N)) = glSet N := by
  rw [show Set.range (qrW (N := N)) = qrMap '' qrDom N by
    ext Z; constructor
    · rintro ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩]
  exact qrMap_image

/- English proof (translation)
Introduce `p q h`. Conclude with `Subtype.ext (qrMap_injOn p.2 q.2 h)`. Use `measurable := measurable_qrMap.comp measurable_subtype_coe`. Use the proof step `measurableSet_image' := by`. Introduce `s hs`.

Establish `h1 : MeasurableSet (Subtype.val '' s : Set (UNgrp N × TriCo N))` using `(MeasurableEmbedding.subtype_coe measurableSet_qrDom).measurableSet_image' hs`. Establish `h2 : qrW '' s = qrMap '' (Subtype.val '' s)`. Rewrite using `[Set.image_image]`. Both sides reduce to the same expression. Rewrite using `[h2]`.

Use `qrMap_measurableSet_image _ h1 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, _, rfl⟩`. Conclude with `p.2`.
-/
theorem measurableEmbedding_qrW : MeasurableEmbedding (qrW (N := N)) where
  injective := by
    intro p q h
    exact Subtype.ext (qrMap_injOn p.2 q.2 h)
  measurable := measurable_qrMap.comp measurable_subtype_coe
  measurableSet_image' := by
    intro s hs
    have h1 : MeasurableSet (Subtype.val '' s : Set (UNgrp N × TriCo N)) :=
      (MeasurableEmbedding.subtype_coe measurableSet_qrDom).measurableSet_image' hs
    have h2 : qrW '' s = qrMap '' (Subtype.val '' s) := by
      rw [Set.image_image]; rfl
    rw [h2]
    refine qrMap_measurableSet_image _ h1 ?_
    rintro _ ⟨p, _, rfl⟩
    exact p.2

def nuW (N : ℕ) : Measure (qrDom N) := (gmMeas N).comap qrW

def nuQR (N : ℕ) : Measure (UNgrp N × TriCo N) := (nuW N).map Subtype.val

/- English proof (translation)
Rewrite using `[nuW, measurableEmbedding_qrW.map_comap, range_qrW]`.
-/
theorem map_qrW_nuW : (nuW N).map qrW = (gmMeas N).restrict (glSet N) := by
  rw [nuW, measurableEmbedding_qrW.map_comap, range_qrW]

/- English proof (translation)
Rewrite using `[nuQR, Measure.map_map measurable_qrMap measurable_subtype_coe]`. Conclude with `map_qrW_nuW`.
-/
theorem map_qrMap_nuQR : (nuQR N).map qrMap = (gmMeas N).restrict (glSet N) := by
  rw [nuQR, Measure.map_map measurable_qrMap measurable_subtype_coe]
  exact map_qrW_nuW

/- English proof (translation)
Rewrite using `[nuQR, Measure.map_apply measurable_subtype_coe hs, nuW, measurableEmbedding_qrW.comap_apply]`.
-/
theorem nuQR_apply (s : Set (UNgrp N × TriCo N)) (hs : MeasurableSet s) :
    nuQR N s = gmMeas N (qrW '' (Subtype.val ⁻¹' s)) := by
  rw [nuQR, Measure.map_apply measurable_subtype_coe hs, nuW, measurableEmbedding_qrW.comap_apply]

/- English proof (translation)
Set `φW : qrDom N → qrDom N` to `fun p => ⟨φ p.1, hφW p.1 p.2⟩`. Establish `hφWm : Measurable φW` using `(hφ.comp measurable_subtype_coe).subtype_mk`. Establish `key : (nuW N).map φW = nuW N`. Establish `h1 : ((nuW N).map φW).map qrW = (nuW N).map qrW`. Rewrite using `[Measure.map_map measurableEmbedding_qrW.measurable hφWm]`.

Establish `hc : qrW ∘ φW = ψ ∘ qrW`. Use function extensionality and compare the values at `p`. Conclude with `hcomm p.1 p.2`. Rewrite using `[hc, ← Measure.map_map hψ measurableEmbedding_qrW.measurable, map_qrW_nuW]`. Use `conv_lhs => rw [← hψG]`.

Rewrite using `[← Measure.restrict_map hψ measurableSet_glSet, hψm]`. Establish `h2` using `congrArg (fun m => m.comap qrW) h1`. Simplify using `only [measurableEmbedding_qrW.comap_map] at h2`. Conclude with `h2`. Rewrite using `[nuQR, Measure.map_map hφ measurable_subtype_coe]`.

Establish `: φ ∘ Subtype.val = Subtype.val ∘ φW` using `rfl`. Rewrite using `[this, ← Measure.map_map measurable_subtype_coe hφWm, key]`.
-/
theorem nuQR_map_eq (φ : UNgrp N × TriCo N → UNgrp N × TriCo N) (hφ : Measurable φ)
    (hφW : ∀ p ∈ qrDom N, φ p ∈ qrDom N) (ψ : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ))
    (hψ : Measurable ψ) (hψm : (gmMeas N).map ψ = gmMeas N) (hψG : ψ ⁻¹' glSet N = glSet N)
    (hcomm : ∀ p ∈ qrDom N, qrMap (φ p) = ψ (qrMap p)) :
    (nuQR N).map φ = nuQR N := by
  let φW : qrDom N → qrDom N := fun p => ⟨φ p.1, hφW p.1 p.2⟩
  have hφWm : Measurable φW := (hφ.comp measurable_subtype_coe).subtype_mk
  have key : (nuW N).map φW = nuW N := by
    have h1 : ((nuW N).map φW).map qrW = (nuW N).map qrW := by
      rw [Measure.map_map measurableEmbedding_qrW.measurable hφWm]
      have hc : qrW ∘ φW = ψ ∘ qrW := by
        funext p; exact hcomm p.1 p.2
      rw [hc, ← Measure.map_map hψ measurableEmbedding_qrW.measurable, map_qrW_nuW]
      conv_lhs => rw [← hψG]
      rw [← Measure.restrict_map hψ measurableSet_glSet, hψm]
    have h2 := congrArg (fun m => m.comap qrW) h1
    simp only [measurableEmbedding_qrW.comap_map] at h2
    exact h2
  rw [nuQR, Measure.map_map hφ measurable_subtype_coe]
  have : φ ∘ Subtype.val = Subtype.val ∘ φW := rfl
  rw [this, ← Measure.map_map measurable_subtype_coe hφWm, key]

/- English proof (translation)
The claim follows from `((Matrix.isUnit_iff_isUnit_det _).mp (k : (Matrix (Fin N) (Fin N) ℂ)ˣ).isUnit).ne_zero`.
-/
theorem det_toM_ne_zero (k : UNgrp N) : (toM k).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (k : (Matrix (Fin N) (Fin N) ℂ)ˣ).isUnit).ne_zero

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular]`. Simplify using `[upMat]`. Introduce `a b hba`. Establish `h1 : a ≠ b` using `ne_of_gt hba`. Establish `h2 : ¬ a < b` using `not_lt.mpr (le_of_lt hba)`.

Simplify using `[upMat, h1, h2]`.
-/
theorem det_upMat (t : TriCo N) : (upMat t).det = ∏ j, ((t.1 j : ℝ) : ℂ) := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upMat]
  · intro a b hba
    have h1 : a ≠ b := ne_of_gt hba
    have h2 : ¬ a < b := not_lt.mpr (le_of_lt hba)
    simp [upMat, h1, h2]

/- English proof (translation)
Rewrite using `[det_upMat]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun j _ => by`. Conclude with `(ne_of_gt (ht j))` after adjusting the coercions.
-/
theorem det_upMat_ne_zero (t : TriCo N) (ht : t ∈ triPos N) : (upMat t).det ≠ 0 := by
  rw [det_upMat]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => by
    exact_mod_cast (ne_of_gt (ht j))

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [upMat]`. Use `split_ifs with h1 h2`. Conclude with `Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)`. Conclude with `(continuous_apply _).comp continuous_snd`.

Conclude with `continuous_const`.
-/
theorem continuous_upMat : Continuous (upMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [upMat]
  split_ifs with h1 h2
  · exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const

/- English proof (translation)
Use `Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun ab => ?_)` and prove the remaining obligations. Conclude with `Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply j))`. Conclude with `(continuous_apply _).comp (continuous_apply _)`.
-/
theorem continuous_triCoOf : Continuous (triCoOf (N := N)) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun ab => ?_)
  · exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply j))
  · exact (continuous_apply _).comp (continuous_apply _)

def triR (t0 : TriCo N) (t : TriCo N) : TriCo N := triCoOf (upMat t * upMat t0)

/- English proof (translation)
The claim follows from `continuous_triCoOf.comp (continuous_upMat.matrix_mul continuous_const)`.
-/
theorem continuous_triR (t0 : TriCo N) : Continuous (triR t0) :=
  continuous_triCoOf.comp (continuous_upMat.matrix_mul continuous_const)

/- English proof (translation)
Establish `hc : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)`. Conclude with `(continuous_const.matrix_mul continuous_id : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => g * Z)`. Conclude with `hc.measurable`.
-/
theorem measurable_mulLeft_mat (g : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z) := by
  have hc : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z) := by
    exact (continuous_const.matrix_mul continuous_id : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => g * Z)
  exact hc.measurable

/- English proof (translation)
Establish `hc : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)`. Conclude with `(continuous_id.matrix_mul continuous_const : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => Z * g)`. Conclude with `hc.measurable`.
-/
theorem measurable_mulRight_mat (g : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g) := by
  have hc : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g) := by
    exact (continuous_id.matrix_mul continuous_const : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => Z * g)
  exact hc.measurable

/- English proof (translation)
Use `nuQR_map_eq _ ((measurable_const_mul k0).comp measurable_fst |>.prodMk measurable_snd) (fun p hp => ⟨trivial, hp.2⟩) (fun Z => Matrix.of.symm (toM k0 * Matrix.of Z)) (measurable_mulLeft_mat _) (gmMeas_map_mul_left _ (det_toM_ne_zero k0)) ?_ ?_` and prove the remaining obligations. Use extensionality with `Z`. Simplify using `only [glSet, Set.mem_preimage, Set.mem_ofPred_eq]`. Express the relevant statement in the definitionally equal form `(toM k0 * Matrix.of Z).det ≠ 0 ↔ _`. Rewrite using `[Matrix.det_mul]`.

Conclude with `⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (det_toM_ne_zero k0) h⟩`. Introduce `p _`. Simplify using `only [qrMap]`. Express the relevant statement in the definitionally equal form `Matrix.of.symm (toM (k0 * p.1) * upMat p.2) = Matrix.of.symm (toM k0 * (toM p.1 * upMat p.2))`. Rewrite using `[← Matrix.mul_assoc]`.

Both sides reduce to the same expression.
-/
theorem nuQR_map_left (k0 : UNgrp N) :
    (nuQR N).map (fun p : UNgrp N × TriCo N => (k0 * p.1, p.2)) = nuQR N := by
  refine nuQR_map_eq _ ((measurable_const_mul k0).comp measurable_fst |>.prodMk measurable_snd)
    (fun p hp => ⟨trivial, hp.2⟩) (fun Z => Matrix.of.symm (toM k0 * Matrix.of Z))
    (measurable_mulLeft_mat _) (gmMeas_map_mul_left _ (det_toM_ne_zero k0)) ?_ ?_
  · ext Z
    simp only [glSet, Set.mem_preimage, Set.mem_ofPred_eq]
    change (toM k0 * Matrix.of Z).det ≠ 0 ↔ _
    rw [Matrix.det_mul]
    exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (det_toM_ne_zero k0) h⟩
  · intro p _
    simp only [qrMap]
    change Matrix.of.symm (toM (k0 * p.1) * upMat p.2) = Matrix.of.symm (toM k0 * (toM p.1 * upMat p.2))
    rw [← Matrix.mul_assoc]; rfl

/- English proof (translation)
Use `nuQR_map_eq _ (measurable_fst.prodMk ((continuous_triR t0).measurable.comp measurable_snd)) ?_ (fun Z => Matrix.of.symm (Matrix.of Z * upMat t0)) (measurable_mulRight_mat _) (gmMeas_map_mul_right _ (det_upMat_ne_zero t0 h0)) ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Use `⟨trivial, fun j => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `0 < (triR t0 p.2).1 j`. Rewrite using `[triR, (upMat_triCoOf_mul p.2 t0).2 j]`.

Conclude with `mul_pos (hp.2 j) (h0 j)`. Use extensionality with `Z`. Simplify using `only [glSet, Set.mem_preimage, Set.mem_ofPred_eq]`. Express the relevant statement in the definitionally equal form `(Matrix.of Z * upMat t0).det ≠ 0 ↔ _`. Rewrite using `[Matrix.det_mul]`.

Conclude with `⟨fun h => left_ne_zero_of_mul h, fun h => mul_ne_zero h (det_upMat_ne_zero t0 h0)⟩`. Introduce `p _`. Simplify using `only [qrMap, triR]`. Rewrite using `[(upMat_triCoOf_mul p.2 t0).1]`. Express the relevant statement in the definitionally equal form `Matrix.of.symm (toM p.1 * (upMat p.2 * upMat t0)) = Matrix.of.symm ((toM p.1 * upMat p.2) * upMat t0)`.

Rewrite using `[Matrix.mul_assoc]`.
-/
theorem nuQR_map_right (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    (nuQR N).map (fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2)) = nuQR N := by
  refine nuQR_map_eq _ (measurable_fst.prodMk ((continuous_triR t0).measurable.comp measurable_snd))
    ?_ (fun Z => Matrix.of.symm (Matrix.of Z * upMat t0))
    (measurable_mulRight_mat _) (gmMeas_map_mul_right _ (det_upMat_ne_zero t0 h0)) ?_ ?_
  · intro p hp
    refine ⟨trivial, fun j => ?_⟩
    change 0 < (triR t0 p.2).1 j
    rw [triR, (upMat_triCoOf_mul p.2 t0).2 j]
    exact mul_pos (hp.2 j) (h0 j)
  · ext Z
    simp only [glSet, Set.mem_preimage, Set.mem_ofPred_eq]
    change (Matrix.of Z * upMat t0).det ≠ 0 ↔ _
    rw [Matrix.det_mul]
    exact ⟨fun h => left_ne_zero_of_mul h, fun h => mul_ne_zero h (det_upMat_ne_zero t0 h0)⟩
  · intro p _
    simp only [qrMap, triR]
    rw [(upMat_triCoOf_mul p.2 t0).1]
    change Matrix.of.symm (toM p.1 * (upMat p.2 * upMat t0)) = Matrix.of.symm ((toM p.1 * upMat p.2) * upMat t0)
    rw [Matrix.mul_assoc]

def kap (N : ℕ) : Measure (TriCo N) := (nuQR N).map Prod.snd

/- English proof (translation)
Rewrite using `[kap, Measure.map_apply measurable_snd measurableSet_triPos.compl, nuQR_apply _ (measurable_snd measurableSet_triPos.compl)]`. Establish `: (Subtype.val ⁻¹' (Prod.snd ⁻¹' (triPos N)ᶜ) : Set (qrDom N)) = ∅` using `Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp p.2.2`. Rewrite using `[this, Set.image_empty, measure_empty]`.
-/
theorem kap_compl : kap N (triPos N)ᶜ = 0 := by
  rw [kap, Measure.map_apply measurable_snd measurableSet_triPos.compl,
    nuQR_apply _ (measurable_snd measurableSet_triPos.compl)]
  have : (Subtype.val ⁻¹' (Prod.snd ⁻¹' (triPos N)ᶜ) : Set (qrDom N)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp p.2.2
  rw [this, Set.image_empty, measure_empty]

/- English proof (translation)
Establish `hKm : MeasurableSet K` using `hK.isClosed.measurableSet`. Rewrite using `[kap, Measure.map_apply measurable_snd hKm, nuQR_apply _ (measurable_snd hKm)]`. Use `lt_of_le_of_lt (measure_mono ?_) (gmMeas_compact_lt_top (qrMap '' (Set.univ ×ˢ K)) ((isCompact_univ.prod hK).image qrMap_continuous) ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `⟨p.1, ⟨trivial, hp⟩, rfl⟩`.

Introduce and unpack `_ ⟨p, hp, rfl⟩`. Establish `: qrMap p ∈ qrMap '' (Set.univ ×ˢ triPos N)` using `⟨p, ⟨trivial, hKs hp.2⟩, rfl⟩`. Rewrite `this` using `[qrMap_image]`. Conclude with `this`.
-/
theorem kap_compact [CompactSpace (UNgrp N)] (K : Set (TriCo N)) (hK : IsCompact K)
    (hKs : K ⊆ triPos N) : kap N K < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [kap, Measure.map_apply measurable_snd hKm, nuQR_apply _ (measurable_snd hKm)]
  refine lt_of_le_of_lt (measure_mono ?_) (gmMeas_compact_lt_top (qrMap '' (Set.univ ×ˢ K))
    ((isCompact_univ.prod hK).image qrMap_continuous) ?_)
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.1, ⟨trivial, hp⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    have : qrMap p ∈ qrMap '' (Set.univ ×ˢ triPos N) := ⟨p, ⟨trivial, hKs hp.2⟩, rfl⟩
    rw [qrMap_image] at this
    exact this

/- English proof (translation)
Establish `hm : Measurable fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2)` using `measurable_fst.prodMk ((continuous_triR t0).measurable.comp measurable_snd)`. Rewrite using `[kap, Measure.map_map (continuous_triR t0).measurable measurable_snd]`. Establish `: triR t0 ∘ Prod.snd = Prod.snd ∘ (fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2))` using `rfl`. Rewrite using `[this, ← Measure.map_map measurable_snd hm, nuQR_map_right t0 h0]`.
-/
theorem kap_inv (t0 : TriCo N) (h0 : t0 ∈ triPos N) : (kap N).map (triR t0) = kap N := by
  have hm : Measurable fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2) :=
    measurable_fst.prodMk ((continuous_triR t0).measurable.comp measurable_snd)
  rw [kap, Measure.map_map (continuous_triR t0).measurable measurable_snd]
  have : triR t0 ∘ Prod.snd = Prod.snd ∘ (fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2)) := rfl
  rw [this, ← Measure.map_map measurable_snd hm, nuQR_map_right t0 h0]

/- English proof (translation)
The claim follows from `triMeas_unique (kap N) kap_compl kap_compact (fun t0 h0 => kap_inv t0 h0)`.
-/
theorem kap_eq [CompactSpace (UNgrp N)] : ∃ c : ENNReal, c ≠ ⊤ ∧ kap N = c • triMeas N :=
  triMeas_unique (kap N) kap_compl kap_compact (fun t0 h0 => kap_inv t0 h0)

/- English proof (translation)
Use `set ρ : Measure (UNgrp N) := ((nuQR N).restrict (Prod.snd ⁻¹' t)).map Prod.fst with hρ`. Establish `hρA : ∀ A, MeasurableSet A → ρ A = nuQR N (A ×ˢ t)`. Introduce `A hA`. Rewrite using `[hρ, Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]`. Both sides reduce to the same expression.

Establish `hρu : ρ Set.univ = kap N t`. Rewrite using `[hρA _ MeasurableSet.univ, kap, Measure.map_apply measurable_snd ht, Set.univ_prod]`. Establish `: IsFiniteMeasure ρ` using `⟨by rw [hρu]; exact hfin⟩`. Establish `: ρ.IsMulLeftInvariant` using `⟨fun g => by`. Establish `hL : Measurable fun p : UNgrp N × TriCo N => (g * p.1, p.2)` using `((measurable_const_mul g).comp measurable_fst).prodMk measurable_snd`.

Rewrite using `[hρ, Measure.map_map (measurable_const_mul g) measurable_fst]`. Establish `: (fun x => g * x) ∘ Prod.fst = Prod.fst ∘ (fun p : UNgrp N × TriCo N => (g * p.1, p.2))` using `rfl`. Rewrite using `[this, ← Measure.map_map measurable_fst hL]`. Use `congr 1`. Use `Measure.restrict_map (μ := nuQR N) hL (measurable_snd ht)` as an intermediate fact.

Rewrite `this` using `[nuQR_map_left]`. Conclude with `this.symm⟩`. Establish `hsm` using `Measure.isMulInvariant_eq_smul_of_compactSpace ρ μ`. Establish `hc : ρ.haarScalarFactor μ = kap N t`. Use `congrArg (fun m : Measure (UNgrp N) => m Set.univ) hsm` as an intermediate fact.

Simplify using `only [Measure.smul_apply, measure_univ] at this`. Rewrite using `[← hρu, this]`. Simplify using the standard rewrite rules. Rewrite using `[← hρA s hs, hsm, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, mul_comm]`.
-/
theorem nuQR_rect (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    [CompactSpace (UNgrp N)] (s : Set (UNgrp N)) (hs : MeasurableSet s) (t : Set (TriCo N))
    (ht : MeasurableSet t) (hfin : kap N t < ⊤) : nuQR N (s ×ˢ t) = μ s * kap N t := by
  set ρ : Measure (UNgrp N) := ((nuQR N).restrict (Prod.snd ⁻¹' t)).map Prod.fst with hρ
  have hρA : ∀ A, MeasurableSet A → ρ A = nuQR N (A ×ˢ t) := by
    intro A hA
    rw [hρ, Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
    rfl
  have hρu : ρ Set.univ = kap N t := by
    rw [hρA _ MeasurableSet.univ, kap, Measure.map_apply measurable_snd ht, Set.univ_prod]
  have : IsFiniteMeasure ρ := ⟨by rw [hρu]; exact hfin⟩
  have : ρ.IsMulLeftInvariant := ⟨fun g => by
    have hL : Measurable fun p : UNgrp N × TriCo N => (g * p.1, p.2) :=
      ((measurable_const_mul g).comp measurable_fst).prodMk measurable_snd
    rw [hρ, Measure.map_map (measurable_const_mul g) measurable_fst]
    have : (fun x => g * x) ∘ Prod.fst =
        Prod.fst ∘ (fun p : UNgrp N × TriCo N => (g * p.1, p.2)) := rfl
    rw [this, ← Measure.map_map measurable_fst hL]
    congr 1
    have := Measure.restrict_map (μ := nuQR N) hL (measurable_snd ht)
    rw [nuQR_map_left] at this
    exact this.symm⟩
  have hsm := Measure.isMulInvariant_eq_smul_of_compactSpace ρ μ
  have hc : ρ.haarScalarFactor μ = kap N t := by
    have := congrArg (fun m : Measure (UNgrp N) => m Set.univ) hsm
    simp only [Measure.smul_apply, measure_univ] at this
    rw [← hρu, this]
    simp
  rw [← hρA s hs, hsm, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, mul_comm]

/- English proof (translation)
Use `Measure.prod_eq_generateFrom (C := {s | MeasurableSet s}) (D := {t | MeasurableSet t ∧ kap N t < ⊤}) MeasurableSpace.generateFrom_measurableSet ?_ MeasurableSpace.isPiSystem_measurableSet ?_ μ.toFiniteSpanningSetsIn ((kap N).toFiniteSpanningSetsIn.mono' fun t ht => ⟨ht.1, ht.2⟩) …` and prove the remaining obligations. Use `le_antisymm (MeasurableSpace.generateFrom_le fun t ht => ht.1) fun t ht => ?_` and prove the remaining obligations. Rewrite using `[← Set.inter_univ t, ← iUnion_spanningSets (kap N), Set.inter_iUnion]`. Conclude with `MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom ⟨ht.inter (measurableSet_spanningSets (kap N) n), lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_spanningSets_lt_top (kap N) n)⟩`. Introduce `s hs t ht _`.

Conclude with `⟨hs.1.inter ht.1, lt_of_le_of_lt (measure_mono Set.inter_subset_left) hs.2⟩`. Introduce `s hs t ht`. Conclude with `nuQR_rect μ s hs t ht.1 ht.2`.
-/
theorem nuQR_eq_prod (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    [CompactSpace (UNgrp N)] [SigmaFinite (kap N)] : μ.prod (kap N) = nuQR N := by
  refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
    (D := {t | MeasurableSet t ∧ kap N t < ⊤}) MeasurableSpace.generateFrom_measurableSet ?_
    MeasurableSpace.isPiSystem_measurableSet ?_ μ.toFiniteSpanningSetsIn
    ((kap N).toFiniteSpanningSetsIn.mono' fun t ht => ⟨ht.1, ht.2⟩) ?_
  · refine le_antisymm (MeasurableSpace.generateFrom_le fun t ht => ht.1) fun t ht => ?_
    rw [← Set.inter_univ t, ← iUnion_spanningSets (kap N), Set.inter_iUnion]
    exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
      ⟨ht.inter (measurableSet_spanningSets (kap N) n),
        lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_spanningSets_lt_top (kap N) n)⟩
  · intro s hs t ht _
    exact ⟨hs.1.inter ht.1, lt_of_le_of_lt (measure_mono Set.inter_subset_left) hs.2⟩
  · intro s hs t ht
    exact nuQR_rect μ s hs t ht.1 ht.2

/- English proof (translation)
Unfold `gmDens`. Conclude with `(by fun_prop : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ (-(2 * (N:ℤ))))).comp continuous_det_of.measurable`.
-/
theorem measurable_gmDens : Measurable (gmDens N) := by
  unfold gmDens
  exact (by fun_prop : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ (-(2 * (N:ℤ))))).comp
    continuous_det_of.measurable

/- English proof (translation)
Unfold `triDens`. Use `fun_prop`.
-/
theorem measurable_triDens : Measurable (triDens (N := N)) := by
  unfold triDens
  fun_prop

/- English proof (translation)
Establish `hk : inUJ (fun _ : Fin N => true) (toM k)` using `k.2`. Establish `hJ : Jm (fun _ : Fin N => true) = 1`. Unfold `Jm`. Simplify using the standard rewrite rules. Unfold `inUJ at hk`.

Rewrite `hk` using `[hJ, Matrix.mul_one]`. Establish `h1` using `congrArg Matrix.det hk`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]`. Establish `h2 : Complex.normSq (toM k).det = 1`. Establish `h3` using `Complex.normSq_eq_conj_mul_self (z := (toM k).det)`.

Establish `h4 : ((Complex.normSq (toM k).det : ℝ) : ℂ) = 1` using `by rw [h3]; exact h1`. Conclude with `h4` after adjusting the coercions. Establish `h5 : ‖(toM k).det‖ ^ 2 = 1` using `by rw [Complex.sq_norm, h2]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5`.
-/
theorem norm_det_toM (k : UNgrp N) : ‖(toM k).det‖ = 1 := by
  have hk : inUJ (fun _ : Fin N => true) (toM k) := k.2
  have hJ : Jm (fun _ : Fin N => true) = 1 := by
    unfold Jm; simp
  unfold inUJ at hk
  rw [hJ, Matrix.mul_one] at hk
  have h1 := congrArg Matrix.det hk
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h1
  have h2 : Complex.normSq (toM k).det = 1 := by
    have h3 := Complex.normSq_eq_conj_mul_self (z := (toM k).det)
    have h4 : ((Complex.normSq (toM k).det : ℝ) : ℂ) = 1 := by rw [h3]; exact h1
    exact_mod_cast h4
  have h5 : ‖(toM k).det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h2]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5

/- English proof (translation)
Establish `hn : ‖(Matrix.of Z).det‖ ≠ 0` using `norm_ne_zero_iff.mpr hZ`. Rewrite using `[gmDens, ← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← zpow_natCast, ← zpow_add₀ hn]`. Use `push_cast`. Simplify using the standard rewrite rules.
-/
theorem gmDens_mul (Z : Fin N → Fin N → ℂ) (hZ : Z ∈ glSet N) :
    gmDens N Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) = 1 := by
  have hn : ‖(Matrix.of Z).det‖ ≠ 0 := norm_ne_zero_iff.mpr hZ
  rw [gmDens, ← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← zpow_natCast,
    ← zpow_add₀ hn]
  push_cast
  simp

/- English proof (translation)
Establish `hpos : ∀ j, 0 ≤ t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1))` using `fun j => zpow_nonneg (ht j).le _`. Rewrite using `[triDens, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hpos j), ← Finset.prod_pow, ← Finset.prod_mul_distrib, qrWt]`. Use `congr 1`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hj` using `j.2`.

Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ne_of_gt (ht j))]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem triDens_mul (t : TriCo N) (ht : t ∈ triPos N) :
    triDens t * ENNReal.ofReal ((∏ j, t.1 j) ^ (2 * N)) = ENNReal.ofReal (qrWt t) := by
  have hpos : ∀ j, 0 ≤ t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1)) := fun j => zpow_nonneg (ht j).le _
  rw [triDens, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hpos j), ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, qrWt]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := j.2
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ne_of_gt (ht j))]
  congr 1
  omega

/- English proof (translation)
Use `congr 2`. Establish `: Matrix.of (qrMap (k, t)) = toM k * upMat t`. Simplify using `[qrMap]`. Rewrite using `[this, Matrix.det_mul, norm_mul, norm_det_toM, one_mul, det_upMat, norm_prod]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (ht j).le]`.
-/
theorem d_qrMap (k : UNgrp N) (t : TriCo N) (ht : t ∈ triPos N) :
    ENNReal.ofReal (‖(Matrix.of (qrMap (k, t))).det‖ ^ (2 * N)) =
      ENNReal.ofReal ((∏ j, t.1 j) ^ (2 * N)) := by
  congr 2
  have : Matrix.of (qrMap (k, t)) = toM k * upMat t := by
    simp [qrMap]
  rw [this, Matrix.det_mul, norm_mul, norm_det_toM, one_mul, det_upMat, norm_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (ht j).le]

end ReciprocityTheory.ChartRestriction.DS.QRH
