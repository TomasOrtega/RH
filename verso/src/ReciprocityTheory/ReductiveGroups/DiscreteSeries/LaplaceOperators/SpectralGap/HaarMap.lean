import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ClosedSubgroupsStatement
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ

noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

namespace ConjugationHaarMap

variable {k r : ℕ}

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hP`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hP`. Establish `hc1 : Continuous (fun x : Mat k r => ((P⁻¹ * x * P : Mat k r) : Mt k r))` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Establish `hc2 : Continuous (fun y : Mt k r => ((P * (show Mat k r from y) * P⁻¹ : Mat k r) : Mat k r))` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Set `e : Mat k r ≃ Mt k r` to `{ toFun := fun x => ((P⁻¹ * x * P : Mat k r) : Mt k r) invFun := fun y => ((P * (show Mat k r from y) * P⁻¹ : Mat k r) : Mat k r) left_inv := fun x => by show P * (P⁻¹ * x * P) * P⁻¹ = x`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]`. Use `right_inv := fun y => by show P⁻¹ * (P * (show Mat k r from y) * P⁻¹) * P = (show Mat k r from y)`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one] }`. Conclude with `(Homeomorph.mk e hc1 hc2).isClosedEmbedding`.
-/
theorem conj_closedEmb (P : Mat k r) (hP : IsUnit P.det) :
    IsClosedEmbedding (fun x : Mat k r => ((P⁻¹ * x * P : Mat k r) : Mt k r)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hc1 : Continuous (fun x : Mat k r => ((P⁻¹ * x * P : Mat k r) : Mt k r)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hc2 : Continuous (fun y : Mt k r => ((P * (show Mat k r from y) * P⁻¹ : Mat k r) : Mat k r)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let e : Mat k r ≃ Mt k r :=
    { toFun := fun x => ((P⁻¹ * x * P : Mat k r) : Mt k r)
      invFun := fun y => ((P * (show Mat k r from y) * P⁻¹ : Mat k r) : Mat k r)
      left_inv := fun x => by
        show P * (P⁻¹ * x * P) * P⁻¹ = x
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
      right_inv := fun y => by
        show P⁻¹ * (P * (show Mat k r from y) * P⁻¹) * P = (show Mat k r from y)
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one] }
  exact (Homeomorph.mk e hc1 hc2).isClosedEmbedding

/- English proof (translation)
Establish `hJ : (Formalism.REAL.Jm ε).det ≠ 0`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.det_diagonal]`. Apply the tactic sequence `exact Finset.prod_ne_zero_iff.mpr (fun a _ => by split_ifs <;> norm_num)`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Establish `h` using `congrArg Matrix.det (show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε from hM)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Conclude with `hJ h.symm`.
-/
private theorem det_unit_of_inUJ_lemma {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Formalism.REAL.inUJ ε M) : IsUnit M.det := by
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by split_ifs <;> norm_num)
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := congrArg Matrix.det (show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε from hM)
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
  exact hJ h.symm

/- English proof (translation)
Establish `hinvc : ContinuousOn (fun A : Mat k r => A⁻¹) {A : Mat k r | IsUnit A}`. Establish `he : (fun A : Mat k r => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate`. Use function extensionality and compare the values at `A`. Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv']`. Rewrite using `[he]`.

Establish `hid : Continuous fun A : Mat k r => A` using `continuous_id`. Conclude with `(ContinuousOn.inv₀ hid.matrix_det.continuousOn (fun A hA => ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero)).smul hid.matrix_adjugate.continuousOn`. Establish `hval : IsEmbedding (Units.val : (Mat k r)ˣ → Mat k r)` using `Units.isEmbedding_val_mk' hinvc (fun u => (Matrix.coe_units_inv u).symm)`. Establish `hU : IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g)`. Use `⟨hval.comp IsEmbedding.subtypeVal, ?_⟩` and prove the remaining obligations.

Establish `hr : Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) = {M : Mat k r | Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε}`. Use extensionality with `M`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `g.2`.

Introduce `hM`. Conclude with `⟨⟨M.nonsingInvUnit (det_unit_of_inUJ_lemma ε M hM), hM⟩, rfl⟩`. Rewrite using `[hr]`. Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Conclude with `(conj_closedEmb P hP).comp hU`.
-/
theorem phi_closedEmb (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hP : IsUnit P.det) :
    IsClosedEmbedding
      (fun g : Formalism.REAL.UJ ε => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)) := by
  have hinvc : ContinuousOn (fun A : Mat k r => A⁻¹) {A : Mat k r | IsUnit A} := by
    have he : (fun A : Mat k r => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
      funext A
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [he]
    have hid : Continuous fun A : Mat k r => A := continuous_id
    exact (ContinuousOn.inv₀ hid.matrix_det.continuousOn
      (fun A hA => ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero)).smul hid.matrix_adjugate.continuousOn
  have hval : IsEmbedding (Units.val : (Mat k r)ˣ → Mat k r) :=
    Units.isEmbedding_val_mk' hinvc (fun u => (Matrix.coe_units_inv u).symm)
  have hU : IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := by
    refine ⟨hval.comp IsEmbedding.subtypeVal, ?_⟩
    have hr : Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) =
        {M : Mat k r | Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε} := by
      ext M
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hM
        exact ⟨⟨M.nonsingInvUnit (det_unit_of_inUJ_lemma ε M hM), hM⟩, rfl⟩
    rw [hr]
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  exact (conj_closedEmb P hP).comp hU

/- English proof (translation)
Take `⟨hPu, hPJ⟩` from `hC`. Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hPu`. Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hd`. Establish `h2 : (P⁻¹)ᴴ * Pᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]`.

Establish `hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε` using `hg`. Use `show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r`. Rewrite using `[← hPJ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Pᴴ * Formalism.REAL.Jm ε * P := by`. Rewrite using `[h1, h2, Matrix.mul_one, Matrix.mul_one, hg', Matrix.mul_assoc]`.
-/
theorem phi_mem (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hC : Formalism.MainNotions.S.IsCayley k r ε P)
    (g : Mat k r) (hg : Formalism.REAL.inUJ ε g) : P⁻¹ * g * P ∈ UH (Hpk k r) := by
  obtain ⟨hPu, hPJ⟩ := hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
  rw [← hPJ]
  calc (P⁻¹ * g * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * g * P)
      = Pᴴ * ((gᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) * g)) * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hg', Matrix.mul_assoc]

/- English proof (translation)
Take `⟨hPu, hPJ⟩` from `hC`. Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hPu`. Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hd`. Establish `h2 : (P⁻¹)ᴴ * Pᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]`.

Establish `hs' : sᴴ * Hpk k r * s = Hpk k r` using `hs`. Use `show (P * s * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * s * P⁻¹) = Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPJ, hs']`.

Use `_ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem conj_mem (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hC : Formalism.MainNotions.S.IsCayley k r ε P)
    (s : Mat k r) (hs : s ∈ UH (Hpk k r)) : Formalism.REAL.inUJ ε (P * s * P⁻¹) := by
  obtain ⟨hPu, hPJ⟩ := hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  show (P * s * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * s * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * s * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * s * P⁻¹)
      = (P⁻¹)ᴴ * (sᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * s) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPJ, hs']
    _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end ConjugationHaarMap

/- English proof (translation)
Introduce `k r ε P hC`. Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hC.1`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hd`. Establish `h2' : ∀ X : Mat k r, P⁻¹ * (P * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, h2, Matrix.one_mul]`.

Set `φ : Formalism.REAL.UJ ε → Mt k r` to `fun g => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)`. Establish `hφ : IsClosedEmbedding φ` using `ConjugationHaarMap.phi_closedEmb ε P hd`. Establish `hme : MeasurableEmbedding φ` using `hφ.measurableEmbedding`. Use `show Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ((Measure.haar : Measure (Formalism.REAL.UJ ε)).map φ)`. Unfold `Formalism.MainNotions.S.IsHaarOn`.

Use `⟨hme.sigmaFinite_map, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Measure.map_eq_zero_iff hme.measurable.aemeasurable]`. Conclude with `Measure.measure_univ_pos.mp (isOpen_univ.measure_pos _ Set.univ_nonempty)`. Rewrite using `[hme.map_apply]`. Establish `hE : φ ⁻¹' {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} = ∅`.

Use `Set.subset_empty_iff.mp ?_` and prove the remaining obligations. Introduce `g hg`. Conclude with `absurd (ConjugationHaarMap.phi_mem ε P hC (Formalism.MainNotions.S.umat g) g.2) hg`. Rewrite using `[hE, measure_empty]`. Introduce `s hs`.

Establish `hsJ` using `ConjugationHaarMap.conj_mem ε P hC s hs`. Set `g₀ : Formalism.REAL.UJ ε` to `⟨(P * s * P⁻¹).nonsingInvUnit (ConjugationHaarMap.det_unit_of_inUJ_lemma ε _ hsJ), hsJ⟩`. Establish `hcl : Continuous (Formalism.QuantumDeterminants.lmulM (k` using `k) (r := r) s) := continuous_const.matrix_mul continuous_id`. Establish `hcomp : Formalism.QuantumDeterminants.lmulM s ∘ φ = φ ∘ (fun g => g₀ * g)`. Use function extensionality and compare the values at `g`.

Use `show s * (P⁻¹ * Formalism.MainNotions.S.umat g * P) = P⁻¹ * ((P * s * P⁻¹) * Formalism.MainNotions.S.umat g) * P`. Simplify using `only [Matrix.mul_assoc, h2']`. Rewrite using `[Measure.map_map hcl.measurable hme.measurable, hcomp, ← Measure.map_map hme.measurable (continuous_mul_left g₀).measurable, map_mul_left_eq_self]`.
-/
theorem haarMap : HaarMapStatement := by
  intro k r ε P hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hC.1
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have h2' : ∀ X : Mat k r, P⁻¹ * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  let φ : Formalism.REAL.UJ ε → Mt k r := fun g => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)
  have hφ : IsClosedEmbedding φ := ConjugationHaarMap.phi_closedEmb ε P hd
  have hme : MeasurableEmbedding φ := hφ.measurableEmbedding
  show Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ((Measure.haar : Measure (Formalism.REAL.UJ ε)).map φ)
  unfold Formalism.MainNotions.S.IsHaarOn
  refine ⟨hme.sigmaFinite_map, ?_, ?_, ?_⟩
  · rw [Ne, Measure.map_eq_zero_iff hme.measurable.aemeasurable]
    exact Measure.measure_univ_pos.mp (isOpen_univ.measure_pos _ Set.univ_nonempty)
  · rw [hme.map_apply]
    have hE : φ ⁻¹' {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} = ∅ := by
      refine Set.subset_empty_iff.mp ?_
      intro g hg
      exact absurd (ConjugationHaarMap.phi_mem ε P hC (Formalism.MainNotions.S.umat g) g.2) hg
    rw [hE, measure_empty]
  · intro s hs
    have hsJ := ConjugationHaarMap.conj_mem ε P hC s hs
    let g₀ : Formalism.REAL.UJ ε := ⟨(P * s * P⁻¹).nonsingInvUnit (ConjugationHaarMap.det_unit_of_inUJ_lemma ε _ hsJ), hsJ⟩
    have hcl : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := continuous_const.matrix_mul continuous_id
    have hcomp : Formalism.QuantumDeterminants.lmulM s ∘ φ = φ ∘ (fun g => g₀ * g) := by
      funext g
      show s * (P⁻¹ * Formalism.MainNotions.S.umat g * P) = P⁻¹ * ((P * s * P⁻¹) * Formalism.MainNotions.S.umat g) * P
      simp only [Matrix.mul_assoc, h2']
    rw [Measure.map_map hcl.measurable hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_mul_left g₀).measurable, map_mul_left_eq_self]

end ReciprocityTheory.ChartRestriction.DS.Lap
