import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Matrix

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.LeftScale

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def orbO (n d : ℕ) : Set (Matrix (Fin n) (Fin d) k) :=
  {Y | ∃ κ ∈ KO k (Fin d), Y = Y0 k n d * κ.val}

def matInt [MeasurableSpace k] (ν : Measure k) {n d : ℕ} (φ : Matrix (Fin n) (Fin d) k → ℂ) : ℂ :=
  ∫ v : Fin n × Fin d → k, φ (Matrix.of fun i j => v (i, j)) ∂(Measure.pi fun _ => ν)

/- English proof (translation)
Set `K : Matrix (Fin n × Fin d) (Fin n × Fin d) k` to `Matrix.kroneckerMap (· * ·) A.val h.valᵀ`. Establish `hK : K.det = (gdet A : k) ^ d * (gdet h : k) ^ n`. Simplify using `[K, Matrix.det_kronecker]`. Set `G : GL (Fin n × Fin d) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero K (by`. Rewrite using `[hK]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (gdet A).ne_zero) (pow_ne_zero _ (gdet h).ne_zero))`. Establish `hGv : G.val = K` using `rfl`. Establish `hG : Matrix.GeneralLinearGroup.det G = gdet A ^ d * gdet h ^ n` using `Units.ext (by`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hGv, hK]`. Use `push_cast`.

Use the proof step `rfl)`. Establish `key` using `GlobalTheory.WeilM.integral_comp_mulVec ν G (fun v => φ (Matrix.of fun i j => v (i, j)))`. Establish `hv : ∀ v : Fin n × Fin d → k, (Matrix.of fun i j => (G.val *ᵥ v) (i, j)) = A.val * Matrix.of (fun i j => v (i, j)) * h.val`. Introduce `v`. Use extensionality with `i j`.

Rewrite using `[hGv]`. Simplify using `only [K, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations. Simplify using `only [hv] at key`.

Unfold `matInt`. Rewrite using `[← key, hG]`. Simplify using `[nabs]`.
-/
theorem matInt_comp [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {n d : ℕ}
    (A : GL (Fin n) k) (h : GL (Fin d) k) (φ : Matrix (Fin n) (Fin d) k → ℂ) :
    ((nabs k (gdet A) ^ d * nabs k (gdet h) ^ n : ℝ) : ℂ) * matInt ν (fun Y : Matrix (Fin n) (Fin d) k => φ (A.val * Y * h.val)) =
      matInt ν φ := by
  classical
  let K : Matrix (Fin n × Fin d) (Fin n × Fin d) k := Matrix.kroneckerMap (· * ·) A.val h.valᵀ
  have hK : K.det = (gdet A : k) ^ d * (gdet h : k) ^ n := by
    simp [K, Matrix.det_kronecker]
  let G : GL (Fin n × Fin d) k := Matrix.GeneralLinearGroup.mkOfDetNeZero K (by
    rw [hK]; exact mul_ne_zero (pow_ne_zero _ (gdet A).ne_zero) (pow_ne_zero _ (gdet h).ne_zero))
  have hGv : G.val = K := rfl
  have hG : Matrix.GeneralLinearGroup.det G = gdet A ^ d * gdet h ^ n := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hGv, hK]; push_cast; rfl)
  have key := GlobalTheory.WeilM.integral_comp_mulVec ν G (fun v => φ (Matrix.of fun i j => v (i, j)))
  have hv : ∀ v : Fin n × Fin d → k, (Matrix.of fun i j => (G.val *ᵥ v) (i, j)) =
      A.val * Matrix.of (fun i j => v (i, j)) * h.val := by
    intro v; ext i j
    rw [hGv]
    simp only [K, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [hv] at key
  unfold matInt
  rw [← key, hG]
  simp [nabs]

/- English proof (translation)
Use `haveI := SplitWeil.secondCountable k`. Use `haveI := SplitWeil.t2Space k`. Set `e : (Fin n × Fin d → k) ≃ₜ Matrix (Fin n) (Fin d) k` to `{ toEquiv := Equiv.curry _ _ _ continuous_toFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j) continuous_invFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1) }`. Conclude with `(hφ.1.continuous.comp e.continuous).integrable_of_hasCompactSupport (hφ.2.comp_homeomorph e)`.
-/
theorem integrable_of_mem_SB [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {n d : ℕ}
    {φ : Matrix (Fin n) (Fin d) k → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) :
    Integrable (fun v : Fin n × Fin d → k => φ (Matrix.of fun i j => v (i, j))) (Measure.pi fun _ => ν) := by
  haveI := SplitWeil.secondCountable k
  haveI := SplitWeil.t2Space k
  let e : (Fin n × Fin d → k) ≃ₜ Matrix (Fin n) (Fin d) k :=
    { toEquiv := Equiv.curry _ _ _
      continuous_toFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
      continuous_invFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1) }
  exact (hφ.1.continuous.comp e.continuous).integrable_of_hasCompactSupport (hφ.2.comp_homeomorph e)

/- English proof (translation)
Unfold `matInt`. Simplify using `only [Finset.sum_apply]`. Conclude with `integral_finset_sum s fun i hi => integrable_of_mem_SB ν (hf i hi)`.
-/
theorem matInt_sum [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {n d : ℕ}
    {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin d) k → ℂ)
    (hf : ∀ i ∈ s, f i ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) :
    matInt ν (∑ i ∈ s, f i) = ∑ i ∈ s, matInt ν (f i) := by
  unfold matInt
  simp only [Finset.sum_apply]
  exact integral_finset_sum s fun i hi => integrable_of_mem_SB ν (hf i hi)

/- English proof (translation)
Use `⟨comp_mul_mem_SB A h hφ.1, fun Y hY => hφ.2 _ ?_⟩` and prove the remaining obligations. Establish `hA : IsUnit A.val.det` using `(Matrix.isUnit_iff_isUnit_det _).1 A.isUnit`. Establish `hh : IsUnit h.val.det` using `(Matrix.isUnit_iff_isUnit_det _).1 h.isUnit`. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ hh, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hA]` and apply the resulting hypothesis.
-/
theorem comp_mem_fullRk {n d : ℕ} (A : GL (Fin n) k) (h : GL (Fin d) k) {φ : Matrix (Fin n) (Fin d) k → ℂ}
    (hφ : φ ∈ fullRk k n d) : (fun Y : Matrix (Fin n) (Fin d) k => φ (A.val * Y * h.val)) ∈ fullRk k n d := by
  refine ⟨comp_mul_mem_SB A h hφ.1, fun Y hY => hφ.2 _ ?_⟩
  have hA : IsUnit A.val.det := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
  have hh : IsUnit h.val.det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hh, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hA]

end GlobalTheory.FullRankCoinv.LeftScale
