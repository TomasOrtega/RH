import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.CoverURep

variable {p q n : ℕ}

/- English proof (translation)
Use `Units.isEmbedding_val_mk' (f := fun A : Mat p q => A⁻¹) (fun A hA => ?_) (fun u => ?_)` and prove the remaining obligations. Establish `hd : A.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero`. Conclude with `(continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt`. Simplify using the standard rewrite rules.
-/
theorem gl_isEmbedding_val :
    Topology.IsEmbedding (Units.val : (Mat p q)ˣ → Mat p q) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Mat p q => A⁻¹) (fun A hA => ?_) (fun u => ?_)
  · have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    exact (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt
  · simp

/- English proof (translation)
Establish `h1 : Topology.IsInducing (fun A : Mat p q => Matrix.reindex e e A)`. Use `Topology.IsInducing.of_comp (g := fun B : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm B) (continuous_id.matrix_reindex e e) (continuous_id.matrix_reindex e.symm e.symm) ?_` and prove the remaining obligations. Use `Topology.IsInducing.id using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `A`. Simplify using the standard rewrite rules.

Conclude with `((h1.comp gl_isEmbedding_val.isInducing).prodMap Units.isEmbedding_val₀.isInducing).comp T.emb.isInducing`.
-/
theorem inducing_pair (T : GrpData p q) (e : Ix p q ≃ Fin n) :
    Topology.IsInducing (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) := by
  have h1 : Topology.IsInducing (fun A : Mat p q => Matrix.reindex e e A) := by
    refine Topology.IsInducing.of_comp (g := fun B : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm B)
      (continuous_id.matrix_reindex e e) (continuous_id.matrix_reindex e.symm e.symm) ?_
    convert Topology.IsInducing.id using 1
    funext A
    simp
  exact ((h1.comp gl_isEmbedding_val.isInducing).prodMap Units.isEmbedding_val₀.isInducing).comp T.emb.isInducing

/- English proof (translation)
Establish `: (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1`. Rewrite using `[h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]`. Rewrite `this` using `[Matrix.det_reindex_self]`. Conclude with `left_ne_zero_of_mul_eq_one this`.
-/
theorem det_Jm_ne_zero {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) : (Jm p q).det ≠ 0 := by
  have : (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1 := by
    rw [h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
  rw [Matrix.det_reindex_self] at this
  exact left_ne_zero_of_mul_eq_one this

/- English proof (translation)
Establish `h1` using `congrArg Matrix.det ((mem_Upq _).1 (T.cov_mem x))`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← T.sq_sq x]`. Establish `h2` using `congrArg norm h1`. Rewrite `h2` using `[norm_mul, norm_mul, norm_star, norm_pow]`. Establish `h3 : ‖(Jm p q).det‖ ≠ 0` using `norm_ne_zero_iff.2 (det_Jm_ne_zero h)`.

Establish `h4 : ‖((T.sq x : ℂˣ) : ℂ)‖ ^ 4 = 1`. Apply `mul_left_cancel₀ h3` to reduce the goal to its premises. Take the linear combination `h2`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4`.
-/
theorem norm_sq_eq_one {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    ‖((T.sq x : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg Matrix.det ((mem_Upq _).1 (T.cov_mem x))
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← T.sq_sq x] at h1
  have h2 := congrArg norm h1
  rw [norm_mul, norm_mul, norm_star, norm_pow] at h2
  have h3 : ‖(Jm p q).det‖ ≠ 0 := norm_ne_zero_iff.2 (det_Jm_ne_zero h)
  have h4 : ‖((T.sq x : ℂˣ) : ℂ)‖ ^ 4 = 1 := by
    apply mul_left_cancel₀ h3
    linear_combination h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4

/- English proof (translation)
Rewrite using `[continuousOn_iff_isClosed]`. Introduce `t ht`. Take `⟨C, hC, hCe⟩` from `(inducing_pair T e).isClosed_iff.1 (ht.preimage hf)`. Establish `hK : CompactSpace (Metric.closedBall (0 : ℂ) 1)` using `isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)`. Establish `hD : IsClosed {z : Matrix (Fin n) (Fin n) ℂ × Metric.closedBall (0 : ℂ) 1 | (z.1, (z.2 : ℂ)) ∈ C ∧ (z.2 : ℂ) ^ 2 = z.1.det}`.

Use `IsClosed.inter (hC.preimage (by fun_prop)) (isClosed_eq (by fun_prop) ?_)` and prove the remaining obligations. Conclude with `continuous_fst.matrix_det`. Use `⟨_, isClosedMap_fst_of_compactSpace _ hD, ?_⟩` and prove the remaining obligations. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hg, hU⟩`. Use `⟨?_, hU⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `h.cov_surj T hU`. Establish `hx : x ∈ (fun x : T.G => (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C`. Rewrite using `[hCe]`.

Conclude with `hg`. Use `⟨(_, ⟨((T.sq x : ℂˣ) : ℂ), by simp [norm_sq_eq_one h T x]⟩), ⟨hx, ?_⟩, rfl⟩` and prove the remaining obligations. Simplify using `only [Matrix.det_reindex_self]`. Conclude with `T.sq_sq x`. Introduce and unpack `⟨⟨⟨g', w, hw⟩, ⟨h1, h2⟩, rfl⟩, hU⟩`.

Use `⟨?_, hU⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `h.cov_surj T hU`. Simplify using `only at hx h1 h2`. Substitute `hx` using the available equality. Rewrite `h2` using `[Matrix.det_reindex_self]`.

Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Use `T.sq_sq x` as an intermediate fact. Rewrite `this` using `[← h2]`. Simplify using `at this`.

Take `⟨y, ⟨hy1, hy2⟩, -⟩` from `T.bij (T.cov x) (T.cov_mem x) (Units.mk0 w hw0) h2`. Establish `hy : y ∈ (fun x : T.G => (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C`. Simplify using `only [Set.mem_preimage, hy1, hy2]`. Conclude with `h1`. Rewrite `hy` using `[hCe]`.

Simplify using `only [Set.mem_preimage, hy1] at hy`. Conclude with `hy`.
-/
theorem continuousOn_of_cover {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q)
    {Y : Type*} [TopologicalSpace Y] (f : Matrix (Fin n) (Fin n) ℂ → Y)
    (hf : Continuous fun x : T.G => f (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))) :
    ContinuousOn f (UJset ε) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  obtain ⟨C, hC, hCe⟩ := (inducing_pair T e).isClosed_iff.1 (ht.preimage hf)
  have hK : CompactSpace (Metric.closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  have hD : IsClosed {z : Matrix (Fin n) (Fin n) ℂ × Metric.closedBall (0 : ℂ) 1 |
      (z.1, (z.2 : ℂ)) ∈ C ∧ (z.2 : ℂ) ^ 2 = z.1.det} := by
    refine IsClosed.inter (hC.preimage (by fun_prop)) (isClosed_eq (by fun_prop) ?_)
    exact continuous_fst.matrix_det
  refine ⟨_, isClosedMap_fst_of_compactSpace _ hD, ?_⟩
  ext g
  constructor
  · rintro ⟨hg, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨x, rfl⟩ := h.cov_surj T hU
    have hx : x ∈ (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C := by
      rw [hCe]; exact hg
    refine ⟨(_, ⟨((T.sq x : ℂˣ) : ℂ), by simp [norm_sq_eq_one h T x]⟩), ⟨hx, ?_⟩, rfl⟩
    simp only [Matrix.det_reindex_self]
    exact T.sq_sq x
  · rintro ⟨⟨⟨g', w, hw⟩, ⟨h1, h2⟩, rfl⟩, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨x, hx⟩ := h.cov_surj T hU
    simp only at hx h1 h2
    subst hx
    rw [Matrix.det_reindex_self] at h2
    have hw0 : w ≠ 0 := by
      rintro rfl
      have := T.sq_sq x
      rw [← h2] at this
      simp at this
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := T.bij (T.cov x) (T.cov_mem x) (Units.mk0 w hw0) h2
    have hy : y ∈ (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C := by
      simp only [Set.mem_preimage, hy1, hy2]
      exact h1
    rw [hCe] at hy
    simp only [Set.mem_preimage, hy1] at hy
    exact hy

/- English proof (translation)
Introduce `p q n e ε T R σ h hF`. Use `⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `hF 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Introduce `a ha b hb`. Take `⟨x, rfl⟩` from `h.cov_surj T ha`. Take `⟨y, rfl⟩` from `h.cov_surj T hb`. Use `hF (x * y)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_mul, hF x, hF y]`. Rewrite using `[← ContinuousLinearMap.mul_def, this]`. Simplify using `[Matrix.submatrix_mul_equiv]`. Introduce `g hg v`. Take `⟨x, rfl⟩` from `h.cov_surj T hg`.

Rewrite using `[← hF x]`. Conclude with `R.U.isom x v`. Introduce `v`. Use `continuousOn_of_cover h T _ ?_` and prove the remaining obligations. Simplify `R.U.cont v` using `only [← hF _]`.

Introduce `S hS hst`. Use `R.irred S hS fun x v hv => ?_` and prove the remaining obligations. Rewrite using `[hF x]`. Conclude with `hst _ (h.cov_mem T x) v hv`.
-/
theorem urep_irred : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T)
    (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ →
      IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ := by
  intro p q n e ε T R σ h hF
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have := hF 1
    rw [map_one, map_one] at this
    rw [this]
    simp
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := h.cov_surj T ha
    obtain ⟨y, rfl⟩ := h.cov_surj T hb
    have := hF (x * y)
    rw [map_mul, map_mul, hF x, hF y] at this
    rw [← ContinuousLinearMap.mul_def, this]
    simp [Matrix.submatrix_mul_equiv]
  · intro g hg v
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    rw [← hF x]
    exact R.U.isom x v
  · intro v
    refine continuousOn_of_cover h T _ ?_
    simpa only [← hF _] using R.U.cont v
  · intro S hS hst
    refine R.irred S hS fun x v hv => ?_
    rw [hF x]
    exact hst _ (h.cov_mem T x) v hv

end GlobalTheory.RealPar.CoverURep

end
