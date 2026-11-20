import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalRingCardinality.Lemmas
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbTiePosDef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Simplify using `only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]`.
-/
theorem hAt_eq_dotProduct {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

/- English proof (translation)
Simplify using `[hAt, Pi.single_apply]`.
-/
theorem hAt_single_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (i j : Fin n) :
    hAt H v (Pi.single i 1) (Pi.single j 1) = v.embedding (H i j) := by
  simp [hAt, Pi.single_apply]

/- English proof (translation)
Establish `herm : (H.map v.embedding).IsHermitian`. Use extensionality with `i j`. Use `h.1 (Pi.single j 1) (Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[hAt_single_single, hAt_single_single]`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply]`.

Rewrite using `[this]`. Establish `hd : DenseRange (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)))` using `DenseRange.piMap (fun _ => Formalism.BasicNotions.denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))`. Establish `psd : (H.map v.embedding).PosSemidef`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg herm fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using hd.induction_on with`.

Consider the case `hp`. Use `isClosed_le continuous_const ?_` and prove the remaining obligations. Conclude with `Continuous.dotProduct (continuous_star) (Continuous.matrix_mulVec continuous_const continuous_id)`. Consider the case `ih y`. Establish `hy : Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)) y = fun i => v.embedding (y i)` using `rfl`.

Rewrite using `[hy, ← hAt_eq_dotProduct]`. Establish `hs` using `h.1 y y`. Establish `him : (hAt H v y y).im = 0`. Use `congrArg Complex.im hs` as an intermediate fact. Simplify using `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Complex.nonneg_iff]`. Use `⟨?_, him.symm⟩` and prove the remaining obligations. Distinguish the cases in `hy0 : y = 0`. Substitute `hy0` using the available equality.

Simplify using `[hAt]`. Conclude with `(h.2 y hy0).le`. Rewrite using `[psd.posDef_iff_det_ne_zero]`. Use `show (v.embedding.mapMatrix H).det ≠ 0`. Rewrite using `[← RingHom.map_det]`.

Introduce `h0`. Rewrite `h0` using `[map_eq_zero]`. Take `⟨y, hy0, hHy⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `hz : hAt H v y y = 0`. Rewrite using `[hAt_eq_dotProduct]`.

Establish `: (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) = 0`. Use function extensionality and compare the values at `i`. Use `RingHom.map_mulVec v.embedding H y i` as an intermediate fact. Rewrite `this` using `[hHy]`. Simplify `this.symm` using `[Function.comp_def]`.

Rewrite using `[this, dotProduct_zero]`. Use `h.2 y hy0` as an intermediate fact. Rewrite `this` using `[hz]`. Simplify using `at this`.
-/
theorem posDef_map_of_posAt [IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K)
    (h : PosAt H v) : (H.map v.embedding).PosDef := by
  have herm : (H.map v.embedding).IsHermitian := by
    ext i j
    have := h.1 (Pi.single j 1) (Pi.single i 1)
    rw [hAt_single_single, hAt_single_single] at this
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [this]
  have hd : DenseRange (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => Formalism.BasicNotions.denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have psd : (H.map v.embedding).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg herm fun z => ?_
    induction z using hd.induction_on with
    | hp =>
      refine isClosed_le continuous_const ?_
      exact Continuous.dotProduct (continuous_star) (Continuous.matrix_mulVec continuous_const continuous_id)
    | ih y =>
      have hy : Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)) y = fun i => v.embedding (y i) := rfl
      rw [hy, ← hAt_eq_dotProduct]
      have hs := h.1 y y
      have him : (hAt H v y y).im = 0 := by
        have := congrArg Complex.im hs
        simp at this
        linarith
      rw [Complex.nonneg_iff]
      refine ⟨?_, him.symm⟩
      by_cases hy0 : y = 0
      · subst hy0
        simp [hAt]
      · exact (h.2 y hy0).le
  rw [psd.posDef_iff_det_ne_zero]
  show (v.embedding.mapMatrix H).det ≠ 0
  rw [← RingHom.map_det]
  intro h0
  rw [map_eq_zero] at h0
  obtain ⟨y, hy0, hHy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : hAt H v y y = 0 := by
    rw [hAt_eq_dotProduct]
    have : (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) = 0 := by
      funext i
      have := RingHom.map_mulVec v.embedding H y i
      rw [hHy] at this
      simpa [Function.comp_def] using this.symm
    rw [this, dotProduct_zero]
  have := h.2 y hy0
  rw [hz] at this
  simp at this

end GlobalTheory.AmbTiePosDef
