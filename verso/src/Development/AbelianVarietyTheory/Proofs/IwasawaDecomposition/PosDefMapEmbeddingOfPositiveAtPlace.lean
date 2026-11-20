import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalRingCardinality.Lemmas
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbTiePosDef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hAt_eq_dotProduct {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hAt_single_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (i j : Fin n) :
    hAt H v (Pi.single i 1) (Pi.single j 1) = v.embedding (H i j) := by
  simp [hAt, Pi.single_apply]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Proceed by induction.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
