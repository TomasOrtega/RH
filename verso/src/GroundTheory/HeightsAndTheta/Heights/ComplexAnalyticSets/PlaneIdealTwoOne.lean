import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hessC_const_smul {D : ℕ} (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.hessC (c • φ) z = (c : ℂ) • ReciprocityTheory.AnForm.hessC φ z := by
  by_cases hc : c = 0
  · subst hc
    have h0 : (0 : ℝ) • φ = fun _ => (0 : ℝ) := by funext x; simp
    ext i j
    simp [ReciprocityTheory.AnForm.hessC, h0]
  have := invertibleOfNonzero hc
  have h1 : fderiv ℝ (c • φ) = c • fderiv ℝ φ := by
    funext x
    exact fderiv_const_smul_of_invertible c
  have h2 : fderiv ℝ (fderiv ℝ (c • φ)) z = c • fderiv ℝ (fderiv ℝ φ) z := by
    rw [h1]
    exact fderiv_const_smul_of_invertible (f := fderiv ℝ φ) c
  ext i j
  simp only [ReciprocityTheory.AnForm.hessC, h2, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  push_cast
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mdisc_const_smul {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ReciprocityTheory.AnForm.mdisc (fun k => c • A k) = c ^ D * ReciprocityTheory.AnForm.mdisc A := by
  unfold ReciprocityTheory.AnForm.mdisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDens_const_smul {D : ℕ} (c : ℝ) (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens (fun k => c • φ k) z = c ^ D * ReciprocityTheory.AnForm.maDens φ z := by
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hessC_const_smul, mdisc_const_smul]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. It suffices to derive a contradiction. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem planeIdeal_two_one : planeIdeal 2 1 = ⊥ := by
  unfold planeIdeal
  rw [Ideal.span_eq_bot]
  rintro q ⟨j, hj, rfl⟩
  exfalso
  have := j.isLt
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
theorem sliceIdeal_two_one :
    planeIdeal 2 1 ⊔ Ideal.span {linForm (Pi.single (⟨0, by norm_num⟩ : Fin 2) (1 : ℂ)) - 1} =
      (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) := by
  rw [planeIdeal_two_one, bot_sup_eq]
  congr 3
  simp [GroundTheory.Heights₂.Heights.linForm, Fin.sum_univ_two]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem isAffVariety_line :
    IsAffVariety (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) 1 := by
  let E := finSuccEquiv ℂ 1
  have hmap : (Ideal.span {Polynomial.X - Polynomial.C (1 : MvPolynomial (Fin 1) ℂ)} :
      Ideal (Polynomial (MvPolynomial (Fin 1) ℂ))) =
      (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)).map (E : MvPolynomial (Fin 2) ℂ →+* _) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [E, finSuccEquiv_X_zero]
  let e : MvPolynomial (Fin 2) ℂ ⧸ (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) ≃+*
      MvPolynomial (Fin 1) ℂ :=
    (Ideal.quotientEquiv _ _ E.toRingEquiv hmap).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (1 : MvPolynomial (Fin 1) ℂ)).toRingEquiv
  refine ⟨?_, ?_⟩
  · have : IsDomain (MvPolynomial (Fin 2) ℂ ⧸ (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ))) :=
      e.toMulEquiv.isDomain _
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  · rw [ringKrullDim_eq_of_ringEquiv e, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    simp

/- English proof (translation)
Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem varInt_fsPot {n : ℕ} (h : GroundTheory.Heights₂.Heights.HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.varInt J 1 f (fun _ => fsPot h) =
      2 * GroundTheory.Heights₂.Heights.varInt J 1 f (fun _ y => Real.log (h.dualNorm y)) := by
  unfold GroundTheory.Heights₂.Heights.varInt
  split_ifs with hA
  · unfold GroundTheory.Heights₂.Heights.chartInt
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [GroundTheory.Heights₂.Heights.chartDens, GroundTheory.Heights₂.Heights.sheetSum]
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun x _ => ?_
    split_ifs with hs
    · have hc : (fun k : Fin 1 => (fun _ : Fin 1 => fsPot h) k ∘ hs.choose) =
          fun k : Fin 1 => (2 : ℝ) • ((fun _ : Fin 1 => fun y => Real.log (h.dualNorm y)) k ∘ hs.choose) := by
        funext k w
        simp [fsPot, Real.log_pow]
      rw [hc, maDens_const_smul]
      ring
    · simp
  · simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ConeSlicePlane.line (hS : ConeSlicePlane.Statement) :
    GroundTheory.Heights₂.Heights.LineSliceMass.Statement := by
  have h2 := (hS 2 1 (by norm_num)).2
  rw [sliceIdeal_two_one, varIntegral_eq _ _ _ isAffVariety_line, varInt_fsPot] at h2
  unfold GroundTheory.Heights₂.Heights.LineSliceMass.Statement
  linarith

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
