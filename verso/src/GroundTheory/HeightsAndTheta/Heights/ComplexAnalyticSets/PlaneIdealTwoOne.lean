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
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Establish `h0 : (0 : ℝ) • φ = fun _ => (0 : ℝ)` using `by funext x; simp`. Use extensionality with `i j`. Simplify using `[ReciprocityTheory.AnForm.hessC, h0]`.

Use `invertibleOfNonzero hc` as an intermediate fact. Establish `h1 : fderiv ℝ (c • φ) = c • fderiv ℝ φ`. Use function extensionality and compare the values at `x`. Conclude with `fderiv_const_smul_of_invertible c`. Establish `h2 : fderiv ℝ (fderiv ℝ (c • φ)) z = c • fderiv ℝ (fderiv ℝ φ) z`.

Rewrite using `[h1]`. Conclude with `fderiv_const_smul_of_invertible (f := fderiv ℝ φ) c`. Use extensionality with `i j`. Simplify using `only [ReciprocityTheory.AnForm.hessC, h2, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
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
Unfold `ReciprocityTheory.AnForm.mdisc`. Simplify using `only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun S _ => by ring`.
-/
theorem mdisc_const_smul {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ReciprocityTheory.AnForm.mdisc (fun k => c • A k) = c ^ D * ReciprocityTheory.AnForm.mdisc A := by
  unfold ReciprocityTheory.AnForm.mdisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

/- English proof (translation)
Unfold `ReciprocityTheory.AnForm.maDens`. Simplify using `only [hessC_const_smul, mdisc_const_smul]`. Rewrite using `[← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDens_const_smul {D : ℕ} (c : ℝ) (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens (fun k => c • φ k) z = c ^ D * ReciprocityTheory.AnForm.maDens φ z := by
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hessC_const_smul, mdisc_const_smul]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Unfold `planeIdeal`. Rewrite using `[Ideal.span_eq_bot]`. Introduce and unpack `q ⟨j, hj, rfl⟩`. It suffices to derive a contradiction. Use `j.isLt` as an intermediate fact.

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
Rewrite using `[planeIdeal_two_one, bot_sup_eq]`. Use `congr 3`. Simplify using `[GroundTheory.Heights₂.Heights.linForm, Fin.sum_univ_two]`.
-/
theorem sliceIdeal_two_one :
    planeIdeal 2 1 ⊔ Ideal.span {linForm (Pi.single (⟨0, by norm_num⟩ : Fin 2) (1 : ℂ)) - 1} =
      (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) := by
  rw [planeIdeal_two_one, bot_sup_eq]
  congr 3
  simp [GroundTheory.Heights₂.Heights.linForm, Fin.sum_univ_two]

/- English proof (translation)
Set `E` to `finSuccEquiv ℂ 1`. Establish `hmap : (Ideal.span {Polynomial.X - Polynomial.C (1 : MvPolynomial (Fin 1) ℂ)} : Ideal (Polynomial (MvPolynomial (Fin 1) ℂ))) = (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)).map (E : MvPolynomial (Fin 2) ℂ →+* _)`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Use `congr 2`. Simplify using `[E, finSuccEquiv_X_zero]`.

Set `e : MvPolynomial (Fin 2) ℂ ⧸ (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) ≃+* MvPolynomial (Fin 1) ℂ` to `(Ideal.quotientEquiv _ _ E.toRingEquiv hmap).trans (Polynomial.quotientSpanXSubCAlgEquiv (1 : MvPolynomial (Fin 1) ℂ)).toRingEquiv`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: IsDomain (MvPolynomial (Fin 2) ℂ ⧸ (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)))` using `e.toMulEquiv.isDomain _`. Conclude with `(Ideal.Quotient.isDomain_iff_prime _).mp inferInstance`. Rewrite using `[ringKrullDim_eq_of_ringEquiv e, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`.

Simplify using the standard rewrite rules.
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
Unfold `GroundTheory.Heights₂.Heights.varInt`. Use `split_ifs with hA`. Unfold `GroundTheory.Heights₂.Heights.chartInt`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `only [GroundTheory.Heights₂.Heights.chartDens, GroundTheory.Heights₂.Heights.sheetSum]`. Rewrite using `[mul_finsum_mem]`. Use `finsum_mem_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `split_ifs with hs`. Establish `hc : (fun k : Fin 1 => (fun _ : Fin 1 => fsPot h) k ∘ hs.choose) = fun k : Fin 1 => (2 : ℝ) • ((fun _ : Fin 1 => fun y => Real.log (h.dualNorm y)) k ∘ hs.choose)`.

Use function extensionality and compare the values at `k w`. Simplify using `[fsPot, Real.log_pow]`. Rewrite using `[hc, maDens_const_smul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
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
Establish `h2` using `(hS 2 1 (by norm_num)).2`. Rewrite `h2` using `[sliceIdeal_two_one, varIntegral_eq _ _ _ isAffVariety_line, varInt_fsPot]`. Unfold `GroundTheory.Heights₂.Heights.LineSliceMass.Statement`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ConeSlicePlane.line (hS : ConeSlicePlane.Statement) :
    GroundTheory.Heights₂.Heights.LineSliceMass.Statement := by
  have h2 := (hS 2 1 (by norm_num)).2
  rw [sliceIdeal_two_one, varIntegral_eq _ _ _ isAffVariety_line, varInt_fsPot] at h2
  unfold GroundTheory.Heights₂.Heights.LineSliceMass.Statement
  linarith

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
