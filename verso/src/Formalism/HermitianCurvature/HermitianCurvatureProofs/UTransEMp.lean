import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerCoordinateProd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section muSS

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def QN (k r : ℕ) : Measure (U.RC k r 0 × (G.UT r → ℂ)) := (U.muRC k r 0).prod volume

instance (k r : ℕ) : SigmaFinite (U.muRC k r 0) := Dx2.SplitF.sf_RC r 0

instance (k r : ℕ) : SFinite (QN k r) := by unfold QN; infer_instance

def TN (k r : ℕ) (p : (Mt k r × (U.RC k r 0 × (G.UT r → ℂ))) × (Mt k r × (U.RC k r 0 × (G.UT r → ℂ)))) :
    B.SS k r :=
  ((p.1.1, psiR k r p.1.2), (p.2.1, psiR k r p.2.2))

/- English proof (translation)
Unfold `TN`. Conclude with `((measurable_fst.comp measurable_fst).prodMk ((psiR_meas r).comp (measurable_snd.comp measurable_fst))).prodMk ((measurable_fst.comp measurable_snd).prodMk ((psiR_meas r).comp (measurable_snd.comp measurable_snd)))`.
-/
theorem TN_meas : Measurable (TN k r) := by
  unfold TN
  exact ((measurable_fst.comp measurable_fst).prodMk ((psiR_meas r).comp (measurable_snd.comp measurable_fst))).prodMk
    ((measurable_fst.comp measurable_snd).prodMk ((psiR_meas r).comp (measurable_snd.comp measurable_snd)))

/- English proof (translation)
Establish `hW : SigmaFinite S.μW` using `Dx2.MN.sigma_of_haar S.haarW`. Establish `hW' : SigmaFinite S.μW'` using `Dx2.MN.sigma_of_haar S.haarW'`. Establish `hN' : S.μN = (QN k r).map (psiR k r)` using `by rw [hN]; exact muN_rev (k := k) r`. Unfold `B.RealPlaceData.μSS`. Rewrite using `[hN', ← Measure.map_id (μ := S.μW), Measure.map_prod_map _ _ measurable_id (psiR_meas r), ← Measure.map_id (μ := S.μW'), Measure.map_prod_map _ _ measurable_id (psiR_meas r), Measure.map_prod_map _ _ (measurable_id.prodMap (psiR_meas r)) (measurable_id.prodMap (psiR_meas r)), Mea …`.

Both sides reduce to the same expression.
-/
theorem muSS_eq (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) :
    S.μSS = ((S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r))).map (TN k r) := by
  have hW : SigmaFinite S.μW := Dx2.MN.sigma_of_haar S.haarW
  have hW' : SigmaFinite S.μW' := Dx2.MN.sigma_of_haar S.haarW'
  have hN' : S.μN = (QN k r).map (psiR k r) := by rw [hN]; exact muN_rev (k := k) r
  unfold B.RealPlaceData.μSS
  rw [hN', ← Measure.map_id (μ := S.μW), Measure.map_prod_map _ _ measurable_id (psiR_meas r),
    ← Measure.map_id (μ := S.μW'), Measure.map_prod_map _ _ measurable_id (psiR_meas r),
    Measure.map_prod_map _ _ (measurable_id.prodMap (psiR_meas r)) (measurable_id.prodMap (psiR_meas r)),
    Measure.map_id, Measure.map_id]
  rfl

end muSS

section utrans

variable {r : ℕ} {X : Type} [MeasurableSpace X]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[if_neg (ne_of_lt h), dif_pos h, zero_add]`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl, dif_neg (lt_irrefl _), add_zero, hA.2 i]`. Rewrite using `[if_neg (ne_of_gt h), dif_neg (not_lt.2 h.le), add_zero, hA.1 i j h]`.
-/
theorem ut_of_mem {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : G.upper (StabilizerDisintegration.utc A) = A := by
  ext i j
  simp only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg (ne_of_lt h), dif_pos h, zero_add]
  · subst h
    rw [if_pos rfl, dif_neg (lt_irrefl _), add_zero, hA.2 i]
  · rw [if_neg (ne_of_gt h), dif_neg (not_lt.2 h.le), add_zero, hA.1 i j h]

/- English proof (translation)
Establish `hT : Matrix.BlockTriangular A id` using `fun i j hij => hA.1 i j hij`. Establish `hu : IsUnit A.det`. Rewrite using `[Matrix.det_of_upperTriangular hT]`. Simplify using `[hA.2]`. Use `haveI := Matrix.invertibleOfIsUnitDet A hu`.

Establish `hTi : Matrix.BlockTriangular A⁻¹ id` using `Matrix.blockTriangular_inv_of_blockTriangular hT`. Use `⟨fun i j hij => hTi hij, fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : (A * A⁻¹) i i = 1` using `by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_apply_eq]`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `h1` using `[hA.2, one_mul]`. Then use the resulting hypothesis.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hA.1 i k h, zero_mul]`. Rewrite using `[hTi h, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem ut_inv_mem {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : A⁻¹ ∈ C2.UTset r := by
  have hT : Matrix.BlockTriangular A id := fun i j hij => hA.1 i j hij
  have hu : IsUnit A.det := by
    rw [Matrix.det_of_upperTriangular hT]
    simp [hA.2]
  haveI := Matrix.invertibleOfIsUnitDet A hu
  have hTi : Matrix.BlockTriangular A⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hT
  refine ⟨fun i j hij => hTi hij, fun i => ?_⟩
  have h1 : (A * A⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rwa [hA.2, one_mul] at h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA.1 i k h, zero_mul]
    · rw [hTi h, mul_zero]
  · simp

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => hA.1 i j hij)]`. Simplify using `[hA.2]`.
-/
theorem ut_det {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : IsUnit A.det := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hA.1 i j hij)]
  simp [hA.2]

def uTransE (A : X → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ x, A x ∈ C2.UTset r) (hAc : ∀ i j, Measurable fun x => A x i j)
    (hAi : ∀ i j, Measurable fun x => (A x)⁻¹ i j) :
    (X × (G.UT r → ℂ)) ≃ᵐ (X × (G.UT r → ℂ)) where
  toFun p := (p.1, StabilizerDisintegration.utc ((A p.1)⁻¹ * G.upper p.2))
  invFun p := (p.1, StabilizerDisintegration.utc (A p.1 * G.upper p.2))
  left_inv p := by
    ext
    · rfl
    · simp only
      rw [ut_of_mem (C2x2.ut_mul (ut_inv_mem (hA p.1)) (StabilizerDisintegration.UC.upper_mem _)), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (ut_det (hA p.1)), Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  right_inv p := by
    ext
    · rfl
    · simp only
      rw [ut_of_mem (C2x2.ut_mul (hA p.1) (StabilizerDisintegration.UC.upper_mem _)), ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ (ut_det (hA p.1)), Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  measurable_toFun := by
    refine measurable_fst.prodMk ?_
    refine measurable_pi_lambda _ fun q => ?_
    simp only [StabilizerDisintegration.utc, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun c _ => Measurable.mul ?_ ?_
    · exact (hAi _ _).comp measurable_fst
    · exact ((StabilizerDisintegration.UC.cont_upper.matrix_elem _ _).measurable).comp measurable_snd
  measurable_invFun := by
    refine measurable_fst.prodMk ?_
    refine measurable_pi_lambda _ fun q => ?_
    simp only [StabilizerDisintegration.utc, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun c _ => Measurable.mul ?_ ?_
    · exact (hAc _ _).comp measurable_fst
    · exact ((StabilizerDisintegration.UC.cont_upper.matrix_elem _ _).measurable).comp measurable_snd

/- English proof (translation)
Establish `h` using `MeasurePreserving.skew_product (f := id) (g := fun x u => StabilizerDisintegration.utc ((A x)⁻¹ * G.upper u)) (MeasurePreserving.id μ) (measurable_snd.comp (uTransE A hA hAc hAi).measurable) (Filter.Eventually.of_forall fun x => (StabilizerDisintegration.utLeft r _ (ut_inv_mem (h …`. Conclude with `h`.
-/
theorem uTransE_mp (A : X → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ x, A x ∈ C2.UTset r) (hAc : ∀ i j, Measurable fun x => A x i j)
    (hAi : ∀ i j, Measurable fun x => (A x)⁻¹ i j)
    (μ : Measure X) [SFinite μ] :
    MeasurePreserving (uTransE A hA hAc hAi) (μ.prod volume) (μ.prod volume) := by
  have h := MeasurePreserving.skew_product (f := id) (g := fun x u => StabilizerDisintegration.utc ((A x)⁻¹ * G.upper u))
    (MeasurePreserving.id μ) (measurable_snd.comp (uTransE A hA hAc hAi).measurable)
    (Filter.Eventually.of_forall fun x => (StabilizerDisintegration.utLeft r _ (ut_inv_mem (hA x))).map_eq)
  exact h

end utrans

end Formalism.FourierDecayAlt.P.PBM
