import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockMatrixMulBlocks
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicElementBlocks
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBallsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MatrixAdditiveHaarNormalizedStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasureInvertibleIntegralMatricesStatement
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.PsiVolume

section Alg

variable {F : Type} [Field F]

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `BlockMul.blocks_mul r d c c x (pEl 1 B m : GL (Fin (r + c)) F).val`. Establish `a1 : bAA (pEl 1 B m : GL (Fin (r + c)) F).val = 1`. Rewrite using `[QLB.pEl_coe, QLB.bAA_reindex]`. Both sides reduce to the same expression. Establish `a2 : bAD (pEl 1 B m : GL (Fin (r + c)) F).val = B`.

Rewrite using `[QLB.pEl_coe, QLB.bAD_reindex]`. Establish `a3 : bDA (pEl 1 B m : GL (Fin (r + c)) F).val = 0`. Rewrite using `[QLB.pEl_coe, QLB.bDA_reindex]`. Establish `a4 : bDD (pEl 1 B m : GL (Fin (r + c)) F).val = (m : Matrix (Fin c) (Fin c) F)`. Rewrite using `[QLB.pEl_coe, QLB.bDD_reindex]`.

Rewrite `h1`, `h3` using `[a1, a3]`. Rewrite `h2`, `h4` using `[a2, a4]`. Use `⟨?_, ?_, h2, h4⟩` and prove the remaining obligations. Rewrite using `[h1]`. Simplify using the standard rewrite rules.

Rewrite using `[h3]`. Simplify using the standard rewrite rules.
-/
theorem blocks_mul_pEl {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F)
    (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F) :
    bAA (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = bAA x ∧
    bDA (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = bDA x ∧
    bAD (x * (pEl 1 B m : GL (Fin (r + c)) F).val) =
      bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∧
    bDD (x * (pEl 1 B m : GL (Fin (r + c)) F).val) =
      bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) := by
  obtain ⟨h1, h2, h3, h4⟩ := BlockMul.blocks_mul r d c c x (pEl 1 B m : GL (Fin (r + c)) F).val
  have a1 : bAA (pEl 1 B m : GL (Fin (r + c)) F).val = 1 := by
    rw [QLB.pEl_coe, QLB.bAA_reindex]; rfl
  have a2 : bAD (pEl 1 B m : GL (Fin (r + c)) F).val = B := by
    rw [QLB.pEl_coe, QLB.bAD_reindex]
  have a3 : bDA (pEl 1 B m : GL (Fin (r + c)) F).val = 0 := by
    rw [QLB.pEl_coe, QLB.bDA_reindex]
  have a4 : bDD (pEl 1 B m : GL (Fin (r + c)) F).val = (m : Matrix (Fin c) (Fin c) F) := by
    rw [QLB.pEl_coe, QLB.bDD_reindex]
  rw [a1, a3] at h1 h3
  rw [a2, a4] at h2 h4
  refine ⟨?_, ?_, h2, h4⟩
  · rw [h1]; simp
  · rw [h3]; simp

/- English proof (translation)
Establish `hn : ‖chi0 δ a‖ = 1` using `by simp [chi0, ha, hδ]`. Establish `hi : ‖(chi0 δ a)⁻¹‖ = 1` using `by rw [norm_inv, hn, inv_one]`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hi]`. Simplify using the standard rewrite rules.
-/
theorem unramifiedCharExt_inv_mul_conj_inv {δ : Fˣ →* ℂˣ} (hδ : ∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1) {a : F} (ha : a ≠ 0) :
    (chi0 δ a)⁻¹ * conj ((chi0 δ a)⁻¹) = 1 := by
  have hn : ‖chi0 δ a‖ = 1 := by simp [chi0, ha, hδ]
  have hi : ‖(chi0 δ a)⁻¹‖ = 1 := by rw [norm_inv, hn, inv_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hi]; simp

/- English proof (translation)
Take `⟨k, -, rfl⟩` from `h`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 k.isUnit).ne_zero`.
-/
theorem det_ne_of_mem_Jset {a : ℕ} {J' : Subgroup (GL (Fin a) F)} {Y : Matrix (Fin a) (Fin a) F}
    (h : Y ∈ Jset J') : Y.det ≠ 0 := by
  obtain ⟨k, -, rfl⟩ := h
  exact ((Matrix.isUnit_iff_isUnit_det _).1 k.isUnit).ne_zero

abbrev psiSet (O : Subring F) (ϖ : F) {r d c : ℕ} (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F) :
    Set (Matrix (Fin (r + d)) (Fin (r + c)) F) :=
  {x | bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c ∧
    bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O r c ∧
    bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O d c}

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `blocks_mul_pEl x B m`. Distinguish the cases in `hx : x ∈ (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F))`. Rewrite using `[Set.indicator_of_mem hx]`. Take `⟨a, b, e, f, g, h⟩` from `hx`. Establish `p1 : phiQ O ϖ δ r d c x = (chi0 δ (bAA x).det)⁻¹`.

Unfold `phiQ`. Rewrite using `[if_pos ⟨a, b, e, f⟩]`. Establish `p2 : phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = (chi0 δ (bAA x).det)⁻¹`. Unfold `phiQ`. Rewrite using `[h1, h2, h3, h4, if_pos ⟨a, b, g, h⟩]`.

Rewrite using `[p1, p2]`. Conclude with `unramifiedCharExt_inv_mul_conj_inv hδ (det_ne_of_mem_Jset a)`. Rewrite using `[Set.indicator_of_notMem hx]`. Distinguish the cases in `hc : bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c`. Establish `p2 : phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = 0`.

Unfold `phiQ`. Rewrite using `[h1, h2, h3, h4, if_neg]`. Introduce and unpack `⟨-, -, g, h⟩`. Conclude with `hx ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, g, h⟩`. Rewrite using `[p2, zero_mul]`.

Establish `p1 : phiQ O ϖ δ r d c x = 0`. Unfold `phiQ`. Rewrite using `[if_neg hc]`. Rewrite using `[p1]`. Simplify using the standard rewrite rules.
-/
theorem phi_mul_conj (O : Subring F) (ϖ : F) {δ : Fˣ →* ℂˣ} (hδ : ∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1)
    {r d c : ℕ} (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F)
    (x : Matrix (Fin (r + d)) (Fin (r + c)) F) :
    phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) * conj (phiQ O ϖ δ r d c x) =
      (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F)).indicator (fun _ => (1 : ℂ)) x := by
  obtain ⟨h1, h2, h3, h4⟩ := blocks_mul_pEl x B m
  by_cases hx : x ∈ (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F))
  · rw [Set.indicator_of_mem hx]
    obtain ⟨a, b, e, f, g, h⟩ := hx
    have p1 : phiQ O ϖ δ r d c x = (chi0 δ (bAA x).det)⁻¹ := by
      unfold phiQ; rw [if_pos ⟨a, b, e, f⟩]
    have p2 : phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) =
        (chi0 δ (bAA x).det)⁻¹ := by
      unfold phiQ
      rw [h1, h2, h3, h4, if_pos ⟨a, b, g, h⟩]
    rw [p1, p2]
    exact unramifiedCharExt_inv_mul_conj_inv hδ (det_ne_of_mem_Jset a)
  · rw [Set.indicator_of_notMem hx]
    by_cases hc : bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧
        bDD x ∈ intMat O d c
    · have p2 : phiQ O ϖ δ r d c (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = 0 := by
        unfold phiQ
        rw [h1, h2, h3, h4, if_neg]
        rintro ⟨-, -, g, h⟩
        exact hx ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, g, h⟩
      rw [p2, zero_mul]
    · have p1 : phiQ O ϖ δ r d c x = 0 := by
        unfold phiQ; rw [if_neg hc]
      rw [p1]; simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, QLB.pEl_det]`.
-/
theorem det_pEl_one {r c : ℕ} (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F) :
    Matrix.GeneralLinearGroup.det (pEl 1 B m : GL (Fin (r + c)) F) =
      Matrix.GeneralLinearGroup.det m := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, QLB.pEl_det]

end Alg

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

/- English proof (translation)
Use `haveI := (GlobalTheory.T.matrix_additive_haar_normalized hLF t a).1`. Take `⟨-, -, -, hc, -, -⟩` from `GlobalTheory.T.localField_topology_norm_balls hLF`. Take `⟨-, -, -, hlt, -⟩` from `NormalisedValue.main hLF`. Establish `he : (IIset O ϖ : Set (Matrix (Fin t) (Fin a) F)) = ⋂ i, ⋂ j, {y : Matrix (Fin t) (Fin a) F | nrm (y i j) < 1}`. Use extensionality with `y`.

Simplify using `only [IIset, Set.mem_setOf_eq, Set.mem_iInter, hlt]`. Rewrite using `[he]`. Use `IsOpen.measurableSet (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)` and prove the remaining obligations. Conclude with `isOpen_lt (hc.comp (continuous_id.matrix_elem i j)) continuous_const`.
-/
theorem measurableSet_IIset (hLF : LF O ϖ nrm q) (t a : ℕ) :
    MeasurableSet (IIset O ϖ : Set (Matrix (Fin t) (Fin a) F)) := by
  haveI := (GlobalTheory.T.matrix_additive_haar_normalized hLF t a).1
  obtain ⟨-, -, -, hc, -, -⟩ := GlobalTheory.T.localField_topology_norm_balls hLF
  obtain ⟨-, -, -, hlt, -⟩ := NormalisedValue.main hLF
  have he : (IIset O ϖ : Set (Matrix (Fin t) (Fin a) F)) =
      ⋂ i, ⋂ j, {y : Matrix (Fin t) (Fin a) F | nrm (y i j) < 1} := by
    ext y
    simp only [IIset, Set.mem_setOf_eq, Set.mem_iInter, hlt]
  rw [he]
  refine IsOpen.measurableSet (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact isOpen_lt (hc.comp (continuous_id.matrix_elem i j)) continuous_const

/- English proof (translation)
Take `⟨dx, h1, h2⟩` from `(GlobalTheory.T.matrix_additive_haar_normalized hLF r r).2.2.2.1`. Conclude with `(GlobalTheory.T.measure_invertible_integral_matrices hLF r dx h1 h2).1`.
-/
theorem measurableSet_Jset (hLF : LF O ϖ nrm q) (r : ℕ) :
    MeasurableSet (Jset (GLint O r)) := by
  obtain ⟨dx, h1, h2⟩ := (GlobalTheory.T.matrix_additive_haar_normalized hLF r r).2.2.2.1
  exact (GlobalTheory.T.measure_invertible_integral_matrices hLF r dx h1 h2).1

/- English proof (translation)
Use `haveI hB : ∀ n k : ℕ, BorelSpace (Matrix (Fin n) (Fin k) F) := fun n k => (GlobalTheory.T.matrix_additive_haar_normalized hLF n k).1`. Establish `hI : ∀ n k : ℕ, MeasurableSet (intMat O n k)` using `fun n k => (GlobalTheory.T.matrix_additive_haar_normalized hLF n k).2.1.measurableSet`. Establish `c1 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bAA x)` using `continuous_id.matrix_submatrix _ _`. Establish `c2 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bAD x)` using `continuous_id.matrix_submatrix _ _`. Establish `c3 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bDA x)` using `continuous_id.matrix_submatrix _ _`.

Establish `c4 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bDD x)` using `continuous_id.matrix_submatrix _ _`. Establish `c5 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F))` using `(c1.matrix_mul continuous_const).add (c2.matrix_mul continuous_const)`. Establish `c6 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F))` using `(c3.matrix_mul continuous_const).add (c4.matrix_mul continuous_const)`. Conclude with `(c1.measurable (measurableSet_Jset hLF r)).inter ((c3.measurable (measurableSet_IIset hLF d r)).inter ((c2.measurable (hI r c)).inter ((c4.measurable (hI d c)).inter ((c5.measurable (hI r c)).inter (c6.measurable (hI d c))))))`.
-/
theorem measurableSet_psiSet (hLF : LF O ϖ nrm q) {r d c : ℕ} (B : Matrix (Fin r) (Fin c) F)
    (m : GL (Fin c) F) :
    MeasurableSet (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F)) := by
  haveI hB : ∀ n k : ℕ, BorelSpace (Matrix (Fin n) (Fin k) F) :=
    fun n k => (GlobalTheory.T.matrix_additive_haar_normalized hLF n k).1
  have hI : ∀ n k : ℕ, MeasurableSet (intMat O n k) :=
    fun n k => (GlobalTheory.T.matrix_additive_haar_normalized hLF n k).2.1.measurableSet
  have c1 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bAA x) :=
    continuous_id.matrix_submatrix _ _
  have c2 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bAD x) :=
    continuous_id.matrix_submatrix _ _
  have c3 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bDA x) :=
    continuous_id.matrix_submatrix _ _
  have c4 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F => bDD x) :=
    continuous_id.matrix_submatrix _ _
  have c5 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F =>
      bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F)) :=
    (c1.matrix_mul continuous_const).add (c2.matrix_mul continuous_const)
  have c6 : Continuous (fun x : Matrix (Fin (r + d)) (Fin (r + c)) F =>
      bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F)) :=
    (c3.matrix_mul continuous_const).add (c4.matrix_mul continuous_const)
  exact (c1.measurable (measurableSet_Jset hLF r)).inter
    ((c3.measurable (measurableSet_IIset hLF d r)).inter
    ((c2.measurable (hI r c)).inter ((c4.measurable (hI d c)).inter
    ((c5.measurable (hI r c)).inter (c6.measurable (hI d c))))))

end Top

/- English proof (translation)
Introduce `F _ _ _ _ _ _ O ϖ nrm q hLF δ η hδ hη r d c dx hdx hdx1 B m`. Establish `hS : MeasurableSet (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F))` using `measurableSet_psiSet hLF B m`. Use `⟨hS, ?_⟩` and prove the remaining obligations. Establish `hint : weilIP dx (omegaS (η * δ) nrm (pEl 1 B m) (phiQ O ϖ δ r d c)) (phiQ O ϖ δ r d c) = ∫ x, ((((η * δ) (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) * ((nrm (m : Matrix (Fin c) (Fin c) F).det ^ (((r + d : ℕ) : ℝ) / 2) : ℝ) : ℂ)) * (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fi …`. Unfold `weilIP`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hp` using `phi_mul_conj O ϖ hδ.unitary B m x`. Simplify using `only [omegaS, det_pEl_one, Fintype.card_fin, Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[mul_assoc _ (phiQ O ϖ δ r d c _), hp]`. Rewrite using `[hint, integral_const_mul, integral_indicator_const _ hS]`.

Simplify using `[Measure.real]`.
-/
theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (δ η : Fˣ →* ℂˣ), Del nrm δ → Nu nrm η → ∀ r d c : ℕ, ∀ (dx : Measure (Matrix (Fin (r + d)) (Fin (r + c)) F)), dx.IsAddLeftInvariant → dx (intMat O (r + d) (r + c)) = 1 → ∀ (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F), MeasurableSet {x : Matrix (Fin (r + d)) (Fin (r + c)) F | bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c ∧ bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O r c ∧ bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O d c} ∧ weilIP dx (omegaS (η * δ) nrm (pEl 1 B m) (phiQ O ϖ δ r d c)) (phiQ O ϖ δ r d c) = (((η * δ) (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) * ((nrm (m : Matrix (Fin c) (Fin c) F).det ^ (((r + d : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (((dx {x : Matrix (Fin (r + d)) (Fin (r + c)) F | bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c ∧ bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O r c ∧ bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) ∈ intMat O d c}).toReal : ℝ) : ℂ) := by
  intro F _ _ _ _ _ _ O ϖ nrm q hLF δ η hδ hη r d c dx hdx hdx1 B m
  have hS : MeasurableSet (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F)) :=
    measurableSet_psiSet hLF B m
  refine ⟨hS, ?_⟩
  have hint : weilIP dx (omegaS (η * δ) nrm (pEl 1 B m) (phiQ O ϖ δ r d c)) (phiQ O ϖ δ r d c) =
      ∫ x, ((((η * δ) (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) *
        ((nrm (m : Matrix (Fin c) (Fin c) F).det ^ (((r + d : ℕ) : ℝ) / 2) : ℝ) : ℂ)) *
        (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F)).indicator (fun _ => (1 : ℂ)) x ∂dx := by
    unfold weilIP
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hp := phi_mul_conj O ϖ hδ.unitary B m x
    simp only [omegaS, det_pEl_one, Fintype.card_fin, Matrix.GeneralLinearGroup.val_det_apply]
    rw [mul_assoc _ (phiQ O ϖ δ r d c _), hp]
  rw [hint, integral_const_mul, integral_indicator_const _ hS]
  simp [Measure.real]

end GlobalTheory.CompanionTheory.QL.PsiVolume
