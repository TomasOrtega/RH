import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChartStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarUpqHasOmegaDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaLebesgueMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousGrpHom

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.OmegaFrobenius

open Formalism.BasicNotions (lieU UpqT entries IsOmegaLeb ballU OmegaDensity)

def realify (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) where
  toFun X := WithLp.toLp 2 (realifyFun X)
  invFun := unrealify
  map_add' X Y := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun]
  left_inv X := by
    ext i j; simp [realifyFun, unrealify]
  right_inv x := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun, unrealify]

/- English proof (translation)
Use `show unrealify (WithLp.toLp 2 (realifyFun X)) = X`. Use extensionality with `i j`. Simplify using `[realifyFun, unrealify]`.
-/
theorem unrealify_realify {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : unrealify (realify n X) = X := by
  show unrealify (WithLp.toLp 2 (realifyFun X)) = X
  ext i j
  simp [realifyFun, unrealify]

/- English proof (translation)
Use `show ⟪WithLp.toLp 2 (realifyFun X), WithLp.toLp 2 (realifyFun Y)⟫_ℝ = _`. Simplify using `only [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_bool, realifyFun, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, RCLike.inner_apply, conj_trivial, if_true, Bool.false_eq_true, if_false, Complex.mul_re, Complex.star_def, C …`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_realify {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪realify n X, realify n Y⟫_ℝ = (Xᴴ * Y).trace.re := by
  show ⟪WithLp.toLp 2 (realifyFun X), WithLp.toLp 2 (realifyFun Y)⟫_ℝ = _
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_bool, realifyFun, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, RCLike.inner_apply, conj_trivial, if_true,
    Bool.false_eq_true, if_false, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `key : ∀ a ∈ UH H, (H * aᴴ * H) * a = 1`. Introduce `a ha`. Establish `ha' : aᴴ * H * a = H` using `ha`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Use `show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * H * 1 = H`. Simplify using the standard rewrite rules. Introduce `a ha b hb`. Establish `ha' : aᴴ * H * a = H` using `ha`.

Establish `hb' : bᴴ * H * b = H` using `hb`. Use `show (a * b)ᴴ * H * (a * b) = H`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `a ha`.

Establish `h1` using `key a ha`. Establish `hinv : a⁻¹ = H * aᴴ * H` using `Matrix.inv_eq_left_inv h1`. Establish `hai : a * a⁻¹ = 1` using `Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse h1)`. Use `⟨?_, hai⟩` and prove the remaining obligations. Establish `ha' : aᴴ * H * a = H` using `ha`.

Use `show (a⁻¹)ᴴ * H * a⁻¹ = H`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) : PI.IsMatGroup (UH H) := by
  have key : ∀ a ∈ UH H, (H * aᴴ * H) * a = 1 := by
    intro a ha
    have ha' : aᴴ * H * a = H := ha
    calc (H * aᴴ * H) * a = H * (aᴴ * H * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', hH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * H * 1 = H
    simp
  · intro a ha b hb
    have ha' : aᴴ * H * a = H := ha
    have hb' : bᴴ * H * b = H := hb
    show (a * b)ᴴ * H * (a * b) = H
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
      _ = H := by rw [ha', hb']
  · intro a ha
    have h1 := key a ha
    have hinv : a⁻¹ = H * aᴴ * H := Matrix.inv_eq_left_inv h1
    have hai : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse h1)
    refine ⟨?_, hai⟩
    have ha' : aᴴ * H * a = H := ha
    show (a⁻¹)ᴴ * H * a⁻¹ = H
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha']
      _ = (a * a⁻¹)ᴴ * H * (a * a⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hai]; simp

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hX`. Establish `hexp : ∀ t : ℝ, NormedSpace.exp (t • (H * (-X)ᴴ * H)) = NormedSpace.exp (t • X)`. Introduce `t`. Establish `h` using `GlobalTheory.UpqExpChart.exp_twist hH (hX t)`.

Establish `e1 : H * (-((t : ℂ) • X))ᴴ * H = t • (H * (-X)ᴴ * H)`. Establish `hs : star (t : ℂ) = (t : ℂ)` using `Complex.conj_ofReal t`. Rewrite using `[Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, hs, Matrix.conjTranspose_neg, Complex.coe_smul, Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg]`. Rewrite `h` using `[e1, Complex.coe_smul]`. Conclude with `h`.

Establish `d1` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) (H * (-X)ᴴ * H) (0 : ℝ)`. Establish `d2` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)`. Establish `d1' : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X)) (NormedSpace.exp ((0 : ℝ) • (H * (-X)ᴴ * H)) * (H * (-X)ᴴ * H)) 0` using `d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hexp t).symm)`. Establish `hYX` using `d1'.unique d2`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul] at hYX`.

Establish `hHH : ∀ W : Matrix (Fin N) (Fin N) ℂ, H * (H * W) = W` using `fun W => by`. Rewrite using `[← Matrix.mul_assoc, hH, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `hX t`. Apply `GlobalTheory.UpqExpChart.exp_unitary hH` to reduce the goal to its premises.

Establish `hs : star (t : ℂ) = (t : ℂ)` using `Complex.conj_ofReal t`. Rewrite using `[Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]`.
-/
theorem mem_lieOf_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) (X : Matrix (Fin N) (Fin N) ℂ) :
    X ∈ lieOf (UH H) ↔ Xᴴ * H + H * X = 0 := by
  constructor
  · intro hX
    have hexp : ∀ t : ℝ, NormedSpace.exp (t • (H * (-X)ᴴ * H)) = NormedSpace.exp (t • X) := by
      intro t
      have h := GlobalTheory.UpqExpChart.exp_twist hH (hX t)
      have e1 : H * (-((t : ℂ) • X))ᴴ * H = t • (H * (-X)ᴴ * H) := by
        have hs : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
        rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, hs, Matrix.conjTranspose_neg, Complex.coe_smul,
          Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
      rw [e1, Complex.coe_smul] at h
      exact h
    have d1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (H * (-X)ᴴ * H) (0 : ℝ)
    have d2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    have d1' : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
        (NormedSpace.exp ((0 : ℝ) • (H * (-X)ᴴ * H)) * (H * (-X)ᴴ * H)) 0 :=
      d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hexp t).symm)
    have hYX := d1'.unique d2
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hYX
    have hHH : ∀ W : Matrix (Fin N) (Fin N) ℂ, H * (H * W) = W := fun W => by
      rw [← Matrix.mul_assoc, hH, Matrix.one_mul]
    calc Xᴴ * H + H * X = Xᴴ * H + H * (H * (-X)ᴴ * H) := by rw [hYX]
      _ = 0 := by rw [Matrix.mul_assoc H, hHH, Matrix.conjTranspose_neg, Matrix.neg_mul, add_neg_cancel]
  · intro hX t
    apply GlobalTheory.UpqExpChart.exp_unitary hH
    have hs : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

/- English proof (translation)
Apply the tactic sequence `let σ : (ι × ι) ⊕ (ι × ι) ≃ Fin n × Fin n × Bool := { toFun := Sum.elim (fun p => (e p.1, e p.2, false)) (fun p => (e p.1, e p.2, true)) invFun := fun q => if q.2.2 then Sum.inr (e.symm q.1, e.symm q.2.1) else Sum.inl (e.symm q.1, e.symm q.2.1) left_inv := by rintro (p | p) <;> s …`. Establish `h1` using `PiLp.volume_preserving_ofLp (ι := Fin n × Fin n × Bool)`. Establish `h2` using `volume_measurePreserving_piCongrLeft (fun _ : (ι × ι) ⊕ (ι × ι) => ℝ) σ.symm`. Establish `h3` using `measurePreserving_sumPiEquivProdPi (X := fun _ : (ι × ι) ⊕ (ι × ι) => ℝ) (fun _ => volume)`. Establish `h4` using `MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (ι × ι) (fun _ => volume) (fun _ => volume))`.

Establish `h5` using `measurePreserving_pi (fun _ : ι × ι => (volume : Measure ℝ).prod volume) (fun _ => (volume : Measure ℂ)) (fun _ => MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod)`. Establish `total` using `h5.comp (h4.comp (h3.comp (h2.comp h1)))`. Establish `hσ1 : ∀ p : ι × ι, σ (Sum.inl p) = (e p.1, e p.2, false)` using `fun p => rfl`. Establish `hσ2 : ∀ p : ι × ι, σ (Sum.inr p) = (e p.1, e p.2, true)` using `fun p => rfl`. Use `total using 1` and compare the differences between its conclusion and the goal.

Use `case e'_7 => exact volume_pi`. Use `clear h1 h2 h3 h4 h5 total`. Use `clear_value σ`. Use function extensionality and compare the values at `x p`. Apply the tactic sequence `apply Complex.ext <;>`.

Simplify using `[hσ1, hσ2, unrealify, MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply, eq_rec_constant, Equiv.arrowProdEquivProdArrow, Complex.measurableEquivRealProd_symm_apply]`.
-/
theorem measurePreserving_unrealify {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n) :
    MeasurePreserving (fun (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) (p : ι × ι) =>
      unrealify x (e p.1) (e p.2)) := by
  let σ : (ι × ι) ⊕ (ι × ι) ≃ Fin n × Fin n × Bool :=
    { toFun := Sum.elim (fun p => (e p.1, e p.2, false)) (fun p => (e p.1, e p.2, true))
      invFun := fun q => if q.2.2 then Sum.inr (e.symm q.1, e.symm q.2.1) else Sum.inl (e.symm q.1, e.symm q.2.1)
      left_inv := by rintro (p | p) <;> simp
      right_inv := by rintro ⟨i, j, b⟩; cases b <;> simp }
  have h1 := PiLp.volume_preserving_ofLp (ι := Fin n × Fin n × Bool)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : (ι × ι) ⊕ (ι × ι) => ℝ) σ.symm
  have h3 := measurePreserving_sumPiEquivProdPi (X := fun _ : (ι × ι) ⊕ (ι × ι) => ℝ) (fun _ => volume)
  have h4 := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (ι × ι) (fun _ => volume) (fun _ => volume))
  have h5 := measurePreserving_pi (fun _ : ι × ι => (volume : Measure ℝ).prod volume) (fun _ => (volume : Measure ℂ))
    (fun _ => MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod)
  have total := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  have hσ1 : ∀ p : ι × ι, σ (Sum.inl p) = (e p.1, e p.2, false) := fun p => rfl
  have hσ2 : ∀ p : ι × ι, σ (Sum.inr p) = (e p.1, e p.2, true) := fun p => rfl
  convert total using 1
  case e'_7 => exact volume_pi
  clear h1 h2 h3 h4 h5 total
  clear_value σ
  funext x p
  apply Complex.ext <;>
    simp [hσ1, hσ2, unrealify, MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply, eq_rec_constant, Equiv.arrowProdEquivProdArrow,
      Complex.measurableEquivRealProd_symm_apply]

variable {n P Q : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Take `⟨a, rfl⟩` from `e.surjective i`. Take `⟨b, rfl⟩` from `e.surjective j`. Rewrite using `[Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`.

Simplify using `[Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.fromBlocks, Matrix.one_apply, h1, h2]`. Apply the tactic sequence `all_goals split_ifs <;> simp`.
-/
theorem jm_eq {ε : Fin n → Bool} {e : Fin P ⊕ Fin Q ≃ Fin n} (h1 : ∀ i, ε (e (Sum.inl i)) = true)
    (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.REAL.Jm ε = (Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.fromBlocks, Matrix.one_apply, h1, h2]
  all_goals split_ifs <;> simp

def coord (e : Fin P ⊕ Fin Q ≃ Fin n) :
    Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) :=
  (Matrix.reindexLinearEquiv ℝ ℂ e e).trans (realify n)

/- English proof (translation)
Use `show unrealify (realify n (X.submatrix e.symm e.symm)) = _`. Rewrite using `[unrealify_realify]`.
-/
theorem unrealify_coord (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    unrealify (coord e X) = X.submatrix e.symm e.symm := by
  show unrealify (realify n (X.submatrix e.symm e.symm)) = _
  rw [unrealify_realify]

/- English proof (translation)
Establish `h : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, coord e Z = realify n (Z.submatrix e.symm e.symm)` using `fun Z => rfl`. Rewrite using `[h, h, inner_realify, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`. Simplify using `only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]`. Rewrite using `[Equiv.sum_comp e.symm (fun j => (Xᴴ * Y) j j)]`.
-/
theorem inner_coord (e : Fin P ⊕ Fin Q ≃ Fin n) (X Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ⟪coord e X, coord e Y⟫_ℝ = (Xᴴ * Y).trace.re := by
  have h : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, coord e Z = realify n (Z.submatrix e.symm e.symm) :=
    fun Z => rfl
  rw [h, h, inner_realify, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e.symm (fun j => (Xᴴ * Y) j j)]

abbrev form (e : Fin P ⊕ Fin Q ≃ Fin n) : Matrix (Fin n) (Fin n) ℂ := (Formalism.UG.Jpq P Q).submatrix e.symm e.symm

/- English proof (translation)
Use `show (Formalism.UG.Jpq P Q).submatrix e.symm e.symm * (Formalism.UG.Jpq P Q).submatrix e.symm e.symm = 1`. Rewrite using `[Matrix.submatrix_mul_equiv, GlobalTheory.UpqExpChart.jpq_sq, Matrix.submatrix_one_equiv]`.
-/
theorem form_sq (e : Fin P ⊕ Fin Q ≃ Fin n) : form e * form e = 1 := by
  show (Formalism.UG.Jpq P Q).submatrix e.symm e.symm * (Formalism.UG.Jpq P Q).submatrix e.symm e.symm = 1
  rw [Matrix.submatrix_mul_equiv, GlobalTheory.UpqExpChart.jpq_sq, Matrix.submatrix_one_equiv]

/- English proof (translation)
Rewrite using `[mem_lieOf_UH _ (form_sq e)]`. Use `show _ ↔ Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0`. Use `show (X.submatrix e.symm e.symm)ᴴ * (Formalism.UG.Jpq P Q).submatrix e.symm e.symm + (Formalism.UG.Jpq P Q).submatrix e.symm e.symm * X.submatrix e.symm e.symm = 0 ↔ _`. Establish `hadd : ∀ A B : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, (A + B).submatrix e.symm e.symm = A.submatrix e.symm e.symm + B.submatrix e.symm e.symm` using `fun A B => rfl`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hadd]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`. Use `congrFun (congrFun h (e i)) (e j)` as an intermediate fact. Simplify using `using this`.

Introduce `h`. Simplify using `[h]`.
-/
theorem submatrix_mem_lieOf (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X.submatrix e.symm e.symm ∈ lieOf (UH (form e)) ↔ X ∈ lieU P Q := by
  rw [mem_lieOf_UH _ (form_sq e)]
  show _ ↔ Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0
  show (X.submatrix e.symm e.symm)ᴴ * (Formalism.UG.Jpq P Q).submatrix e.symm e.symm +
    (Formalism.UG.Jpq P Q).submatrix e.symm e.symm * X.submatrix e.symm e.symm = 0 ↔ _
  have hadd : ∀ A B : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ,
      (A + B).submatrix e.symm e.symm = A.submatrix e.symm e.symm + B.submatrix e.symm e.symm := fun A B => rfl
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hadd]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (e i)) (e j)
    simpa using this
  · intro h
    simp [h]

/- English proof (translation)
Establish `hset : ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf (UH (form e)) : Set (EuclideanSpace ℝ (Fin n × Fin n × Bool))) = ((lieU P Q).map (coord e).toLinearMap : Set _)`. Use extensionality with `v`. Rewrite using `[Submodule.map_coe]`. Simplify using `only [Set.mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨Y, hY, rfl⟩`. Establish `hXY : (Y.submatrix e e).submatrix e.symm e.symm = Y` using `by ext i j; simp`. Use `⟨Y.submatrix e e, (submatrix_mem_lieOf e _).1 (by rw [hXY]; exact hY), ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun Z => WithLp.toLp 2 (realifyFun Z)) hXY`. Introduce and unpack `⟨X, hX, rfl⟩`.

Conclude with `⟨X.submatrix e.symm e.symm, (submatrix_mem_lieOf e X).2 hX, rfl⟩`. Unfold `lieE`. Rewrite using `[hset, Submodule.span_eq]`.
-/
theorem map_lieU (e : Fin P ⊕ Fin Q ≃ Fin n) :
    (lieU P Q).map (coord e).toLinearMap = lieE (UH (form e)) := by
  have hset : ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf (UH (form e)) :
      Set (EuclideanSpace ℝ (Fin n × Fin n × Bool))) = ((lieU P Q).map (coord e).toLinearMap : Set _) := by
    ext v
    rw [Submodule.map_coe]
    simp only [Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      have hXY : (Y.submatrix e e).submatrix e.symm e.symm = Y := by ext i j; simp
      refine ⟨Y.submatrix e e, (submatrix_mem_lieOf e _).1 (by rw [hXY]; exact hY), ?_⟩
      exact congrArg (fun Z => WithLp.toLp 2 (realifyFun Z)) hXY
    · rintro ⟨X, hX, rfl⟩
      exact ⟨X.submatrix e.symm e.symm, (submatrix_mem_lieOf e X).2 hX, rfl⟩
  unfold lieE
  rw [hset, Submodule.span_eq]

def lieCoord (e : Fin P ⊕ Fin Q ≃ Fin n) : lieU P Q ≃L[ℝ] lieE (UH (form e)) :=
  ((coord e).ofSubmodules _ _ (map_lieU e)).toContinuousLinearEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_lieCoord (e : Fin P ⊕ Fin Q ≃ Fin n) (X : lieU P Q) :
    (lieCoord e X : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = coord e X := rfl

/- English proof (translation)
Establish `hJ` using `GlobalTheory.UpqExpChart.jpq_sq P Q`. Establish `hA : A.1ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * A.1 = 0` using `A.2`. Establish `hB : B.1ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * B.1 = 0` using `B.2`. Establish `key : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, Zᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * Z = 0 → Zᴴ = -(Formalism.UG.Jpq P Q * Z * Formalism.UG.Jpq P Q)`. Introduce `Z hZ`.

Establish `h1 : Zᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * Z)` using `eq_neg_of_add_eq_zero_left hZ`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : (A.1ᴴ * B.1).trace = -(Formalism.UG.Jpq P Q * A.1 * (Formalism.UG.Jpq P Q * B.1)).trace`. Rewrite using `[key A.1 hA, Matrix.neg_mul, Matrix.trace_neg]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `h2 : star (A.1ᴴ * B.1).trace = -(Formalism.UG.Jpq P Q * B.1 * (Formalism.UG.Jpq P Q * A.1)).trace`. Rewrite using `[← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, key B.1 hB, Matrix.neg_mul, Matrix.trace_neg]`. Simplify using `only [Matrix.mul_assoc]`. Establish `h3 : star (A.1ᴴ * B.1).trace = (A.1ᴴ * B.1).trace`. Rewrite using `[h2, h1, Matrix.trace_mul_comm]`.

Conclude with `Complex.conj_eq_iff_im.mp h3`.
-/
theorem trace_im (A B : lieU P Q) : (A.1ᴴ * B.1).trace.im = 0 := by
  have hJ := GlobalTheory.UpqExpChart.jpq_sq P Q
  have hA : A.1ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * A.1 = 0 := A.2
  have hB : B.1ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * B.1 = 0 := B.2
  have key : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ,
      Zᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * Z = 0 → Zᴴ = -(Formalism.UG.Jpq P Q * Z * Formalism.UG.Jpq P Q) := by
    intro Z hZ
    have h1 : Zᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * Z) := eq_neg_of_add_eq_zero_left hZ
    calc Zᴴ = Zᴴ * Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = -(Formalism.UG.Jpq P Q * Z * Formalism.UG.Jpq P Q) := by rw [h1, Matrix.neg_mul]
  have h1 : (A.1ᴴ * B.1).trace = -(Formalism.UG.Jpq P Q * A.1 * (Formalism.UG.Jpq P Q * B.1)).trace := by
    rw [key A.1 hA, Matrix.neg_mul, Matrix.trace_neg]
    simp only [Matrix.mul_assoc]
  have h2 : star (A.1ᴴ * B.1).trace = -(Formalism.UG.Jpq P Q * B.1 * (Formalism.UG.Jpq P Q * A.1)).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, key B.1 hB,
      Matrix.neg_mul, Matrix.trace_neg]
    simp only [Matrix.mul_assoc]
  have h3 : star (A.1ᴴ * B.1).trace = (A.1ᴴ * B.1).trace := by
    rw [h2, h1, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.mp h3

/- English proof (translation)
Establish `hn : ∀ Z, ‖coord e Z‖ ^ 2 = (Zᴴ * Z).trace.re` using `fun Z => by`. Rewrite using `[← real_inner_self_eq_norm_sq, inner_coord]`. Rewrite using `[hn, hn, hn]`. Establish `e1` using `trace_im A B`. Establish `e2` using `trace_im B A`.

Establish `hI : star Complex.I = -Complex.I` using `Complex.conj_I`. Establish `hZ : (A.1 + Complex.I • B.1)ᴴ * (A.1 + Complex.I • B.1) = A.1ᴴ * A.1 + B.1ᴴ * B.1 + Complex.I • (A.1ᴴ * B.1) - Complex.I • (B.1ᴴ * A.1)`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hI]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul, smul_neg]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hZ]`. Simplify using `only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]`. Combine the linear relations using `[e1, e2]`.
-/
theorem norm_sq_add (e : Fin P ⊕ Fin Q ≃ Fin n) (A B : lieU P Q) :
    ‖coord e (A.1 + Complex.I • B.1)‖ ^ 2 = ‖coord e A.1‖ ^ 2 + ‖coord e B.1‖ ^ 2 := by
  have hn : ∀ Z, ‖coord e Z‖ ^ 2 = (Zᴴ * Z).trace.re := fun Z => by
    rw [← real_inner_self_eq_norm_sq, inner_coord]
  rw [hn, hn, hn]
  have e1 := trace_im A B
  have e2 := trace_im B A
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hZ : (A.1 + Complex.I • B.1)ᴴ * (A.1 + Complex.I • B.1) =
      A.1ᴴ * A.1 + B.1ᴴ * B.1 + Complex.I • (A.1ᴴ * B.1) - Complex.I • (B.1ᴴ * A.1) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hI]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, neg_mul,
      Complex.I_mul_I, neg_neg, one_smul, neg_smul, smul_neg]
    abel
  rw [hZ]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.I_re, Complex.I_im]
  linarith [e1, e2]

def cplxIsom (e : Fin P ⊕ Fin Q ≃ Fin n) :
    WithLp 2 (lieE (UH (form e)) × lieE (UH (form e))) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) where
  toFun p := coord e (((lieCoord e).symm p.fst).1 + Complex.I • ((lieCoord e).symm p.snd).1)
  map_add' p q := by
    rw [← map_add]; congr 1
    simp only [WithLp.add_fst, WithLp.add_snd, map_add, Submodule.coe_add, smul_add]
    abel
  map_smul' c p := by
    rw [RingHom.id_apply, ← map_smul]; congr 1
    simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, Submodule.coe_smul, smul_add]
    rw [smul_comm c Complex.I]
  norm_map' p := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2]
    refine (norm_sq_add e _ _).trans ?_
    rw [← coe_lieCoord, ← coe_lieCoord, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    rfl

/- English proof (translation)
Introduce `v`. Establish `hJ` using `GlobalTheory.UpqExpChart.jpq_sq P Q`. Establish `hJh` using `GlobalTheory.OmegaLebExists.J_conjTranspose P Q`. Establish `hJJ : ∀ W : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * W) = W` using `fun W => by`. Rewrite using `[← Matrix.mul_assoc, hJ, Matrix.one_mul]`.

Use `set J := Formalism.UG.Jpq P Q`. Use `set Z := (coord e).symm v`. Set `A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ` to `(1 / 2 : ℂ) • (Z - J * Zᴴ * J)`. Set `B : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ` to `(-Complex.I / 2) • (Z + J * Zᴴ * J)`. Establish `s1 : star (1 / 2 : ℂ) = 1 / 2` using `by simp`.

Establish `s2 : star (-Complex.I / 2) = Complex.I / 2` using `by simp [Complex.conj_I]`. Establish `hA : A ∈ lieU P Q` using `by show Aᴴ * J + J * A = 0`. Simplify using `only [A, Matrix.conjTranspose_smul, s1, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJ, hJJ, Matrix.mul_one, ← smul_add]`. Rewrite using `[show Zᴴ * J - J * Z + (J * Z - Zᴴ * J) = 0 by abel, smul_zero]`. Establish `hB : B ∈ lieU P Q` using `by show Bᴴ * J + J * B = 0`.

Simplify using `only [B, Matrix.conjTranspose_smul, s2, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJ, hJJ, Matrix.mul_one]`. Rewrite using `[show -Complex.I / 2 = -(Complex.I / 2) by ring, neg_smul, ← sub_eq_add_neg, ← smul_sub]`. Rewrite using `[show Zᴴ * J + J * Z - (J * Z + Zᴴ * J) = 0 by abel, smul_zero]`. Establish `hAB : A + Complex.I • B = Z`. Simplify using `only [A, B, smul_smul, smul_sub, smul_add]`.

Rewrite using `[show Complex.I * (-Complex.I / 2) = 1 / 2 by field_simp; simp [Complex.I_sq]]`. Rewrite using `[← sub_eq_zero]`. Establish `: (2 : ℂ) ≠ 0` using `two_ne_zero`. Rewrite using `[show (1 / 2 : ℂ) • Z - (1 / 2 : ℂ) • (J * Zᴴ * J) + ((1 / 2 : ℂ) • Z + (1 / 2 : ℂ) • (J * Zᴴ * J)) - Z = ((1 / 2 : ℂ) + 1 / 2 - 1) • Z by module]`. Evaluate the numerical expressions.

Use `⟨WithLp.toLp 2 (lieCoord e ⟨A, hA⟩, lieCoord e ⟨B, hB⟩), ?_⟩` and prove the remaining obligations. Use `show coord e (((lieCoord e).symm (lieCoord e ⟨A, hA⟩)).1 + Complex.I • ((lieCoord e).symm (lieCoord e ⟨B, hB⟩)).1) = v`. Rewrite using `[ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]`. Use `show coord e (A + Complex.I • B) = v`. Rewrite using `[hAB]`.

Conclude with `(coord e).apply_symm_apply v`.
-/
theorem cplxIsom_surjective (e : Fin P ⊕ Fin Q ≃ Fin n) : Function.Surjective (cplxIsom e) := by
  intro v
  have hJ := GlobalTheory.UpqExpChart.jpq_sq P Q
  have hJh := GlobalTheory.OmegaLebExists.J_conjTranspose P Q
  have hJJ : ∀ W : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * W) = W := fun W => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  set J := Formalism.UG.Jpq P Q
  set Z := (coord e).symm v
  let A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (1 / 2 : ℂ) • (Z - J * Zᴴ * J)
  let B : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (-Complex.I / 2) • (Z + J * Zᴴ * J)
  have s1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have s2 : star (-Complex.I / 2) = Complex.I / 2 := by simp [Complex.conj_I]
  have hA : A ∈ lieU P Q := by
    show Aᴴ * J + J * A = 0
    simp only [A, Matrix.conjTranspose_smul, s1, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hJ, hJJ, Matrix.mul_one, ← smul_add]
    rw [show Zᴴ * J - J * Z + (J * Z - Zᴴ * J) = 0 by abel, smul_zero]
  have hB : B ∈ lieU P Q := by
    show Bᴴ * J + J * B = 0
    simp only [B, Matrix.conjTranspose_smul, s2, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hJ, hJJ, Matrix.mul_one]
    rw [show -Complex.I / 2 = -(Complex.I / 2) by ring, neg_smul, ← sub_eq_add_neg, ← smul_sub]
    rw [show Zᴴ * J + J * Z - (J * Z + Zᴴ * J) = 0 by abel, smul_zero]
  have hAB : A + Complex.I • B = Z := by
    simp only [A, B, smul_smul, smul_sub, smul_add]
    rw [show Complex.I * (-Complex.I / 2) = 1 / 2 by field_simp; simp [Complex.I_sq]]
    rw [← sub_eq_zero]
    have : (2 : ℂ) ≠ 0 := two_ne_zero
    rw [show (1 / 2 : ℂ) • Z - (1 / 2 : ℂ) • (J * Zᴴ * J) + ((1 / 2 : ℂ) • Z + (1 / 2 : ℂ) • (J * Zᴴ * J)) - Z =
      ((1 / 2 : ℂ) + 1 / 2 - 1) • Z by module]
    norm_num
  refine ⟨WithLp.toLp 2 (lieCoord e ⟨A, hA⟩, lieCoord e ⟨B, hB⟩), ?_⟩
  show coord e (((lieCoord e).symm (lieCoord e ⟨A, hA⟩)).1 + Complex.I • ((lieCoord e).symm (lieCoord e ⟨B, hB⟩)).1) = v
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  show coord e (A + Complex.I • B) = v
  rw [hAB]
  exact (coord e).apply_symm_apply v

/- English proof (translation)
Establish `: BorelSpace (lieU P Q)` using `⟨rfl⟩`. Use `⟨(lieCoord e).symm.isAddHaarMeasure_map _, ?_⟩` and prove the remaining obligations. Establish `hLs : Measurable (lieCoord e).symm` using `(lieCoord e).symm.continuous.measurable`. Establish `hL : Measurable (lieCoord e)` using `(lieCoord e).continuous.measurable`. Establish `hI` using `(LinearIsometryEquiv.ofSurjective (cplxIsom e) (cplxIsom_surjective e)).measurePreserving`.

Establish `hT` using `(measurePreserving_unrealify (ι := Fin P ⊕ Fin Q) e).comp (hI.comp (WithLp.volume_preserving_toLp (U := lieE (UH (form e))) (V := lieE (UH (form e)))))`. Establish `hG : Measurable (fun ab : lieU P Q × lieU P Q => entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) + Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))`. Use `hT.measurable.comp (hL.prodMap hL) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `ab`. Use function extensionality and compare the values at `p`.

Use `show ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) + Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) p.1 p.2 = unrealify (coord e (((lieCoord e).symm (lieCoord e ab.1) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) + Complex.I • ((lieCoord e).symm (lieCoord e ab. …`. Rewrite using `[ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply, unrealify_coord]`. Simplify using the standard rewrite rules. Rewrite using `[Measure.map_prod_map _ _ hLs hLs, Measure.map_map hG (hLs.prodMap hLs)]`. Use `hT.map_eq using 2` and compare the differences between its conclusion and the goal.

Use `case e'_6 => rfl`. Use function extensionality and compare the values at `ab`. Use function extensionality and compare the values at `p`. Use `show ((lieCoord e).symm ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) p.1 p.2 + (Complex.I • ((lieCoord e).symm ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) p.1 p.2 = unrealify (coord e (((lieCoord e).symm ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) + Complex.I • ((l …`. Rewrite using `[unrealify_coord]`.

Simplify using the standard rewrite rules.
-/
theorem isOmegaLeb_frobenius (e : Fin P ⊕ Fin Q ≃ Fin n) :
    IsOmegaLeb ((volume : Measure (lieE (UH (form e)))).map (lieCoord e).symm) := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  refine ⟨(lieCoord e).symm.isAddHaarMeasure_map _, ?_⟩
  have hLs : Measurable (lieCoord e).symm := (lieCoord e).symm.continuous.measurable
  have hL : Measurable (lieCoord e) := (lieCoord e).continuous.measurable
  have hI := (LinearIsometryEquiv.ofSurjective (cplxIsom e) (cplxIsom_surjective e)).measurePreserving
  have hT := (measurePreserving_unrealify (ι := Fin P ⊕ Fin Q) e).comp
    (hI.comp (WithLp.volume_preserving_toLp (U := lieE (UH (form e))) (V := lieE (UH (form e)))))
  have hG : Measurable (fun ab : lieU P Q × lieU P Q =>
      entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) := by
    convert hT.measurable.comp (hL.prodMap hL) using 1
    funext ab
    funext p
    show ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) p.1 p.2 =
      unrealify (coord e (((lieCoord e).symm (lieCoord e ab.1) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • ((lieCoord e).symm (lieCoord e ab.2) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) (e p.1) (e p.2)
    rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply, unrealify_coord]
    simp
  rw [Measure.map_prod_map _ _ hLs hLs, Measure.map_map hG (hLs.prodMap hLs)]
  convert hT.map_eq using 2
  case e'_6 => rfl
  funext ab
  funext p
  show ((lieCoord e).symm ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) p.1 p.2 +
      (Complex.I • ((lieCoord e).symm ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) p.1 p.2 =
    unrealify (coord e (((lieCoord e).symm ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
      Complex.I • ((lieCoord e).symm ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) (e p.1) (e p.2)
  rw [unrealify_coord]
  simp

def emb (e : Fin P ⊕ Fin Q ≃ Fin n) (g : UpqT P Q) : PI.MtM n :=
  Matrix.of.symm (Matrix.reindex e e (UpqT.mat g))

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (congrFun h (e i)) (e j)` as an intermediate fact. Simplify using `using this`.
-/
theorem submatrix_inj (e : Fin P ⊕ Fin Q ≃ Fin n) {X Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : X.submatrix e.symm e.symm = Y.submatrix e.symm e.symm) : X = Y := by
  ext i j
  have := congrFun (congrFun h (e i)) (e j)
  simpa using this

/- English proof (translation)
Set `h : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ ≃ₜ PI.MtM n` to `{ toEquiv := (Matrix.reindex e e).trans Matrix.of.symm continuous_toFun := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (e.symm i) (e.symm j) continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (e i) (e j) }`. Conclude with `h.isClosedEmbedding.comp (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P) (Q := Q))`.
-/
theorem isClosedEmbedding_emb (e : Fin P ⊕ Fin Q ≃ Fin n) : IsClosedEmbedding (emb e) := by
  let h : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ ≃ₜ PI.MtM n :=
    { toEquiv := (Matrix.reindex e e).trans Matrix.of.symm
      continuous_toFun := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (e.symm i) (e.symm j)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (e i) (e j) }
  exact h.isClosedEmbedding.comp (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P) (Q := Q))

/- English proof (translation)
Use `show (X.submatrix e.symm e.symm)ᴴ * (Formalism.UG.Jpq P Q).submatrix e.symm e.symm * X.submatrix e.symm e.symm = (Formalism.UG.Jpq P Q).submatrix e.symm e.symm ↔ _`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`. Conclude with `⟨submatrix_inj e, fun h => by rw [h]⟩`.
-/
theorem submatrix_mem_UH (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X.submatrix e.symm e.symm ∈ UH (form e) ↔ Xᴴ * Formalism.UG.Jpq P Q * X = Formalism.UG.Jpq P Q := by
  show (X.submatrix e.symm e.symm)ᴴ * (Formalism.UG.Jpq P Q).submatrix e.symm e.symm * X.submatrix e.symm e.symm =
    (Formalism.UG.Jpq P Q).submatrix e.symm e.symm ↔ _
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  exact ⟨submatrix_inj e, fun h => by rw [h]⟩

/- English proof (translation)
Establish `hl` using `GlobalTheory.UpqTopology.upq_lcsc P Q`. Use `hl.1` as an intermediate fact. Use `hl.2.1` as an intermediate fact. Use `hl.2.2.1` as an intermediate fact. Use `hl.2.2.2.1` as an intermediate fact.

Use `hl.2.2.2.2.1` as an intermediate fact. Establish `hme : MeasurableEmbedding (emb e)` using `(isClosedEmbedding_emb e).measurableEmbedding`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hme.sigmaFinite_map`. Conclude with `(Measure.map_ne_zero_iff hme.measurable.aemeasurable).2 (NeZero.ne μ)`.

Rewrite using `[hme.map_apply]`. Establish `hemp : emb e ⁻¹' {x | Matrix.of x ∉ UH (form e)} = ∅`. Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]`. Conclude with `(submatrix_mem_UH e _).2 (GlobalTheory.UpqTopology.mat_unitary g)`.

Rewrite using `[hemp, measure_empty]`. Introduce `s hs`. Establish `hss : (s.submatrix e e).submatrix e.symm e.symm = s` using `by ext i j; simp`. Establish `hX : (s.submatrix e e)ᴴ * Formalism.UG.Jpq P Q * s.submatrix e e = Formalism.UG.Jpq P Q`. Rewrite using `[← submatrix_mem_UH e, hss]`.

Conclude with `hs`. Take `⟨g, hg⟩ : s.submatrix e e ∈ Set.range (UpqT.mat (P` from `P) (Q := Q)) := by`. Rewrite using `[GlobalTheory.UpqTopology.range_mat]`. Conclude with `hX`. Establish `hs' : s = (UpqT.mat g).submatrix e.symm e.symm` using `by rw [hg, hss]`.

Establish `hcomm : PI.lmulQ s ∘ emb e = emb e ∘ (fun h => g * h)`. Use function extensionality and compare the values at `h`. Use `show s * (UpqT.mat h).submatrix e.symm e.symm = (UpqT.mat (g * h)).submatrix e.symm e.symm`. Rewrite using `[hs', Matrix.submatrix_mul_equiv, GlobalTheory.HaarDensityUpq.mat_mul]`. Establish `hmeas : Measurable (PI.lmulQ s)`.

Establish `: Continuous (PI.lmulQ s)`. Unfold `PI.lmulQ`. Conclude with `continuous_const.matrix_mul continuous_id`. Conclude with `this.measurable`. Rewrite using `[Measure.map_map hmeas hme.measurable, hcomm, ← Measure.map_map hme.measurable (measurable_const_mul g), map_mul_left_eq_self]`.
-/
theorem isHaarOnM_map (e : Fin P ⊕ Fin Q ≃ Fin n) (μ : Measure (UpqT P Q)) [μ.IsHaarMeasure] :
    PI.IsHaarOnM (UH (form e)) (μ.map (emb e)) := by
  have hl := GlobalTheory.UpqTopology.upq_lcsc P Q
  have := hl.1
  have := hl.2.1
  have := hl.2.2.1
  have := hl.2.2.2.1
  have := hl.2.2.2.2.1
  have hme : MeasurableEmbedding (emb e) := (isClosedEmbedding_emb e).measurableEmbedding
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hme.sigmaFinite_map
  · exact (Measure.map_ne_zero_iff hme.measurable.aemeasurable).2 (NeZero.ne μ)
  · rw [hme.map_apply]
    have hemp : emb e ⁻¹' {x | Matrix.of x ∉ UH (form e)} = ∅ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact (submatrix_mem_UH e _).2 (GlobalTheory.UpqTopology.mat_unitary g)
    rw [hemp, measure_empty]
  · intro s hs
    have hss : (s.submatrix e e).submatrix e.symm e.symm = s := by ext i j; simp
    have hX : (s.submatrix e e)ᴴ * Formalism.UG.Jpq P Q * s.submatrix e e = Formalism.UG.Jpq P Q := by
      rw [← submatrix_mem_UH e, hss]
      exact hs
    obtain ⟨g, hg⟩ : s.submatrix e e ∈ Set.range (UpqT.mat (P := P) (Q := Q)) := by
      rw [GlobalTheory.UpqTopology.range_mat]
      exact hX
    have hs' : s = (UpqT.mat g).submatrix e.symm e.symm := by rw [hg, hss]
    have hcomm : PI.lmulQ s ∘ emb e = emb e ∘ (fun h => g * h) := by
      funext h
      show s * (UpqT.mat h).submatrix e.symm e.symm = (UpqT.mat (g * h)).submatrix e.symm e.symm
      rw [hs', Matrix.submatrix_mul_equiv, GlobalTheory.HaarDensityUpq.mat_mul]
    have hmeas : Measurable (PI.lmulQ s) := by
      have : Continuous (PI.lmulQ s) := by
        unfold PI.lmulQ
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hmeas hme.measurable, hcomm, ← Measure.map_map hme.measurable (measurable_const_mul g),
      map_mul_left_eq_self]

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Set `T' : E →L[ℝ] Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toContinuousLinearMap T`. Set `π : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ` to `{ toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Set `π' : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap π`. Establish `hg : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (T' 0)`. Rewrite using `[map_zero]`.

Conclude with `hasStrictFDerivAt_exp_zero (𝕂 := ℝ)`. Establish `h2` using `π'.hasStrictFDerivAt.comp (0 : E) (hg.comp (0 : E) T'.hasStrictFDerivAt)`. Use `⟨π'.comp ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).comp T'), ?_, fun v => ?_⟩` and prove the remaining obligations. Conclude with `h2`. Both sides reduce to the same expression.
-/
theorem hasStrictFDerivAt_entry {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ∃ D : E →L[ℝ] ℂ, HasStrictFDerivAt (fun x => NormedSpace.exp (T x) i j) D 0 ∧ ∀ v, D v = T v i j := by
  let T' : E →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap T
  let π : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let π' : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap π
  have hg : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (T' 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero (𝕂 := ℝ)
  have h2 := π'.hasStrictFDerivAt.comp (0 : E) (hg.comp (0 : E) T'.hasStrictFDerivAt)
  refine ⟨π'.comp ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).comp T'), ?_, fun v => ?_⟩
  · exact h2
  · rfl

/- English proof (translation)
Rewrite using `[PiLp.norm_eq_of_L1, Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
private theorem norm_toL1_eq_sum_norm_entries (X : lieU P Q) :
    ‖GlobalTheory.HaarDensityUpq.toL1 P Q X‖ = ∑ i, ∑ j, ‖(X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ := by
  rw [PiLp.norm_eq_of_L1, Fintype.sum_prod_type]
  rfl

/- English proof (translation)
Establish `: BorelSpace (lieU P Q)` using `⟨rfl⟩`. Establish `hl` using `GlobalTheory.UpqTopology.upq_lcsc P Q`. Use `hl.1` as an intermediate fact. Use `hl.2.1` as an intermediate fact. Use `hl.2.2.1` as an intermediate fact.

Use `hl.2.2.2.1` as an intermediate fact. Use `hl.2.2.2.2.1` as an intermediate fact. Establish `hme : MeasurableEmbedding (emb e)` using `(isClosedEmbedding_emb e).measurableEmbedding`. Establish `hLme : MeasurableEmbedding (lieCoord e).symm` using `(lieCoord e).symm.toHomeomorph.measurableEmbedding`. Use `letI := GlobalTheory.HaarDensityUpq.sumNorm P Q`.

Use `letI : NormedSpace ℝ (lieU P Q) := ⟨fun a X => by show ‖GlobalTheory.HaarDensityUpq.toL1 P Q (a • X)‖ ≤ ‖a‖ * ‖GlobalTheory.HaarDensityUpq.toL1 P Q X‖`. Rewrite using `[map_smul]`. Conclude with `norm_smul_le a _⟩`. Establish `hball : ∀ r : ℝ, Metric.ball (0 : lieU P Q) r = ballU P Q r`. Introduce `r`.

Use extensionality with `X`. Rewrite using `[mem_ball_zero_iff]`. Use `show ‖GlobalTheory.HaarDensityUpq.toL1 P Q X‖ < r ↔ ∑ i, ∑ j, ‖(X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r`. Rewrite using `[norm_toL1_eq_sum_norm_entries]`. Set `Φ : lieU P Q → Matrix (Fin n) (Fin n) ℂ` to `fun X => (NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).submatrix e.symm e.symm`.

Establish `hΦ0 : Φ 0 = 1` using `by simp [Φ]`. Establish `hΦS : ∀ᶠ x in 𝓝 (0 : lieU P Q), Φ x ∈ UH (form e)` using `Filter.Eventually.of_forall fun X => (submatrix_mem_UH e _).2 (GlobalTheory.UpqExpChart.exp_unitary (GlobalTheory.UpqExpChart.jpq_sq P Q) X.2)`. Establish `hder : ∀ i j, ∃ D : lieU P Q →L[ℝ] ℂ, HasStrictFDerivAt (fun x => Φ x i j) D 0 ∧ ∀ v, D v = unrealify ((lieCoord e v : lieE (UH (form e))) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) i j`. Introduce `i j`. Set `T : lieU P Q →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ` to `{ toFun := fun X => (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix e.symm e.symm map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Apply the tactic sequence `obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_entry T i j`. Use `⟨D, ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `hf : (fun x => Φ x i j) = fun x => NormedSpace.exp (T x) i j`. Use function extensionality and compare the values at `x`. Use `show (NormedSpace.exp (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).submatrix e.symm e.symm i j = NormedSpace.exp ((x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix e.symm e.symm) i j`.

Rewrite using `[GlobalTheory.CompactDualSwap.exp_submatrix]`. Rewrite using `[hf]`. Conclude with `hD`. Rewrite using `[hDv, coe_lieCoord, unrealify_coord]`. Both sides reduce to the same expression.

Establish `key` using `GlobalTheory.T.tendsto_measure_image_ball_div_volume n (UH (form e)) (μ.map (emb e)) c (isMatGroup_UH _ (form_sq e)) (isHaarOnM_map e μ) hc (lieU P Q) Φ (lieCoord e) hΦ0 hΦS hder`. Use `⟨_, isOmegaLeb_frobenius e, key.congr fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[hball r]`. Use `congr 1`. Rewrite using `[hme.map_apply]`.

Use `congr 1`. Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X, hX, h⟩`.

Conclude with `⟨X, hX, (submatrix_inj e (X := NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) (Y := UpqT.mat g) h).symm⟩`. Introduce and unpack `⟨X, hX, h⟩`. Use `⟨X, hX, ?_⟩` and prove the remaining obligations. Use `show (NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).submatrix e.symm e.symm = (UpqT.mat g).submatrix e.symm e.symm`. Rewrite using `[h]`.

Rewrite using `[hLme.map_apply]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Simplify using `using hy`. Introduce `hx`. Conclude with `⟨(lieCoord e).symm x, hx, (lieCoord e).apply_symm_apply x⟩`.
-/
theorem omegaDensity_of_hasDens (e : Fin P ⊕ Fin Q ≃ Fin n) (μ : Measure (UpqT P Q)) [μ.IsHaarMeasure]
    (c : ℝ≥0∞) (hc : HasDens (UH (form e)) (μ.map (emb e)) c) : OmegaDensity μ c := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have hl := GlobalTheory.UpqTopology.upq_lcsc P Q
  have := hl.1
  have := hl.2.1
  have := hl.2.2.1
  have := hl.2.2.2.1
  have := hl.2.2.2.2.1
  have hme : MeasurableEmbedding (emb e) := (isClosedEmbedding_emb e).measurableEmbedding
  have hLme : MeasurableEmbedding (lieCoord e).symm := (lieCoord e).symm.toHomeomorph.measurableEmbedding
  letI := GlobalTheory.HaarDensityUpq.sumNorm P Q
  letI : NormedSpace ℝ (lieU P Q) := ⟨fun a X => by
    show ‖GlobalTheory.HaarDensityUpq.toL1 P Q (a • X)‖ ≤ ‖a‖ * ‖GlobalTheory.HaarDensityUpq.toL1 P Q X‖
    rw [map_smul]
    exact norm_smul_le a _⟩
  have hball : ∀ r : ℝ, Metric.ball (0 : lieU P Q) r = ballU P Q r := by
    intro r
    ext X
    rw [mem_ball_zero_iff]
    show ‖GlobalTheory.HaarDensityUpq.toL1 P Q X‖ < r ↔ ∑ i, ∑ j, ‖(X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r
    rw [norm_toL1_eq_sum_norm_entries]
  let Φ : lieU P Q → Matrix (Fin n) (Fin n) ℂ := fun X =>
    (NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).submatrix e.symm e.symm
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hΦS : ∀ᶠ x in 𝓝 (0 : lieU P Q), Φ x ∈ UH (form e) := Filter.Eventually.of_forall fun X =>
    (submatrix_mem_UH e _).2 (GlobalTheory.UpqExpChart.exp_unitary (GlobalTheory.UpqExpChart.jpq_sq P Q) X.2)
  have hder : ∀ i j, ∃ D : lieU P Q →L[ℝ] ℂ, HasStrictFDerivAt (fun x => Φ x i j) D 0 ∧
      ∀ v, D v = unrealify ((lieCoord e v : lieE (UH (form e))) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) i j := by
    intro i j
    let T : lieU P Q →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      { toFun := fun X => (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix e.symm e.symm
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    obtain ⟨D, hD, hDv⟩ := hasStrictFDerivAt_entry T i j
    refine ⟨D, ?_, fun v => ?_⟩
    · have hf : (fun x => Φ x i j) = fun x => NormedSpace.exp (T x) i j := by
        funext x
        show (NormedSpace.exp (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).submatrix e.symm e.symm i j =
          NormedSpace.exp ((x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix e.symm e.symm) i j
        rw [GlobalTheory.CompactDualSwap.exp_submatrix]
      rw [hf]
      exact hD
    · rw [hDv, coe_lieCoord, unrealify_coord]
      rfl
  have key := GlobalTheory.T.tendsto_measure_image_ball_div_volume n (UH (form e)) (μ.map (emb e)) c (isMatGroup_UH _ (form_sq e)) (isHaarOnM_map e μ) hc
    (lieU P Q) Φ (lieCoord e) hΦ0 hΦS hder
  refine ⟨_, isOmegaLeb_frobenius e, key.congr fun r => ?_⟩
  rw [hball r]
  congr 1
  · rw [hme.map_apply]
    congr 1
    ext g
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨X, hX, h⟩
      exact ⟨X, hX, (submatrix_inj e (X := NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
        (Y := UpqT.mat g) h).symm⟩
    · rintro ⟨X, hX, h⟩
      refine ⟨X, hX, ?_⟩
      show (NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).submatrix e.symm e.symm =
        (UpqT.mat g).submatrix e.symm e.symm
      rw [h]
  · rw [hLme.map_apply]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨(lieCoord e).symm x, hx, (lieCoord e).apply_symm_apply x⟩

/- English proof (translation)
Introduce `n ε P Q e h1 h2 μ c hμ hc`. Use `hμ` as an intermediate fact. Rewrite using `[jm_eq h1 h2]`. Establish `hH` using `isHaarOnM_map e μ`. Use `⟨hH, ?_⟩` and prove the remaining obligations.

Take `⟨c', -, hc', -⟩` from `GlobalTheory.T.exists_unique_haarDensity_at_identity n (UH (form e)) (μ.map (emb e)) (isMatGroup_UH _ (form_sq e)) hH`. Establish `h3` using `omegaDensity_of_hasDens e μ _ hc'`. Rewrite using `[GlobalTheory.OmegaDensityScale.omegaDensity_unique h3 hc]`. Conclude with `hc'`.
-/
theorem hasDens_of_omegaDensity : ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ (μ : Measure (Formalism.BasicNotions.UpqT P Q)) (c : ℝ≥0∞), μ.IsHaarMeasure → Formalism.BasicNotions.OmegaDensity μ c → PI.IsHaarOnM (UH (Formalism.REAL.Jm ε)) (μ.map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧ HasDens (UH (Formalism.REAL.Jm ε)) (μ.map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) c := by
  intro n ε P Q e h1 h2 μ c hμ hc
  have := hμ
  rw [jm_eq h1 h2]
  have hH := isHaarOnM_map e μ
  refine ⟨hH, ?_⟩
  obtain ⟨c', -, hc', -⟩ := GlobalTheory.T.exists_unique_haarDensity_at_identity n (UH (form e)) (μ.map (emb e)) (isMatGroup_UH _ (form_sq e)) hH
  have h3 := omegaDensity_of_hasDens e μ _ hc'
  rw [GlobalTheory.OmegaDensityScale.omegaDensity_unique h3 hc]
  exact hc'

end GlobalTheory.OmegaFrobenius
