import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.NormFixedUnitaryEntryLeOne

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k : ℕ}

def sg (k : ℕ) (i : Fin (2 * 0 + k + 1)) : ℂ := if i = iK k then -1 else 1

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma hpk_diag (k : ℕ) : Hpk k 0 = Matrix.diagonal (sg k) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Matrix.diagonal_apply, sg, iK, wI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | simp_all

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma hpk_mulVec (v : Fin (2 * 0 + k + 1) → ℂ) (i : Fin (2 * 0 + k + 1)) :
    (Hpk k 0 *ᵥ v) i = sg k i * v i := by
  rw [hpk_diag, Matrix.mulVec_diagonal]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma hpk_sq (k : ℕ) : Hpk k 0 * Hpk k 0 = 1 := by
  rw [hpk_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [sg]
  split_ifs <;> norm_num

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma herm0 (v w : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k 0) v w = ∑ i, star (w i) * (sg k i * v i) := by
  simp only [herm, dotProduct, Pi.star_apply, hpk_mulVec]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma herm_re (y : Fin (2 * 0 + k + 1) → ℂ) :
    (herm (Hpk k 0) y y).re = tW (iK k) y ^ 2 - Complex.normSq (y (iK k)) := by
  have hterm : ∀ i, (star (y i) * (sg k i * y i)).re =
      Complex.normSq (y i) - (if i = iK k then 2 * Complex.normSq (y i) else 0) := by
    intro i
    by_cases h : i = iK k
    · simp [sg, h, Complex.normSq_apply, Complex.mul_re]
      ring
    · simp [sg, h, Complex.normSq_apply, Complex.mul_re]
  rw [herm0, tW_sq, Complex.re_sum, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma phi'_eq (hk : 1 ≤ k) :
    phiV' k 0 0 = ((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) - bvec (iK k)) := by
  have hWK := iW_ne_iK hk
  funext i
  rw [phiV', hpk_mulVec]
  show sg k i * (((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) + bvec (iK k))) i = (((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) - bvec (iK k))) i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, bvec]
  rcases eq_or_ne i (iW k) with rfl | h1
  · simp [sg, hWK]
  · rcases eq_or_ne i (iK k) with rfl | h2
    · simp [sg, hWK.symm]
    · simp [h1, h2]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma phi'_iW (hk : 1 ≤ k) : phiV' k 0 0 (iW k) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [phi'_eq hk]
  simp [bvec, iW_ne_iK hk]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma phi'_iK (hk : 1 ≤ k) : phiV' k 0 0 (iK k) = -((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [phi'_eq hk]
  simp [bvec, (iW_ne_iK hk).symm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma phi'_zero (hk : 1 ≤ k) (i : Fin (2 * 0 + k + 1)) (h1 : i ≠ iW k) (h2 : i ≠ iK k) :
    phiV' k 0 0 i = 0 := by
  rw [phi'_eq hk]
  simp [bvec, h1, h2]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
lemma normSq_c : Complex.normSq ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma star_c : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma norm_c : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
  rw [norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Evaluate the numerical expressions.
-/
lemma phi'_dot (hk : 1 ≤ k) : star (phiV' k 0 0) ⬝ᵥ phiV' k 0 0 = 1 := by
  have hWK := iW_ne_iK hk
  have hφ : ∀ i, Complex.normSq (phiV' k 0 0 i) =
      (if i = iW k then 1 / 2 else 0) + (if i = iK k then 1 / 2 else 0) := by
    intro i
    rcases eq_or_ne i (iW k) with rfl | h1
    · rw [phi'_iW hk, normSq_c, if_pos rfl, if_neg hWK, add_zero]
    · rcases eq_or_ne i (iK k) with rfl | h2
      · rw [phi'_iK hk, Complex.normSq_neg, normSq_c, if_neg h1, if_pos rfl, zero_add]
      · rw [phi'_zero hk i h1 h2, map_zero, if_neg h1, if_neg h2, add_zero]
  rw [dot_star_self, Finset.sum_congr rfl fun i _ => hφ i, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sum_phi_lemma (hk : 1 ≤ k) (X : Fin (2 * 0 + k + 1) → ℂ) :
    ∑ i, star (phiV' k 0 0 i) * (sg k i * X i) = ((Real.sqrt 2)⁻¹ : ℂ) * (X (iW k) + X (iK k)) := by
  have hWK := iW_ne_iK hk
  have h : ∀ i, star (phiV' k 0 0 i) * (sg k i * X i) =
      (if i = iW k then ((Real.sqrt 2)⁻¹ : ℂ) * X (iW k) else 0) + (if i = iK k then ((Real.sqrt 2)⁻¹ : ℂ) * X (iK k) else 0) := by
    intro i
    rcases eq_or_ne i (iW k) with rfl | h1
    · rw [phi'_iW hk, star_c, if_pos rfl, if_neg hWK, add_zero]
      simp [sg, hWK]
    · rcases eq_or_ne i (iK k) with rfl | h2
      · rw [phi'_iK hk, star_neg, star_c, if_neg h1, if_pos rfl, zero_add]
        simp [sg]
      · rw [phi'_zero hk i h1 h2, star_zero, zero_mul, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
lemma phi'_iso (hk : 1 ≤ k) : herm (Hpk k 0) (phiV' k 0 0) (phiV' k 0 0) = 0 := by
  rw [herm0, sum_phi_lemma hk, phi'_iW hk, phi'_iK hk]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private lemma dl0_lemma_2 (M : Mat k 0) :
    Dl k 0 0 M = herm (Hpk k 0) (M *ᵥ phiV' k 0 0) (phiV' k 0 0) := by
  unfold Dl
  exact Matrix.det_fin_one _

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma dl_eq (hk : 1 ≤ k) (M : Mat k 0) :
    Dl k 0 0 M = ((Real.sqrt 2)⁻¹ : ℂ) * ((M *ᵥ phiV' k 0 0) (iW k) + (M *ᵥ phiV' k 0 0) (iK k)) := by
  rw [dl0_lemma_2, herm0, sum_phi_lemma hk]

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma G_left {g : Mat k 0} (hg : g ∈ GV k 0) : (Hpk k 0 * gᴴ * Hpk k 0) * g = 1 := by
  have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
  calc Hpk k 0 * gᴴ * Hpk k 0 * g = Hpk k 0 * (gᴴ * Hpk k 0 * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma G_star {g : Mat k 0} (hg : g ∈ GV k 0) : g * Hpk k 0 * gᴴ = Hpk k 0 := by
  have h1 : g * (Hpk k 0 * gᴴ * Hpk k 0) = 1 := mul_eq_one_comm.mp (G_left hg)
  calc g * Hpk k 0 * gᴴ = g * (Hpk k 0 * gᴴ * Hpk k 0) * Hpk k 0 := by
        simp only [Matrix.mul_assoc, hpk_sq, Matrix.mul_one]
    _ = Hpk k 0 := by rw [h1, Matrix.one_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma G_det {g : Mat k 0} (hg : g ∈ GV k 0) : g.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (G_left hg)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma herm_G {g : Mat k 0} (hg : g ∈ GV k 0) (v w : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k 0) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k 0) v w := by
  have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg']

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private lemma ga0_lemma_3 (Y : Fin (0 + 1) → Fin (2 * 0 + k + 1) → ℂ) :
    Ga k 0 0 Y = (star (Y 0) ⬝ᵥ Y 0).re := by
  unfold Ga
  exact congrArg Complex.re (Matrix.det_fin_one _)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
lemma sphericalFunction_fixedUnitary_eq_one (hk : 1 ≤ k) {h : Mat k 0} (hh : h ∈ U0 k) (s : Fin (0 + 1) → ℝ) : fsR k 0 s h = 1 := by
  rw [fsR, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ga0_lemma_3]
  rw [fixedUnitary_preserves_normSq hh, phi'_dot hk, Complex.one_re, Real.one_rpow]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
lemma fsE_avg (hk : 1 ≤ k) {h : Mat k 0} (hh : h ∈ U0 k) (g h' : Mat k 0) (s : Fin (0 + 1) → ℝ) :
    FsE k 0 s (h⁻¹ * g * h') = ENNReal.ofReal ((Real.sqrt 2)⁻¹ *
      ‖(hᴴ *ᵥ ((g * h') *ᵥ phiV' k 0 0)) (iW k) + ((g * h') *ᵥ phiV' k 0 0) (iK k)‖) ^ (-s 0) := by
  have hinv : h⁻¹ = hᴴ := Matrix.inv_eq_left_inv (fixedUnitary_projection_identities hh).1
  rw [FsE, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, enn_nnnorm, dl_eq hk, norm_mul, norm_c,
    hinv, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, fixedUnitary_mulVec_fixedIndex (fixedUnitary_conjTranspose_mem hh)]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma outer_eq (hk : 1 ≤ k) {h' : Mat k 0} (hh : h' ∈ U0 k) (g : Mat k 0) :
    ‖((g * h') *ᵥ phiV' k 0 0) (iK k)‖ = (Real.sqrt 2)⁻¹ *
      ‖(h'ᴴ *ᵥ (fun j => star (g (iK k) j))) (iW k) + -star (g (iK k) (iK k))‖ := by
  have hM : ∀ M : Mat k 0, (M *ᵥ phiV' k 0 0) (iK k) =
      ((Real.sqrt 2)⁻¹ : ℂ) * (M (iK k) (iW k) - M (iK k) (iK k)) := by
    intro M
    rw [phi'_eq hk, Matrix.mulVec_smul, Matrix.mulVec_sub]
    simp [bvec, Matrix.mulVec_single]
  rw [hM, norm_mul, norm_c]
  congr 1
  have h1 : (g * h') (iK k) (iK k) = g (iK k) (iK k) := by
    rw [Matrix.mul_apply]
    simp [fixedUnitary_apply_fixedIndex_right hh]
  have h2 : (h'ᴴ *ᵥ fun j => star (g (iK k) j)) (iW k) = star ((g * h') (iK k) (iW k)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum,
      star_mul]
  rw [h1, h2, ← star_neg, ← star_add, norm_star, sub_eq_add_neg]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma outer_ws {g : Mat k 0} (hg : g ∈ GV k 0) :
    tW (iK k) (fun j => star (g (iK k) j)) ^ 2 + 1 = Complex.normSq (g (iK k) (iK k)) := by
  have e : (g * Hpk k 0 * gᴴ) (iK k) (iK k) = Hpk k 0 (iK k) (iK k) := by rw [G_star hg]
  rw [hpk_diag, Matrix.diagonal_apply_eq, Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] at e
  have hsK : sg k (iK k) = -1 := by simp [sg]
  have e2 : herm (Hpk k 0) (fun j => star (g (iK k) j)) (fun j => star (g (iK k) j)) = -1 := by
    rw [herm0, ← hsK, ← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [star_star]
    ring
  have hre := herm_re (k := k) (fun j => star (g (iK k) j))
  rw [e2] at hre
  have hn : Complex.normSq (star (g (iK k) (iK k))) = Complex.normSq (g (iK k) (iK k)) :=
    Complex.normSq_conj _
  simp only [Complex.neg_re, Complex.one_re] at hre
  rw [hn] at hre
  linarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma iso_y (hk : 1 ≤ k) {g h' : Mat k 0} (hg : g ∈ GV k 0) (hh : h' ∈ GV k 0) :
    tW (iK k) ((g * h') *ᵥ phiV' k 0 0) ^ 2 = Complex.normSq (((g * h') *ᵥ phiV' k 0 0) (iK k)) ∧
    ((g * h') *ᵥ phiV' k 0 0) (iK k) ≠ 0 := by
  have hgh : g * h' ∈ GV k 0 := by
    show (g * h')ᴴ * Hpk k 0 * (g * h') = Hpk k 0
    have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
    have hh' : h'ᴴ * Hpk k 0 * h' = Hpk k 0 := hh
    rw [Matrix.conjTranspose_mul]
    calc h'ᴴ * gᴴ * Hpk k 0 * (g * h') = h'ᴴ * (gᴴ * Hpk k 0 * g) * h' := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k 0 := by rw [hg', hh']
  have hiso : herm (Hpk k 0) ((g * h') *ᵥ phiV' k 0 0) ((g * h') *ᵥ phiV' k 0 0) = 0 := by
    rw [herm_G hgh, phi'_iso hk]
  have hre := herm_re ((g * h') *ᵥ phiV' k 0 0)
  rw [hiso, Complex.zero_re] at hre
  refine ⟨by linarith, fun h0 => ?_⟩
  have hsum := tW_sq (iK k) ((g * h') *ᵥ phiV' k 0 0)
  rw [h0, map_zero, sub_zero] at hsum
  rw [h0, map_zero] at hre
  have hz : ∑ i, Complex.normSq (((g * h') *ᵥ phiV' k 0 0) i) = 0 := by
    rw [← hsum]
    linarith
  have hall : ∀ i, ((g * h') *ᵥ phiV' k 0 0) i = 0 := fun i =>
    Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp hz i
        (Finset.mem_univ i))
  have hdet : (g * h').det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (G_det hg) (G_det hh)
  have hphi := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext hall)
  have hW := congrFun hphi (iW k)
  rw [phi'_iW hk, Pi.zero_apply] at hW
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))) hW

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
