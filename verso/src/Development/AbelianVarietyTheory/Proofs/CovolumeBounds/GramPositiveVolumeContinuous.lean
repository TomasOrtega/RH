import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.GramPos

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem sq_half : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

/- English proof (translation)
Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem bvec_pair {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    star (bvec i) ⬝ᵥ M *ᵥ bvec j = M i j := by
  have : star (bvec i : Fin n → ℂ) = bvec i := by
    ext l; by_cases h : l = i <;> simp [bvec, h]
  rw [this]; simp [bvec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem frame_pair (k r : ℕ) (M : Mat k r) (a b : Fin (r + 1)) :
    ((frame k r)ᴴ * M * frame k r) a b =
      star (fvec k r (isoVec k r) a) ⬝ᵥ M *ᵥ fvec k r (isoVec k r) b := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, frame, dotProduct, mulVec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem pair_iso_left (k r : ℕ) (M : Mat k r) (j) :
    star (isoVec k r) ⬝ᵥ M *ᵥ bvec j =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (M (wI k r 0) j + M (wI k r (Fin.last k)) j) := by
  rw [isoVec, star_smul, star_add, smul_dotProduct, add_dotProduct, bvec_pair, bvec_pair]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem pair_iso_right (k r : ℕ) (M : Mat k r) (v) :
    star v ⬝ᵥ M *ᵥ isoVec k r =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ M *ᵥ bvec (wI k r 0) + star v ⬝ᵥ M *ᵥ bvec (wI k r (Fin.last k))) := by
  rw [isoVec, mulVec_smul, mulVec_add, dotProduct_smul, dotProduct_add]
  simp

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem frame_orthonormal (k r : ℕ) (hk : 1 ≤ k) : (frame k r)ᴴ * frame k r = 1 := by
  ext a b
  have := frame_pair k r 1 a b
  rw [Matrix.mul_one] at this
  rw [this]
  have ha := a.isLt
  have hb := b.isLt
  unfold fvec
  split_ifs with h1 h2 h2
  · rw [bvec_pair]; simp [one_apply, eI, Fin.ext_iff]
  · rw [pair_iso_right, bvec_pair, bvec_pair]
    simp only [one_apply, eI, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · rw [pair_iso_left]
    simp only [one_apply, eI, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · rw [pair_iso_right, pair_iso_left, pair_iso_left]
    simp only [one_apply, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    have e : a.val = b.val := by omega
    have h3 : ¬ (r + k = r + 0) := by omega
    have h4 : ¬ (r + 0 = r + k) := by omega
    simp only [if_pos e, h3, h4, if_true, if_false]
    linear_combination 2 * sq_half

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
lemma mulVec_inj (k r : ℕ) (hk : 1 ≤ k) (g : Mat k r) (hg : g ∈ GV k r) :
    Function.Injective (g * frame k r).mulVec := by
  have hH : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have hF : (frame k r)ᴴ * frame k r = 1 := frame_orthonormal k r hk
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) * (g * frame k r) = 1 := by
    calc ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) * (g * frame k r)
        = (frame k r)ᴴ * ((Hpk k r * (gᴴ * Hpk k r * g)) * frame k r) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hH, Matrix.one_mul, hF]
  intro x y hxy
  have := congrArg (fun v => ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) *ᵥ v) hxy
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma gram_pos (k r : ℕ) (hk : 1 ≤ k) (g : Mat k r) (hg : g ∈ GV k r) (a : Fin (r + 1)) :
    0 < gram k r g a := by
  have hP : ((g * frame k r)ᴴ * (g * frame k r)).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ (mulVec_inj k r hk g hg)
  have hS := hP.submatrix (Fin.castLE_injective (Nat.succ_le_of_lt a.isLt))
  have hd := hS.det_pos
  exact (Complex.pos_iff.mp hd).1

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma gram_continuous (k r : ℕ) (a : Fin (r + 1)) : Continuous fun g : Mat k r => gram k r g a := by
  unfold gram
  have h : Continuous fun g : Mat k r => g * frame k r := continuous_id.matrix_mul continuous_const
  exact Complex.continuous_re.comp
    ((h.matrix_conjTranspose.matrix_mul h).matrix_submatrix _ _).matrix_det

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma gram_measurable (k r : ℕ) (a : Fin (r + 1)) :
    Measurable fun x : Mt k r => gram k r (Matrix.of x) a := by
  have h : Continuous fun x : Mt k r => gram k r (Matrix.of x) a := gram_continuous k r a
  exact h.measurable

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem gram_vHalf_pos_measurable_continuousOn : ∀ k r : ℕ, 1 ≤ k → (∀ g ∈ GV k r, ∀ a : Fin (r + 1), 0 < gram k r g a) ∧ (∀ g ∈ GV k r, 0 < vHalf k r g) ∧ (Measurable fun x : Mt k r => vHalf k r (Matrix.of x)) ∧ ContinuousOn (vHalf k r) (GV k r) := by
  intro k r hk
  refine ⟨gram_pos k r hk, fun g hg => ?_, ?_, ?_⟩
  · unfold vHalf
    exact mul_pos (Finset.prod_pos fun a _ => inv_pos.mpr (gram_pos k r hk g hg _))
      (Real.rpow_pos_of_pos (gram_pos k r hk g hg _) _)
  · unfold vHalf
    exact (Finset.measurable_prod _ fun a _ => (gram_measurable k r _).inv).mul
      ((gram_measurable k r _).pow_const _)
  · unfold vHalf
    refine ContinuousOn.mul (continuousOn_finsetProd _ fun a _ => ?_) ?_
    · exact (gram_continuous k r _).continuousOn.inv₀ fun g hg => (gram_pos k r hk g hg _).ne'
    · exact (gram_continuous k r _).continuousOn.rpow_const
        fun g hg => Or.inl (gram_pos k r hk g hg _).ne'

end GlobalTheory.HCXi.GramPos
