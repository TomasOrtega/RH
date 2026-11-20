import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DetEqMulMinorOfColZero

noncomputable section

set_option linter.unusedSimpArgs false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section grp
variable (k r' : ℕ)

/- English proof (translation)
Establish `key : ∀ q : Fin (2 * (1 + r') + k + 1), A *ᵥ Pi.single q 1 = B *ᵥ Pi.single q 1`. Introduce `q`. Distinguish the cases in `hq0 : q.val = 0`. Establish `he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = e0 k r'`. Establish `hq : q = eI k (1 + r') (a0 r')` using `Fin.ext (by simp [eI, a0, hq0])`.

Rewrite using `[hq]`. Both sides reduce to the same expression. Rewrite using `[he, h0]`. Distinguish the cases in `hql : q.val = 2 * (1 + r') + k`. Establish `he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = es0 k r'`.

Establish `hq : q = esI k (1 + r') (a0 r')` using `Fin.ext (by simp [esI, a0, hql])`. Rewrite using `[hq]`. Both sides reduce to the same expression. Rewrite using `[he, h1]`. Establish `he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = liftVec k 1 r' (Pi.single ⟨q.val - 1, by omega⟩ 1)`.

Use function extensionality and compare the values at `p`. Simplify using `only [liftVec, Pi.single_apply, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[he, h2]`. Use extensionality with `p q`.

Establish `h` using `congrFun (key q) p`. Simplify `h` using `[Matrix.mulVec_single_one, Matrix.transpose_apply]`.
-/
theorem mat_ext_lev {A B : Mat k (1 + r')} (h0 : A *ᵥ e0 k r' = B *ᵥ e0 k r')
    (h1 : A *ᵥ es0 k r' = B *ᵥ es0 k r') (h2 : ∀ v, A *ᵥ liftVec k 1 r' v = B *ᵥ liftVec k 1 r' v) : A = B := by
  have key : ∀ q : Fin (2 * (1 + r') + k + 1), A *ᵥ Pi.single q 1 = B *ᵥ Pi.single q 1 := by
    intro q
    by_cases hq0 : q.val = 0
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = e0 k r' := by
        have hq : q = eI k (1 + r') (a0 r') := Fin.ext (by simp [eI, a0, hq0])
        rw [hq]
        rfl
      rw [he, h0]
    by_cases hql : q.val = 2 * (1 + r') + k
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = es0 k r' := by
        have hq : q = esI k (1 + r') (a0 r') := Fin.ext (by simp [esI, a0, hql])
        rw [hq]
        rfl
      rw [he, h1]
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) =
          liftVec k 1 r' (Pi.single ⟨q.val - 1, by omega⟩ 1) := by
        funext p
        simp only [liftVec, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [he, h2]
  ext p q
  have h := congrFun (key q) p
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h

/- English proof (translation)
Apply `mat_ext_lev` to reduce the goal to its premises. Simplify using `only [← Matrix.mulVec_mulVec, levi_fixes_base_vector]`. Simplify using `only [← Matrix.mulVec_mulVec, levi_fixes_last_basis]`. Introduce `v`. Simplify using `only [← Matrix.mulVec_mulVec, lev_lift]`.
-/
theorem lev_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift]

/- English proof (translation)
Apply `mat_ext_lev` to reduce the goal to its premises. Simplify using `only [levi_fixes_base_vector, Matrix.one_mulVec]`. Simplify using `only [levi_fixes_last_basis, Matrix.one_mulVec]`. Introduce `v`. Simplify using `only [lev_lift, Matrix.one_mulVec]`.
-/
theorem lev_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_lev
  · simp only [levi_fixes_base_vector, Matrix.one_mulVec]
  · simp only [levi_fixes_last_basis, Matrix.one_mulVec]
  · intro v
    simp only [lev_lift, Matrix.one_mulVec]

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [Matrix.conjTranspose_apply, ιLev]`. Apply the tactic sequence `split_ifs <;> (try subst_vars) <;> simp_all [Matrix.conjTranspose_apply]`.
-/
theorem lev_conjT (g : Mat k r') : (ιLev k 1 r' g)ᴴ = ιLev k 1 r' gᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, ιLev]
  split_ifs <;> (try subst_vars) <;> simp_all [Matrix.conjTranspose_apply]

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r' * g = Hpk k r'` using `hg`. Use `show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r')`. Rewrite using `[lev_conjT]`. Apply `mat_ext_lev` to reduce the goal to its premises. Simplify using `only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, Hpk_mulVec_e0, levi_fixes_last_basis]`.

Simplify using `only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, hermMatrix_last_basis, levi_fixes_base_vector]`. Introduce `v`. Simplify using `only [← Matrix.mulVec_mulVec, lev_lift, Hpk_lift]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']`.
-/
theorem lev_mem {g : Mat k r'} (hg : g ∈ GV k r') : ιLev k 1 r' g ∈ GV k (1 + r') := by
  have hg' : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r')
  rw [lev_conjT]
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, Hpk_mulVec_e0, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, hermMatrix_last_basis, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, Hpk_lift]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

/- English proof (translation)
Apply `mat_ext_lev` to reduce the goal to its premises. Simplify using `only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, long_weyl_sends_base_to_dual, Matrix.mulVec_smul, levi_fixes_last_basis]`. Simplify using `only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, rankOneMatrix_last_basis, Matrix.mulVec_smul, levi_fixes_base_vector]`. Introduce `v`. Simplify using `only [← Matrix.mulVec_mulVec, lev_lift, rankOneMatrix_lift]`.
-/
theorem rankOne_levi_comm (c : ℂ) (g : Mat k r') : w0 k r' c * ιLev k 1 r' g = ιLev k 1 r' g * w0 k r' c := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, long_weyl_sends_base_to_dual, Matrix.mulVec_smul, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, rankOneMatrix_last_basis, Matrix.mulVec_smul, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, rankOneMatrix_lift]

/- English proof (translation)
Use `⟨lev_mem k r' hκ.1, ?_⟩` and prove the remaining obligations. Rewrite using `[lev_conjT, ← lev_mul, hκ.2, lev_one]`.
-/
theorem lev_K {κ : Mat k r'} (hκ : κ ∈ Kset k r') : ιLev k 1 r' κ ∈ Kset k (1 + r') := by
  refine ⟨lev_mem k r' hκ.1, ?_⟩
  rw [lev_conjT, ← lev_mul, hκ.2, lev_one]

end grp

section gn
variable {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.trace]`. Simplify using `only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Use `push_cast`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression.
-/
theorem normSq_sum_eq_trace (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/- English proof (translation)
Unfold `gN`. Use `congr 1`. Establish `h1` using `normSq_sum_eq_trace (κ * X)`. Establish `h2` using `normSq_sum_eq_trace X`. Rewrite `h1` using `[Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]`.

Conclude with `h1.trans h2.symm` after adjusting the coercions.
-/
theorem gN_unitary (k r : ℕ) {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  have h1 := normSq_sum_eq_trace (κ * X)
  have h2 := normSq_sum_eq_trace X
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul] at h1
  exact_mod_cast h1.trans h2.symm

/- English proof (translation)
Unfold `gN`. Conclude with `Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))`.
-/
theorem gN_cont (k r : ℕ) : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _
    fun j _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

end gn

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
