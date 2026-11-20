import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules.
-/
theorem lehw_eval_idFrame_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame ℚ r n) (hw ℚ hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  apply Finset.prod_eq_one
  intro s _
  rw [map_pow]
  convert one_pow (M := ℚ) _
  unfold lpMinor
  rw [RingHom.map_det]
  refine (congrArg Matrix.det ?_).trans Matrix.det_one
  ext p q
  simp [idFrame, Matrix.one_apply, Fin.ext_iff]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem fock_space_highest_weight : FockQHW := by
  intro r n hn ν hν F hF
  classical
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F with hGdef
  have hG : G ∈ dualWeyl ℚ r n ν := dualWeylRowGraded ℚ r n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine ℚ r n hn ν hν G hG
    (fun a b hab k hk => lehw_kill hn ν hν G hG hGh a b hab k hk)
  have hHW := hwRowWeight ℚ r n hn ν hν
  have h1 : fockQ (hw ℚ hn ν) F = fockQ (hw ℚ hn ν) G := by
    unfold fockQ
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hm))]
  have h2 : fockQ (hw ℚ hn ν) G = c * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
    rw [hc]
    unfold fockQ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul]
    ring
  have hcolF : IsWeightedHomogeneous (colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  have hcolH : IsWeightedHomogeneous (colW r n) (hw ℚ hn ν) ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp (hwMem ℚ r n hn ν hν)).1
  have hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idFrame ℚ r n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  have eF := lhwline_diag hn ν F hcolF (idFrame ℚ r n) hD
  have eH := lhwline_diag hn ν (hw ℚ hn ν) hcolH (idFrame ℚ r n) hD
  have hev1 := lehw_eval_idFrame_hw hn ν
  have hDmem : lhwline_mnu hn ν ∈ (hw ℚ hn ν).support := by
    rw [mem_support_iff]
    intro h0
    rw [h0, zero_mul, hev1] at eH
    exact one_ne_zero eH
  have hcoef : coeff (lhwline_mnu hn ν) F = c * coeff (lhwline_mnu hn ν) (hw ℚ hn ν) := by
    have e : coeff (lhwline_mnu hn ν) F = coeff (lhwline_mnu hn ν) G := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hDmem))]
    rw [e, hc, coeff_smul, smul_eq_mul]
  have hevF : eval (idFrame ℚ r n) F = c := by
    rw [eF, hcoef, mul_assoc, ← eH, hev1, mul_one]
  rw [h1, h2, hevF]

end Formalism.GradedWeylDivisibility
