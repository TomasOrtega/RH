import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Unfold `hw`. Rewrite using `[map_prod]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[map_pow]`.

Use `one_pow (M := ℚ) _` and compare the differences between its conclusion and the goal. Unfold `lpMinor`. Rewrite using `[RingHom.map_det]`. Use `(congrArg Matrix.det ?_).trans Matrix.det_one` and prove the remaining obligations. Use extensionality with `p q`.

Simplify using `[idFrame, Matrix.one_apply, Fin.ext_iff]`.
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
Introduce `r n hn ν hν F hF`. Use `set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F with hGdef`. Establish `hG : G ∈ dualWeyl ℚ r n ν` using `dualWeylRowGraded ℚ r n ν _ F hF`. Establish `hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r` using `r) ν) := weightedHomogeneousComponent_isWeightedHomogeneous _ _`. Take `⟨c, hc⟩` from `hwLine ℚ r n hn ν hν G hG (fun a b hab k hk => lehw_kill hn ν hν G hG hGh a b hab k hk)`.

Establish `hHW` using `hwRowWeight ℚ r n hn ν hν`. Establish `h1 : fockQ (hw ℚ hn ν) F = fockQ (hw ℚ hn ν) G`. Unfold `fockQ`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hm))]`.

Establish `h2 : fockQ (hw ℚ hn ν) G = c * fockQ (hw ℚ hn ν) (hw ℚ hn ν)`. Rewrite using `[hc]`. Unfold `fockQ`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcolF : IsWeightedHomogeneous (colW r n) F ν` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1`. Establish `hcolH : IsWeightedHomogeneous (colW r n) (hw ℚ hn ν) ν` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp (hwMem ℚ r n hn ν hν)).1`. Establish `hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idFrame ℚ r n (a, j) = 0`.

Introduce `a j h`. Simplify using `[idFrame, h]`. Establish `eF` using `lhwline_diag hn ν F hcolF (idFrame ℚ r n) hD`. Establish `eH` using `lhwline_diag hn ν (hw ℚ hn ν) hcolH (idFrame ℚ r n) hD`. Establish `hev1` using `lehw_eval_idFrame_hw hn ν`.

Establish `hDmem : lhwline_mnu hn ν ∈ (hw ℚ hn ν).support`. Rewrite using `[mem_support_iff]`. Introduce `h0`. Rewrite `eH` using `[h0, zero_mul, hev1]`. Conclude with `one_ne_zero eH`.

Establish `hcoef : coeff (lhwline_mnu hn ν) F = c * coeff (lhwline_mnu hn ν) (hw ℚ hn ν)`. Establish `e : coeff (lhwline_mnu hn ν) F = coeff (lhwline_mnu hn ν) G`. Rewrite using `[hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hDmem))]`. Rewrite using `[e, hc, coeff_smul, smul_eq_mul]`. Establish `hevF : eval (idFrame ℚ r n) F = c`.

Rewrite using `[eF, hcoef, mul_assoc, ← eH, hev1, mul_one]`. Rewrite using `[h1, h2, hevF]`.
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
