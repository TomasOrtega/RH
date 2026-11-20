import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSpecFirst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [specRest, specFirst]`. Consider the case `add p q hp hq`. Simplify using `only [specRest, specFirst, eval₂_add, map_add] at hp hq ⊢`. Rewrite using `[hp, hq]`.

Consider the case `mul_X p ij hp`. Simplify using `only [specRest, specFirst, eval₂_mul, eval₂_X, map_mul, bind₁_X_right] at hp ⊢`. Rewrite using `[hp]`. Use `congr 1`. Take `⟨i, j⟩` from `ij`.

Apply the tactic sequence `cases i using Fin.cases <;> simp [specFirstVar]`.
-/
theorem eval_specRest {k E : Type*} [CommRing k] [CommRing E] (φ : k →+* E) {n e : ℕ}
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (u : Fin n → k) :
    eval (fun j => φ (u j)) (specRest φ g y) =
      eval₂ φ (fun ij : Fin e × Fin n => y (.inl ij)) (specFirst g u) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [specRest, specFirst]
  | add p q hp hq =>
    simp only [specRest, specFirst, eval₂_add, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p ij hp =>
    simp only [specRest, specFirst, eval₂_mul, eval₂_X, map_mul, bind₁_X_right] at hp ⊢
    rw [hp]
    congr 1
    obtain ⟨i, j⟩ := ij
    cases i using Fin.cases <;> simp [specFirstVar]

/- English proof (translation)
Introduce `k E _ _ _ _ n e Q g y u hy hQ hg hu`. Use `set QE := Q.map (MvPolynomial.map (algebraMap k E)) with hQE`. Take `⟨hfin, c, _, hcg⟩` from `h1 k E n e Q g y hy hQ hg`. Establish `hy' : AlgebraicIndependent k (fun ij : Fin e × Fin n => y (.inl ij))` using `hy.comp _ Sum.inl_injective`. Establish `hne : eval (fun j => algebraMap k E (u j)) (specRest (algebraMap k E) g y) ≠ 0`.

Rewrite using `[eval_specRest]`. Conclude with `fun h0 => h3 k n e Q g u hQ hg hu (hy'.eq_zero_of_aeval_eq_zero _ (by rw [aeval_def]; exact h0))`. Establish `hsum : (∑ j, algebraMap E (SecAlg QE y) (algebraMap k E (u j)) * secCoord QE y j) = secLin QE y (fun j => algebraMap k E (u j))`. Simplify using `only [secLin, linForm, map_sum, map_mul]`. Both sides reduce to the same expression.

Establish `hnorm : Algebra.norm E (secLin QE y (fun j => algebraMap k E (u j))) ≠ 0`. Establish `h` using `h2 E (SecAlg QE y) n (secCoord QE y) (fun j => algebraMap k E (u j))`. Rewrite `h` using `[hsum]`. Rewrite `hne` using `[hcg, eval_mul, eval_C, h]`. Conclude with `right_ne_zero_of_mul hne`.

Establish `hunit : IsUnit (Algebra.lmul E (SecAlg QE y) (secLin QE y fun j => algebraMap k E (u j)))`. Rewrite using `[LinearMap.isUnit_iff_isUnit_det]`. Conclude with `isUnit_iff_ne_zero.mpr hnorm`. Take `⟨z, hz⟩` from `((Module.End.isUnit_iff _).mp hunit).2 1`. Establish `hz' : secLin QE y (fun j => algebraMap k E (u j)) * z = 1`.

Simplify using `using hz`. Conclude with `(isUnit_iff_exists_inv.mpr ⟨z, hz'⟩).mem_nonZeroDivisors`.
-/
theorem SecLinNZD.proof (h1 : ChowNormForm.Statement) (h2 : NormFormEval.Statement)
    (h3 : SpecFirstNeField.Statement) : SecLinNZD.Statement := by
  intro k E _ _ _ _ n e Q g y u hy hQ hg hu
  set QE := Q.map (MvPolynomial.map (algebraMap k E)) with hQE
  obtain ⟨hfin, c, _, hcg⟩ := h1 k E n e Q g y hy hQ hg
  have hy' : AlgebraicIndependent k (fun ij : Fin e × Fin n => y (.inl ij)) :=
    hy.comp _ Sum.inl_injective
  have hne : eval (fun j => algebraMap k E (u j)) (specRest (algebraMap k E) g y) ≠ 0 := by
    rw [eval_specRest]
    exact fun h0 => h3 k n e Q g u hQ hg hu
      (hy'.eq_zero_of_aeval_eq_zero _ (by rw [aeval_def]; exact h0))
  have hsum : (∑ j, algebraMap E (SecAlg QE y) (algebraMap k E (u j)) * secCoord QE y j) =
      secLin QE y (fun j => algebraMap k E (u j)) := by
    simp only [secLin, linForm, map_sum, map_mul]
    rfl
  have hnorm : Algebra.norm E (secLin QE y (fun j => algebraMap k E (u j))) ≠ 0 := by
    have h := h2 E (SecAlg QE y) n (secCoord QE y) (fun j => algebraMap k E (u j))
    rw [hsum] at h
    rw [hcg, eval_mul, eval_C, h] at hne
    exact right_ne_zero_of_mul hne
  have hunit : IsUnit (Algebra.lmul E (SecAlg QE y) (secLin QE y fun j => algebraMap k E (u j))) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hnorm
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp hunit).2 1
  have hz' : secLin QE y (fun j => algebraMap k E (u j)) * z = 1 := by
    simpa using hz
  exact (isUnit_iff_exists_inv.mpr ⟨z, hz'⟩).mem_nonZeroDivisors

end

end GroundTheory.Heights₂.Heights.Vertical
