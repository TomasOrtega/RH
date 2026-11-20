import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial Filter

noncomputable section

/- English proof (translation)
Use `conv_lhs => rw [p.as_sum, map_sum]`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[bind₁_monomial]`. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[totalDegree_C, zero_add]`.

Use `(totalDegree_finsetProd _ _).trans ?_` and prove the remaining obligations. Use `le_trans ?_ (le_totalDegree hs)` and prove the remaining obligations. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `(totalDegree_pow _ _).trans ?_` and prove the remaining obligations. Simplify using `using Nat.mul_le_mul_left (s i) (hf i)`.
-/
theorem totalDegree_bind₁_le_of_le_one {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

/- English proof (translation)
Introduce `K _ h p c hp`. Use `⟨bind₁ (fun k => X k - C (c k : ℚ)) p, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `ht : Tendsto (fun m : K → ℤ => m + -c) atTop atTop` using `tendsto_atTop_add_const_right atTop (-c) tendsto_id`. Use `(ht.eventually hp).mono fun m hm => ?_` and prove the remaining obligations. Simplify using `only [← sub_eq_add_neg] at hm`.

Establish `e` using `eval₂Hom_bind₁ (RingHom.id ℚ) (fun k => (m k : ℚ)) (fun k => X k - C (c k : ℚ)) p`. Rewrite using `[hm]`. Use `Eq.trans ?_ e.symm` and prove the remaining obligations. Use `show eval _ p = eval _ p`. Use `congrArg (fun x => eval x p) (funext fun k => ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Conclude with `totalDegree_bind₁_le_of_le_one _ (fun k => (totalDegree_sub_C_le _ _).trans (totalDegree_X k).le) p`. Introduce and unpack `rfl`. Conclude with `map_zero _`.
-/
theorem EventuallyPolyShift.proof : EventuallyPolyShift.Statement := by
  intro K _ h p c hp
  refine ⟨bind₁ (fun k => X k - C (c k : ℚ)) p, ?_, ?_, ?_⟩
  · have ht : Tendsto (fun m : K → ℤ => m + -c) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-c) tendsto_id
    refine (ht.eventually hp).mono fun m hm => ?_
    simp only [← sub_eq_add_neg] at hm
    have e := eval₂Hom_bind₁ (RingHom.id ℚ) (fun k => (m k : ℚ)) (fun k => X k - C (c k : ℚ)) p
    rw [hm]
    refine Eq.trans ?_ e.symm
    show eval _ p = eval _ p
    refine congrArg (fun x => eval x p) (funext fun k => ?_)
    simp
  · exact totalDegree_bind₁_le_of_le_one _
      (fun k => (totalDegree_sub_C_le _ _).trans (totalDegree_X k).le) p
  · rintro rfl
    exact map_zero _

end

end GroundTheory.Heights₂.Heights.FieldNumbers
