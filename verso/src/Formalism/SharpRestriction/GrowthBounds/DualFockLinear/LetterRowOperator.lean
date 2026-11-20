import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FRSmulRight

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

def letterRowOperator (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)) : Module.End K (VV K m d) :=
  if vec then Ed K (m + 1) d a b else (if a = b then (d : K) • (1 : Module.End K (VV K m d)) else 0) - Ed K (m + 1) d b a

/- English proof (translation)
Establish `h` using `hT K m vec d a b P.1 ((mem_Hd_iff _).2 P.2)`. Use `show theta K m vec ((letterRowOperator K m vec d a b P : VV K m d) : MvPolynomial (Fin (m + 1)) K) = RE K (m + 1) a b (theta K m vec P.1)`. Rewrite using `[h]`. Use `congr 1`. Unfold `letterRowOperator TE`.

Consider the cases of `vec`. Distinguish the cases in `hab : a = b`. Simplify using `[hab, Ed]`. Simplify using `[hab, Ed]`. Simplify using `[Ed]`.
-/
theorem letter_operator_matches_row_operator (hT : RestTheta) (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)) (P : VV K m d) :
    thV K m vec d (letterRowOperator K m vec d a b P) = RE K (m + 1) a b (thV K m vec d P) := by
  have h := hT K m vec d a b P.1 ((mem_Hd_iff _).2 P.2)
  show theta K m vec ((letterRowOperator K m vec d a b P : VV K m d) : MvPolynomial (Fin (m + 1)) K) = RE K (m + 1) a b (theta K m vec P.1)
  rw [h]
  congr 1
  unfold letterRowOperator TE
  cases vec
  · by_cases hab : a = b
    · simp [hab, Ed]
    · simp [hab, Ed]
  · simp [Ed]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `P`. Rewrite using `[← sub_eq_zero]`. Apply `uniqV hR hm vec d` to reduce the goal to its premises. Introduce `Q`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, fR_sub_left, hA]`. Rewrite using `[letter_operator_matches_row_operator hT, hAdj, ← letter_operator_matches_row_operator hT, hA, letter_operator_matches_row_operator hT, letter_operator_matches_row_operator hT]`. Establish `e1 : RE K (m + 1) b a (thV K m vec d Q) * β = RE K (m + 1) b a (thV K m vec d Q * β) - thV K m vec d Q * RE K (m + 1) b a β`. Rewrite using `[RE_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, fR_sub_right, ← hAdj, RE_mul, fR_add_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comm_A (hAdj : RestAdj) (hT : RestTheta) (hR : RestRep) {K : Type} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m)
    (vec : Bool) (d : ℕ)
    (A : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → Module.End K (VV K m d))
    (hA : ∀ β s P Q, fockR (thV K m vec d (A β s P)) (thV K m vec d Q) = fockR (thV K m vec d P * s) (thV K m vec d Q * β))
    (a b : Fin (m + 1)) (β s : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    letterRowOperator K m vec d a b * A β s - A β s * letterRowOperator K m vec d a b = A β (RE K (m + 1) a b s) - A (RE K (m + 1) b a β) s := by
  apply LinearMap.ext
  intro P
  rw [← sub_eq_zero]
  apply uniqV hR hm vec d
  intro Q
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, fR_sub_left, hA]
  rw [letter_operator_matches_row_operator hT, hAdj, ← letter_operator_matches_row_operator hT, hA, letter_operator_matches_row_operator hT, letter_operator_matches_row_operator hT]
  have e1 : RE K (m + 1) b a (thV K m vec d Q) * β =
      RE K (m + 1) b a (thV K m vec d Q * β) - thV K m vec d Q * RE K (m + 1) b a β := by
    rw [RE_mul]; ring
  rw [e1, fR_sub_right, ← hAdj, RE_mul, fR_add_left]
  ring

end Formalism.MainNotions.TestSideCounting
