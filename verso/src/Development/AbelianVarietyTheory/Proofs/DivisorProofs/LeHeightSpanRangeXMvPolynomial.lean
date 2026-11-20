import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `[RingHom.mem_ker]`. Introduce `p hp`.

Rewrite `hp` using `[RingHom.mem_ker]`. Establish `key : ∀ q : MvPolynomial (Fin n) k, q - MvPolynomial.C (MvPolynomial.constantCoeff q) ∈ Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))`. Introduce `q`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp`.

Consider the case `add p q hp hq`. Use `Ideal.add_mem _ hp hq` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `mul_X p i _`. Simplify using `only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`. Simplify `key p` using `[hp]`.
-/
theorem span_range_X_eq_ker_constantCoeff (k : Type) [Field k] (n : ℕ) :
    Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))
      = RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have key : ∀ q : MvPolynomial (Fin n) k, q - MvPolynomial.C (MvPolynomial.constantCoeff q) ∈
        Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k))) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
        have := Ideal.add_mem _ hp hq
        convert this using 1
        simp only [map_add]; ring
      | mul_X p i _ =>
        simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    simpa [hp] using key p

/- English proof (translation)
Introduce `k _ n`. Rewrite using `[span_range_X_eq_ker_constantCoeff]`. Use `haveI : (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by simp⟩)`. Establish `h` using `ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k))`. Conclude with `h.2.ge`.
-/
theorem le_height_span_range_X_mvPolynomial : ∀ (k : Type) [Field k] (n : ℕ), ((n : ℕ∞)) ≤ (Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))).height := by
  intro k _ n
  rw [span_range_X_eq_ker_constantCoeff]
  haveI : (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by simp⟩)
  have h := ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k))
  exact h.2.ge

end GlobalTheory
