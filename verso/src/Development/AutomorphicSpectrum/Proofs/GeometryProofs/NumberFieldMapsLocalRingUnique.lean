import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo.TwoMaps

open Polynomial

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem ringHom_eq_of_comp_eq (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B]
    [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B)
    (h : π.comp s = π.comp t) : s = t := by
  refine RingHom.ext fun a => ?_
  have hsep : (minpoly ℚ a).Separable := Algebra.IsSeparable.isSeparable ℚ a
  obtain ⟨p, hp⟩ : ∃ p : K[X], p = (minpoly ℚ a).map (algebraMap ℚ K) := ⟨_, rfl⟩
  have hpa : p.eval a = 0 := by
    rw [hp, eval_map_algebraMap]
    exact minpoly.aeval ℚ a
  have hpd : p.derivative.eval a ≠ 0 := by
    rw [hp, derivative_map, eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ a)
  have hst : p.map s = p.map t := by
    rw [hp, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hx : (p.map s).eval (s a) = 0 := by
    rw [eval_map, eval₂_at_apply, hpa, map_zero]
  have hy : (p.map s).eval (t a) = 0 := by
    rw [hst, eval_map, eval₂_at_apply, hpa, map_zero]
  have hdx : (p.map s).derivative.eval (s a) = s (p.derivative.eval a) := by
    rw [derivative_map, eval_map, eval₂_at_apply]
  have hunit : IsUnit ((p.map s).derivative.eval (s a)) := by
    rw [hdx]
    exact (IsUnit.mk0 _ hpd).map s
  obtain ⟨k, hk⟩ := binomExpansion (p.map s) (s a) (t a - s a)
  have hd : ¬ IsUnit (t a - s a) := by
    intro hu
    have h0 : π (t a - s a) = 0 := by
      have := RingHom.congr_fun h a
      simp only [RingHom.comp_apply] at this
      rw [map_sub, this, sub_self]
    exact (hu.map π).ne_zero h0
  have hkd : ¬ IsUnit (-(k * (t a - s a))) := by
    rw [IsUnit.neg_iff]
    exact fun hu => hd (isUnit_of_mul_isUnit_right hu)
  have hu2 : IsUnit ((p.map s).derivative.eval (s a) + k * (t a - s a)) := by
    by_contra hc
    have hsum := IsLocalRing.nonunits_add (R := B) (a := (p.map s).derivative.eval (s a) + k * (t a - s a))
      (b := -(k * (t a - s a))) hc hkd
    apply hsum
    simpa using hunit
  have hmul : (t a - s a) * ((p.map s).derivative.eval (s a) + k * (t a - s a)) = 0 := by
    have e : s a + (t a - s a) = t a := by ring
    rw [e, hy, hx] at hk
    linear_combination -hk
  have hz : t a - s a = 0 := by
    simpa using (hu2.mul_left_eq_zero).1 hmul
  exact (sub_eq_zero.1 hz).symm

end GlobalTheory.CompanionTheory.Ggeo.TwoMaps
