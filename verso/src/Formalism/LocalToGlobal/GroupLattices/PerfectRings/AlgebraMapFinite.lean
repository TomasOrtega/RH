import Formalism.LocalRingCardinality.SpanPowerMembership.GatRing

noncomputable section

namespace Formalism.L2.G.Quad

open QuadraticAlgebra

variable {R : Type} [CommRing R] (π : R)

def toRes : QuadraticAlgebra R π 0 →+* R ⧸ Ideal.span {π} where
  toFun z := Ideal.Quotient.mk _ z.re
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    have h : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
    simp [h]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toRes_apply (z : QuadraticAlgebra R π 0) : toRes π z = Ideal.Quotient.mk _ z.re := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem toRes_surjective : Function.Surjective (toRes π) := by
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨⟨r, 0⟩, rfl⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem mem_span_om (z : QuadraticAlgebra R π 0) :
    z ∈ Ideal.span {(ω : QuadraticAlgebra R π 0)} ↔ π ∣ z.re := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.im, by simp⟩
  · rintro ⟨d, hd⟩
    refine ⟨⟨z.im, d⟩, ?_⟩
    ext <;> simp [hd]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem ker_toRes : RingHom.ker (toRes π) = Ideal.span {(ω : QuadraticAlgebra R π 0)} := by
  ext z
  rw [RingHom.mem_ker, toRes_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    mem_span_om]

def resEquiv : (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) ≃+* (R ⧸ Ideal.span {π}) :=
  (Ideal.quotEquivOfEq (ker_toRes π).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toRes_surjective π))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem card_res :
    Nat.card (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) =
      Nat.card (R ⧸ Ideal.span {π}) :=
  Nat.card_congr (resEquiv π).toEquiv

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem algebraMap_finite : (algebraMap R (QuadraticAlgebra R π 0)).Finite := by
  rw [RingHom.finite_algebraMap]
  infer_instance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.
-/
theorem algebraMap_injective : Function.Injective (algebraMap R (QuadraticAlgebra R π 0)) := by
  intro x y h
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg QuadraticAlgebra.re h

end Formalism.L2.G.Quad
