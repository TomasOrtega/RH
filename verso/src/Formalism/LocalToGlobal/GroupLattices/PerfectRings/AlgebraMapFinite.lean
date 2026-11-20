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
Introduce `q`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Conclude with `⟨⟨r, 0⟩, rfl⟩`.
-/
theorem toRes_surjective : Function.Surjective (toRes π) := by
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨⟨r, 0⟩, rfl⟩

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨c.im, by simp⟩`. Introduce and unpack `⟨d, hd⟩`.

Use `⟨⟨z.im, d⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [hd]`.
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
Use extensionality with `z`. Rewrite using `[RingHom.mem_ker, toRes_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, mem_span_om]`.
-/
theorem ker_toRes : RingHom.ker (toRes π) = Ideal.span {(ω : QuadraticAlgebra R π 0)} := by
  ext z
  rw [RingHom.mem_ker, toRes_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    mem_span_om]

def resEquiv : (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) ≃+* (R ⧸ Ideal.span {π}) :=
  (Ideal.quotEquivOfEq (ker_toRes π).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toRes_surjective π))

/- English proof (translation)
The claim follows from `Nat.card_congr (resEquiv π).toEquiv`.
-/
theorem card_res :
    Nat.card (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) =
      Nat.card (R ⧸ Ideal.span {π}) :=
  Nat.card_congr (resEquiv π).toEquiv

/- English proof (translation)
Rewrite using `[RingHom.finite_algebraMap]`. Use `infer_instance`.
-/
theorem algebraMap_finite : (algebraMap R (QuadraticAlgebra R π 0)).Finite := by
  rw [RingHom.finite_algebraMap]
  infer_instance

/- English proof (translation)
Introduce `x y h`. Simplify `congrArg QuadraticAlgebra.re h` using `[Algebra.algebraMap_eq_smul_one]`.
-/
theorem algebraMap_injective : Function.Injective (algebraMap R (QuadraticAlgebra R π 0)) := by
  intro x y h
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg QuadraticAlgebra.re h

end Formalism.L2.G.Quad
