import Mathlib
import Formalism.PeriodIntegrals.LocalEnd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.ValSurjective

open NumberField IsDedekindDomain

namespace PI.LocalEndW

/- English proof (translation)
Establish `hV : ValPreserved` using `hB2 (hB1 hA)`. Introduce `F _ _ v τ`. Establish `hτv : ∀ x, Valued.v (τ x) = Valued.v x` using `hV F v τ`. Establish `hsurj` using `hC2 F v τ hτv`. Set `e` to `RingEquiv.ofBijective τ ⟨τ.injective, hsurj⟩`.

Use `⟨hC1 F v τ hτv, e.symm.toRingHom, ?_, fun a => e.apply_symm_apply a⟩` and prove the remaining obligations. Apply `hC1 F v` to reduce the goal to its premises. Introduce `x`. Use `hτv (e.symm x)` as an intermediate fact. Rewrite `this` using `[show τ (e.symm x) = x from e.apply_symm_apply x]`.

Conclude with `this.symm`.
-/
theorem localEndHomeo_of (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt)
    (hC1 : ValContinuous) (hC2 : ValSurjective) : PI.LocalEndHomeo := by
  have hV : ValPreserved := hB2 (hB1 hA)
  intro F _ _ v τ
  have hτv : ∀ x, Valued.v (τ x) = Valued.v x := hV F v τ
  have hsurj := hC2 F v τ hτv
  let e := RingEquiv.ofBijective τ ⟨τ.injective, hsurj⟩
  refine ⟨hC1 F v τ hτv, e.symm.toRingHom, ?_, fun a => e.apply_symm_apply a⟩
  apply hC1 F v
  intro x
  have := hτv (e.symm x)
  rw [show τ (e.symm x) = x from e.apply_symm_apply x] at this
  exact this.symm

end PI.LocalEndW
