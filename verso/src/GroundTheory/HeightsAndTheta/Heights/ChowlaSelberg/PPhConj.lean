import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem mem_conjLattice_iff (Λ : Submodule ℤ ℂ) (z : ℂ) : z ∈ conjLattice Λ ↔ conj z ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨conj z, h, by simp⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
theorem eisensteinSum_conjLattice (Λ : Submodule ℤ ℂ) (n : ℕ) :
    eisensteinSum (conjLattice Λ) n = conj (eisensteinSum Λ n) := by
  unfold eisensteinSum
  let e : Λ ≃ conjLattice Λ :=
    (Submodule.equivMapOfInjective _ (star_injective (R := ℂ)) Λ).toEquiv
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext l
  change ((conj (l : ℂ)) ^ n)⁻¹ = conj (((l : ℂ) ^ n)⁻¹)
  simp [map_inv₀, map_pow]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem latticeDiscr_conjLattice (Λ : Submodule ℤ ℂ) :
    latticeDiscr (conjLattice Λ) = conj (latticeDiscr Λ) := by
  simp [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_conjLattice, map_sub, map_mul, map_pow, map_ofNat]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem conjLattice_eq_comap (Λ : Submodule ℤ ℂ) :
    conjLattice Λ =
      ZLattice.comap ℝ Λ Complex.conjLIE.toLinearEquiv.toLinearMap := by
  ext z
  rw [mem_conjLattice_iff]
  exact Iff.rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem latticeArea_conjLattice (L : PeriodPair) :
    latticeArea (conjLattice L.lattice) = latticeArea L.lattice := by
  unfold latticeArea
  rw [conjLattice_eq_comap]
  exact ZLattice.covolume_comap L.lattice volume volume
    (e := Complex.conjLIE.toContinuousLinearEquiv) Complex.conjLIE.measurePreserving

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem PhConj.proof : PhConj.Statement := by
  intro L
  unfold logPeriod
  rw [latticeArea_conjLattice, latticeDiscr_conjLattice, Complex.norm_conj]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
