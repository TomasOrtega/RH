import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Simplify using `using hw`. Introduce `h`. Conclude with `⟨conj z, h, by simp⟩`.
-/
theorem mem_conjLattice_iff (Λ : Submodule ℤ ℂ) (z : ℂ) : z ∈ conjLattice Λ ↔ conj z ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨conj z, h, by simp⟩

/- English proof (translation)
Unfold `eisensteinSum`. Set `e : Λ ≃ conjLattice Λ` to `(Submodule.equivMapOfInjective _ (star_injective (R := ℂ)) Λ).toEquiv`. Rewrite using `[← e.tsum_eq, Complex.conj_tsum]`. Use `congr 1`. Use extensionality with `l`.

Express the relevant statement in the definitionally equal form `((conj (l : ℂ)) ^ n)⁻¹ = conj (((l : ℂ) ^ n)⁻¹)`. Simplify using `[map_inv₀, map_pow]`.
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
Simplify using `[latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_conjLattice, map_sub, map_mul, map_pow, map_ofNat]`.
-/
theorem latticeDiscr_conjLattice (Λ : Submodule ℤ ℂ) :
    latticeDiscr (conjLattice Λ) = conj (latticeDiscr Λ) := by
  simp [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_conjLattice, map_sub, map_mul, map_pow, map_ofNat]

/- English proof (translation)
Use extensionality with `z`. Rewrite using `[mem_conjLattice_iff]`. Conclude with `Iff.rfl`.
-/
theorem conjLattice_eq_comap (Λ : Submodule ℤ ℂ) :
    conjLattice Λ =
      ZLattice.comap ℝ Λ Complex.conjLIE.toLinearEquiv.toLinearMap := by
  ext z
  rw [mem_conjLattice_iff]
  exact Iff.rfl

/- English proof (translation)
Unfold `latticeArea`. Rewrite using `[conjLattice_eq_comap]`. Conclude with `ZLattice.covolume_comap L.lattice volume volume (e := Complex.conjLIE.toContinuousLinearEquiv) Complex.conjLIE.measurePreserving`.
-/
theorem latticeArea_conjLattice (L : PeriodPair) :
    latticeArea (conjLattice L.lattice) = latticeArea L.lattice := by
  unfold latticeArea
  rw [conjLattice_eq_comap]
  exact ZLattice.covolume_comap L.lattice volume volume
    (e := Complex.conjLIE.toContinuousLinearEquiv) Complex.conjLIE.measurePreserving

/- English proof (translation)
Introduce `L`. Unfold `logPeriod`. Rewrite using `[latticeArea_conjLattice, latticeDiscr_conjLattice, Complex.norm_conj]`.
-/
theorem PhConj.proof : PhConj.Statement := by
  intro L
  unfold logPeriod
  rw [latticeArea_conjLattice, latticeDiscr_conjLattice, Complex.norm_conj]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
