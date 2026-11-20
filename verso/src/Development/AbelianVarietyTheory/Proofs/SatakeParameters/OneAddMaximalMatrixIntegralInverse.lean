import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix

namespace GlobalTheory.Hk3

/- English proof (translation)
Set `v : Valuation L (WithZero (Multiplicative ℤ))` to `Valued.v`. Set `O` to `v.valuationSubring`. Set `Y : Matrix (Fin n) (Fin n) O` to `fun i j => ⟨X i j, (hX i j).le⟩`. Establish `hY : ∀ i j, IsLocalRing.residue O (Y i j) = 0` using `fun i j => by`. Rewrite using `[IsLocalRing.residue_eq_zero_iff]`.

Conclude with `(Valuation.mem_maximalIdeal_iff L v).2 (hX i j)`. Establish `h1 : (IsLocalRing.residue O).mapMatrix (1 + Y) = 1`. Rewrite using `[map_add, map_one]`. Establish `: (IsLocalRing.residue O).mapMatrix Y = 0`. Use extensionality with `i j`.

Conclude with `hY i j`. Rewrite using `[this, add_zero]`. Establish `hd : IsUnit (1 + Y).det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1, det_one]`. Conclude with `one_ne_zero`.

Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hd`. Use `⟨Units.map (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _).toMonoidHom u, ?_, ?_⟩` and prove the remaining obligations. Use `show O.subtype.mapMatrix (u : Matrix (Fin n) (Fin n) O) = _`. Rewrite using `[hu, map_add, map_one]`. Both sides reduce to the same expression.

Introduce `i j`. Rewrite using `[← map_inv]`. Conclude with `((u⁻¹ : (Matrix (Fin n) (Fin n) O)ˣ).1 i j).2`.
-/
theorem one_add_maximal_inv_int (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (n : ℕ) (X : Matrix (Fin n) (Fin n) L) (hX : ∀ i j, Valued.v (X i j) < 1) :
    ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧
      ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  classical
  let v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v
  let O := v.valuationSubring
  let Y : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, (hX i j).le⟩
  have hY : ∀ i j, IsLocalRing.residue O (Y i j) = 0 := fun i j => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff L v).2 (hX i j)
  have h1 : (IsLocalRing.residue O).mapMatrix (1 + Y) = 1 := by
    rw [map_add, map_one]
    have : (IsLocalRing.residue O).mapMatrix Y = 0 := by
      ext i j; exact hY i j
    rw [this, add_zero]
  have hd : IsUnit (1 + Y).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1, det_one]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨Units.map (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _).toMonoidHom u, ?_, ?_⟩
  · show O.subtype.mapMatrix (u : Matrix (Fin n) (Fin n) O) = _
    rw [hu, map_add, map_one]
    rfl
  · intro i j
    rw [← map_inv]
    exact ((u⁻¹ : (Matrix (Fin n) (Fin n) O)ˣ).1 i j).2

end GlobalTheory.Hk3
