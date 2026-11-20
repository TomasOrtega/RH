import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.EntIntegral

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem conj_sub_one (g u : GL (Fin n) k) : (g⁻¹ * u * g).val - 1 = g⁻¹.val * (u.val - 1) * g.val := by
  simp only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem mem_stab_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (c : Matrix (Fin n) (Fin n) k)
    (p : Sp k n) (u : GL (Fin n) k) (hcu : u.val * c = c * u.val) (hu : u.val - 1 ∈ Bz Z) :
    u ∈ stab Z p ↔ u.val - 1 ∈ cS Z (p.1 - c) p.2 := by
  have e : (u.val - 1) * (p.1 - c) - (p.1 - c) * (u.val - 1) =
      (u.val * p.1 - p.1 * u.val) - (u.val * c - c * u.val) := by noncomm_ring
  rw [hcu, sub_self, sub_zero] at e
  have e1 : (u.val - 1) * (p.1 - c) = (p.1 - c) * (u.val - 1) ↔ u.val * p.1 = p.1 * u.val := by
    rw [← sub_eq_zero, e, sub_eq_zero]
  have e2 : u.val * p.1 * u⁻¹.val = p.1 ↔ u.val * p.1 = p.1 * u.val := by
    constructor
    · intro h
      calc u.val * p.1 = u.val * p.1 * u⁻¹.val * u.val := by simp [mul_assoc]
        _ = p.1 * u.val := by rw [h]
    · intro h
      rw [h, mul_assoc, Units.mul_inv, mul_one]
  have e3 : u.val *ᵥ p.2 = p.2 ↔ (u.val - 1) *ᵥ p.2 = 0 := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero]
  show (u ∈ Gz Z ∧ act u p = p) ↔ _
  rw [mem_Gz_iff]
  simp only [act, Prod.ext_iff]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨⟨hu, e1.2 (e2.1 h1)⟩, e3.1 h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨hu, e2.2 (e1.1 h1), e3.2 h2⟩

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
