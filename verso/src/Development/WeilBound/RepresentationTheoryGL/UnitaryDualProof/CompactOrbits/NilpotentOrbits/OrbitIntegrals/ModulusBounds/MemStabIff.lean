import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.EntIntegral

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Simplify using `only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]`.
-/
theorem conj_sub_one (g u : GL (Fin n) k) : (g⁻¹ * u * g).val - 1 = g⁻¹.val * (u.val - 1) * g.val := by
  simp only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]

/- English proof (translation)
Establish `e : (u.val - 1) * (p.1 - c) - (p.1 - c) * (u.val - 1) = (u.val * p.1 - p.1 * u.val) - (u.val * c - c * u.val)` using `by noncomm_ring`. Rewrite `e` using `[hcu, sub_self, sub_zero]`. Establish `e1 : (u.val - 1) * (p.1 - c) = (p.1 - c) * (u.val - 1) ↔ u.val * p.1 = p.1 * u.val`. Rewrite using `[← sub_eq_zero, e, sub_eq_zero]`. Establish `e2 : u.val * p.1 * u⁻¹.val = p.1 ↔ u.val * p.1 = p.1 * u.val`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Introduce `h`. Rewrite using `[h, mul_assoc, Units.mul_inv, mul_one]`.

Establish `e3 : u.val *ᵥ p.2 = p.2 ↔ (u.val - 1) *ᵥ p.2 = 0`. Rewrite using `[sub_mulVec, one_mulVec, sub_eq_zero]`. Use `show (u ∈ Gz Z ∧ act u p = p) ↔ _`. Rewrite using `[mem_Gz_iff]`. Simplify using `only [act, Prod.ext_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h1, h2⟩`. Conclude with `⟨⟨hu, e1.2 (e2.1 h1)⟩, e3.1 h2⟩`. Introduce and unpack `⟨⟨-, h1⟩, h2⟩`. Conclude with `⟨hu, e2.2 (e1.1 h1), e3.2 h2⟩`.
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
