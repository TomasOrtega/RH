import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

/- English proof (translation)
Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem actOn_inC {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (c : G.C) (w : VQ D) :
    actOn L.rep (AfP p) (inC G (AfP p) c) ((1 : AfP p) ⊗ₜ w) = (1 : AfP p) ⊗ₜ (L.rep c w) := by
  simp only [actOn, inC, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, one_mul, Module.End.baseChangeHom, AlgHom.comp_apply]
  exact LinearMap.baseChange_tmul _ _ _

/- English proof (translation)
Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem actG_toAf {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (B : GlobalTheory.LKCx.Form G)
    (y : GlobalTheory.LKCx.grp G B.β) (w : VQ D) :
    L.actG (B.toAf y) (actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ w)) =
      actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) w)) := by
  have hval : (L.actG (B.toAf y) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
      = actOn L.rep (AfP p) ((trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := rfl
  rw [hval, ← Module.End.mul_apply, ← map_mul,
    show (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C)
        = (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) by
      simp [mul_assoc],
    map_mul, Module.End.mul_apply, actOn_inC]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rdAct_of : RdAct := by
  intro p _ D G L B y h₁ h₂ w
  simp only [rd, actY]
  conv_rhs =>
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one, map_mul,
      Module.End.mul_apply, actG_toAf]

end UpperTheory.Gal.W2
