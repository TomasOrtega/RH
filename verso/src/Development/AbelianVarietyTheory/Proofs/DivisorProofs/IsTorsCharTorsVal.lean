import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {p : ℕ} {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {G : PDivGroup p R}
  (t : G.TorsionTower A) (N : ℕ)

open Classical in

def torsVal (b : G.A N) : Fn0 A := fun D _ _ x ↦
  if h : x ^ p ^ N = 1 then t.lift N x h b else 0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lift_spOver {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (w : Pt A D) (hw : w ^ p ^ N = 1) (hw' : (spOver φ ≫ w) ^ p ^ N = 1) :
    t.lift N (spOver φ ≫ w) hw' = φ.comp (t.lift N w hw) :=
  t.inj N D' _ _ (by rw [t.lift_y, ← spOver_comp, Category.assoc, t.lift_y])

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lift_mul {D : Type} [CommRing D] [Algebra R D] (w w' : Pt A D) (hw : w ^ p ^ N = 1)
    (hw' : w' ^ p ^ N = 1) (h : (w * w') ^ p ^ N = 1) :
    t.lift N (w * w') h = (toConv (t.lift N w hw) * toConv (t.lift N w' hw')).ofConv :=
  t.inj N D _ _ (by rw [t.lift_y, t.mul, ofConv_toConv, ofConv_toConv, t.lift_y, t.lift_y])

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isTorsChar_torsVal (b : G.A N) (hb : cobOne R (G.A N) b = 0) :
    IsTorsChar (p ^ N) (torsVal t N b) := by
  have hc : Coalgebra.comul (R := R) b = b ⊗ₜ 1 + 1 ⊗ₜ b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb; exact hb
  refine ⟨fun D _ _ D' _ _ φ w hw ↦ ?_, fun D _ _ w w' hw hw' ↦ ?_⟩
  · have hw2 : (spOver φ ≫ w) ^ p ^ N = 1 := by rw [← MonObj.comp_pow, hw, MonObj.comp_one]
    simp only [torsVal, dif_pos hw, dif_pos hw2, lift_spOver t N φ w hw hw2, AlgHom.comp_apply]
  · have h : (w * w') ^ p ^ N = 1 := (t.exists_iff N _).1
      ⟨(toConv (t.lift N w hw) * toConv (t.lift N w' hw')).ofConv, by
        rw [t.mul, ofConv_toConv, ofConv_toConv, t.lift_y, t.lift_y]⟩
    simp only [torsVal, dif_pos hw, dif_pos hw', dif_pos h, lift_mul t N w w' hw hw' h,
      AlgHom.convMul_apply, hc, map_add, Algebra.TensorProduct.lift_tmul, ofConv_toConv, map_one,
      _root_.mul_one, _root_.one_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem exists_isTorsChar : ∀ (p : ℕ)  (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (G : PDivGroup p R) (t : G.TorsionTower A) (N : ℕ) (b : G.A N), cobOne R (G.A N) b = 0 → ∃ β : Fn0 A, IsTorsChar (p ^ N) β ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (φ : G.A N →ₐ[R] D), β D (spOver φ ≫ t.y N) = φ b := by
  intro p R _ A _ G t N b hb
  refine ⟨torsVal t N b, isTorsChar_torsVal t N b hb, fun D _ _ φ ↦ ?_⟩
  have h : (spOver φ ≫ t.y N) ^ p ^ N = 1 := (t.exists_iff N _).1 ⟨φ, rfl⟩
  have e : t.lift N (spOver φ ≫ t.y N) h = φ := t.inj N D _ _ (t.lift_y N _ h)
  simp only [torsVal, dif_pos h, e]

end GlobalTheory.PtExt
