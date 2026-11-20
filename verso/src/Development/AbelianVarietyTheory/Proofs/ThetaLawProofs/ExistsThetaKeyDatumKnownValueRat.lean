import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsKeyPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LatticeBlocks
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplexStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

/- English proof (authored)
Unpack the normal-form data for a value of x. Each entry of the two characteristic vectors is either zero or one half, so both vectors coincide pointwise with their real-part vectors viewed over ℂ. The power formula for normal forms then gives the transformed data for y and its determinant relation.

Use the transformed data as the witnesses for the value of y. The new constant is cʲ and is nonzero because c is nonzero. Substituting the determinant relation and combining the powers gives the value tʲ.
-/
theorem Val.pow {x y : KeyIn ℂ} {j : ℕ} {t : ℂ} (hp : IsKeyPow y x j) (h : Val x t) : Val y (t ^ j) := by
  obtain ⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hN, rfl⟩ := h
  have ea : a = fun k => (((a k).re : ℝ) : ℂ) := by
    funext k
    rcases ha k with h | h <;> rw [h] <;> norm_num
  have eb : b = fun k => (((b k).re : ℝ) : ℂ) := by
    funext k
    rcases hb k with h | h <;> rw [h] <;> norm_num
  rw [ea, eb] at hN
  obtain ⟨e, τ', M', hdet, hN'⟩ := normalAt_pow x y j τ M _ _ c hp hN
  refine ⟨τ', M', _, _, c ^ j, ⟨fun p => ?_, fun p => ?_⟩, pow_ne_zero _ hc, hN', ?_⟩
  · rw [← congrFun ea]; exact ha _
  · rw [← congrFun eb]; exact hb _
  · rw [hdet, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm 4, Nat.mul_comm 8]

/- English proof (authored)
Compute the Weierstrass invariants of the model y² = x³ − x and substitute them in the discriminant formula. The discriminant is 64. It is nonzero, hence a unit in ℚ, which is the ellipticity criterion for the model.
-/
theorem isElliptic_cube_sub : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic := by
  refine ⟨Ne.isUnit ?_⟩
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/- English proof (authored)
Start with the rational elliptic curve y² = x³ − x. Its elliptic key has genus one and known value equal to the discriminant. Take its gth key power to get genus g. The proposed known value is the gth power of the discriminant.

After extension to ℂ, choose normal-form data for the original elliptic key. The discriminant formula gives its value in this normal form. The key power raises that value to the gth power by `Val.pow`. The base-change comparison and cancellation identify this normal form with the one for the given complex key of genus g, giving the required known value.
-/
theorem exists_known_rat : Out.Laws → ThetaUnifAV → ∀ g : ℕ, 1 ≤ g → ∃ y : KeyIn ℚ, y.P.g = g ∧ Known ℚ y := by
  intro _ hU g hg
  have := isElliptic_cube_sub
  obtain ⟨y₁, h₁, hval⟩ := EllipticKey.exists_keyIn_value_eq_discriminant hU ℚ ⟨0, 0, 0, -1, 0⟩
  obtain ⟨y, hy⟩ := exists_isKeyPow ℚ y₁ g hg
  refine ⟨y, ?_, (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ ^ g, fun e x hx => ?_⟩
  · obtain ⟨-, h, -⟩ := hy
    rw [← h, h₁, Nat.mul_one]
  · obtain ⟨x₁, hx₁⟩ := exists_keyPB_ring y₁ e
    obtain ⟨⟨τ, M, a, b, c, hab, hc, -, hN⟩, -⟩ := KeyNormalExists.exists_normalAt hU x₁
    have hv₁ : Val x₁ (e (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ) :=
      ⟨τ, M, a, b, c, hab, hc, hN, (hval e x₁ τ M a b c hx₁ hab hc hN).symm⟩
    obtain ⟨x', hx'⟩ := exists_isKeyPow ℂ x₁ g hg
    have hpb := keyPB_of_isKeyPow ℚ ℂ e y₁ y x₁ x' g hx₁ hy hx'
    have hid : KeyPB x x' (RingHom.id ℂ) := KeyCancel.keyPB_cancel ℚ ℂ ℂ y x' x e (RingHom.id ℂ) hpb hx
    rw [map_pow]
    exact ((GlobalTheory.T.normalForms_eq_of_keyDataIso_complex x' x hid).1 _).1 (hv₁.pow hx')

end GlobalTheory.KeyFam
