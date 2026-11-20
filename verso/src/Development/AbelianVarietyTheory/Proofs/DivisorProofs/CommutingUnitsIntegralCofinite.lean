import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFixedFieldEmbeddingInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMonicPolynomialOfUnitRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralOfIntegralCoordsLocalTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusionStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocNormTau

variable {p : ℕ} [Fact p.Prime]

def tauR (G : HTGroup p) (β : G.Cˣ) (R : Type) [CommRing R] [Algebra ℚ R] (x : R ⊗[ℚ] G.C) : R ⊗[ℚ] G.C :=
  inC G R (β : G.C) * (starT G.star R x).unop * inC G R ((β⁻¹ : G.Cˣ) : G.C)

variable (G : HTGroup p) (β : G.Cˣ) (R : Type) [CommRing R] [Algebra ℚ R]

/- English proof (translation)
Simplify using `only [tauR, map_add, MulOpposite.unop_add, mul_add, add_mul]`.
-/
theorem tauR_add (x y : R ⊗[ℚ] G.C) : tauR G β R (x + y) = tauR G β R x + tauR G β R y := by
  simp only [tauR, map_add, MulOpposite.unop_add, mul_add, add_mul]

/- English proof (translation)
Rewrite using `[← map_mul, Units.inv_mul, map_one]`.
-/
theorem inC_inv_mul : inC G R ((β⁻¹ : G.Cˣ) : G.C) * inC G R (β : G.C) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

/- English proof (translation)
Establish `h` using `inC_inv_mul G β R`. Simplify using `only [tauR, map_mul, MulOpposite.unop_mul, mul_assoc]`. Use `congr 2`. Rewrite using `[← mul_assoc (inC G R ((β⁻¹ : G.Cˣ) : G.C)), h, one_mul]`.
-/
theorem tauR_mul (x y : R ⊗[ℚ] G.C) : tauR G β R (x * y) = tauR G β R y * tauR G β R x := by
  have h := inC_inv_mul G β R
  simp only [tauR, map_mul, MulOpposite.unop_mul, mul_assoc]
  congr 2
  rw [← mul_assoc (inC G R ((β⁻¹ : G.Cˣ) : G.C)), h, one_mul]

/- English proof (translation)
Simplify using `only [tauR, map_one, MulOpposite.unop_one, mul_one]`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.
-/
theorem tauR_one : tauR G β R 1 = 1 := by
  simp only [tauR, map_one, MulOpposite.unop_one, mul_one]
  rw [← map_mul, Units.mul_inv, map_one]

/- English proof (translation)
Simplify using `only [sh, map_mul, MulOpposite.unop_mul]`.
-/
theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

/- English proof (translation)
Establish `h : (starT G.star R (inC G R c)).unop = inC G R (sh G c)`. Express the relevant statement in the definitionally equal form `(starT G.star R ((1 : R) ⊗ₜ c)).unop = (1 : R) ⊗ₜ (G.star c).unop`. Conclude with `starT_tmul G.star R 1 c`. Simplify using `only [tauR, h, map_mul]`.
-/
theorem tauR_inC (c : G.C) :
    tauR G β R (inC G R c) = inC G R ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)) := by
  have h : (starT G.star R (inC G R c)).unop = inC G R (sh G c) := by
    change (starT G.star R ((1 : R) ⊗ₜ c)).unop = (1 : R) ⊗ₜ (G.star c).unop
    exact starT_tmul G.star R 1 c
  simp only [tauR, h, map_mul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact Commute.zero_right _`. Consider the case `tmul r c`. Express the relevant statement in the definitionally equal form `(1 : R) ⊗ₜ e * r ⊗ₜ c = r ⊗ₜ c * (1 : R) ⊗ₜ e`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, (he c).eq]`.

Consider the case `add x y hx hy => exact hx.add_right hy`.
-/
theorem commute_inC_of_forall (e : G.C) (he : ∀ c : G.C, Commute e c) (x : R ⊗[ℚ] G.C) :
    Commute (inC G R e) x := by
  induction x using TensorProduct.induction_on with
  | zero => exact Commute.zero_right _
  | tmul r c =>
    change (1 : R) ⊗ₜ e * r ⊗ₜ c = r ⊗ₜ c * (1 : R) ⊗ₜ e
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, (he c).eq]
  | add x y hx hy => exact hx.add_right hy

end GlobalTheory.LocNormTau

namespace GlobalTheory.LocNormTau

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hne` using `IsCMField.complexConj_ne_one G.F`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, IsCMField.complexConj G.F x ≠ x := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (AlgEquiv.ext h)`.

Use `⟨x - IsCMField.complexConj G.F x, sub_ne_zero.2 (Ne.symm hx), ?_⟩` and prove the remaining obligations. Simplify using `[IsCMField.complexConj_apply_apply]`.
-/
theorem exists_conj_neg (G : HTGroup p) : ∃ f : G.F, f ≠ 0 ∧ IsCMField.complexConj G.F f = -f := by
  have hne := IsCMField.complexConj_ne_one G.F
  obtain ⟨x, hx⟩ : ∃ x, IsCMField.complexConj G.F x ≠ x := by
    by_contra h
    push_neg at h
    exact hne (AlgEquiv.ext h)
  refine ⟨x - IsCMField.complexConj G.F x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  simp [IsCMField.complexConj_apply_apply]

/- English proof (translation)
Establish `h1 : a * (E * b) = a * b * E` using `by rw [hb.eq, mul_assoc]`. Establish `h2 : b * E * a = a * b * E` using `by rw [mul_assoc, ha.eq, ← mul_assoc, hab]`. Establish `h3 : b * E * (E * b) = E * E * (b * b)`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : E * b * a = a * b * E` using `by rw [mul_assoc, ← hab, (ha.mul_right hb).eq]`.

Establish `h5 : E * b * (b * E) = E * E * (b * b)`. Combine the equalities or inequalities in the displayed calculation. Prove the components needed by the constructor for the conclusion. Rewrite using `[show (a + b * E) * (a - E * b) = a * a - a * (E * b) + b * E * a - b * E * (E * b) by noncomm_ring, h1, h2, h3]`. Normalize the expressions using the abelian group laws.

Rewrite using `[show (a - E * b) * (a + b * E) = a * a + a * b * E - E * b * a - E * b * (b * E) by noncomm_ring, h4, h5]`. Normalize the expressions using the abelian group laws.
-/
theorem norm_aux {A : Type*} [Ring A] (a b E : A) (ha : Commute E a) (hb : Commute E b) (hab : a * b = b * a) :
    (a + b * E) * (a - E * b) = a * a - E * E * (b * b) ∧ (a - E * b) * (a + b * E) = a * a - E * E * (b * b) := by
  have h1 : a * (E * b) = a * b * E := by rw [hb.eq, mul_assoc]
  have h2 : b * E * a = a * b * E := by rw [mul_assoc, ha.eq, ← mul_assoc, hab]
  have h3 : b * E * (E * b) = E * E * (b * b) := by
    calc b * E * (E * b) = b * (E * E) * b := by noncomm_ring
      _ = E * E * (b * b) := by rw [← (hb.mul_left hb).eq, mul_assoc]
  have h4 : E * b * a = a * b * E := by rw [mul_assoc, ← hab, (ha.mul_right hb).eq]
  have h5 : E * b * (b * E) = E * E * (b * b) := by
    calc E * b * (b * E) = E * ((b * b) * E) := by noncomm_ring
      _ = E * E * (b * b) := by rw [← (hb.mul_right hb).eq, mul_assoc]
  constructor
  · rw [show (a + b * E) * (a - E * b) = a * a - a * (E * b) + b * E * a - b * E * (E * b) by noncomm_ring,
      h1, h2, h3]
    abel
  · rw [show (a - E * b) * (a + b * E) = a * a + a * b * E - E * b * a - E * b * (b * E) by noncomm_ring,
      h4, h5]
    abel

end GlobalTheory.LocNormTau
