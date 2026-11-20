import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sh_mul' (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sh_add' (G : HTGroup p) (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add, MulOpposite.unop_add]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sh_sh' (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sh_inv_of_sym (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have e : sh G ((β⁻¹ : G.Cˣ) : G.C) * β = 1 := by
    rw [← hβ, ← sh_mul', Units.mul_inv, sh_one']
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [e, one_mul]

end GlobalTheory.CentConj

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.CentConj
