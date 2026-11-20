import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Simplify using `only [sh, map_mul, MulOpposite.unop_mul]`.
-/
theorem sh_mul' (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

/- English proof (translation)
Simplify using `only [sh, map_add, MulOpposite.unop_add]`.
-/
theorem sh_add' (G : HTGroup p) (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add, MulOpposite.unop_add]

/- English proof (translation)
Simplify using `only [sh, map_one, MulOpposite.unop_one]`.
-/
theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

/- English proof (translation)
The claim follows from `G.star_star x`.
-/
theorem sh_sh' (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

/- English proof (translation)
Establish `e : sh G ((β⁻¹ : G.Cˣ) : G.C) * β = 1`. Rewrite using `[← hβ, ← sh_mul', Units.mul_inv, sh_one']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, Units.mul_inv, mul_one]`. Use `_ = _ := by rw [e, one_mul]`.
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
