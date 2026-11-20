import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Form

/- English proof (translation)
Establish `sh_mul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a`. Introduce `a b`. Simplify using `only [sh, map_mul, MulOpposite.unop_mul]`. Establish `sh_one : sh G (1 : G.C) = 1` using `by simp only [sh, map_one, MulOpposite.unop_one]`. Use `⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩` and prove the remaining obligations.

Conclude with `⟨1, 1, one_pos, by simp [sh_one]⟩`. Take `⟨y, s, hs, hβ⟩` from `h`. Use `⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩` and prove the remaining obligations. Establish `e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1`. Rewrite using `[← sh_mul, Units.inv_mul, sh_one]`.

Rewrite using `[hβ]`. Simplify using `only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one, inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]`. Take `⟨y, s, hs, hβ⟩` from `h`. Take `⟨y', s', hs', hβ'⟩` from `h'`. Use `⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[hβ', hβ, Units.val_mul, sh_mul]`. Simplify using `only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]`.
-/
theorem rel_equivalence {p : ℕ} [Fact p.Prime] (G : HTGroup p) : Equivalence (Form.Rel (G := G)) := by
  have sh_mul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have sh_one : sh G (1 : G.C) = 1 := by simp only [sh, map_one, MulOpposite.unop_one]
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · exact ⟨1, 1, one_pos, by simp [sh_one]⟩
  · obtain ⟨y, s, hs, hβ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩
    have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
      rw [← sh_mul, Units.inv_mul, sh_one]
    rw [hβ]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
      inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
  · obtain ⟨y, s, hs, hβ⟩ := h
    obtain ⟨y', s', hs', hβ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩
    rw [hβ', hβ, Units.val_mul, sh_mul]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]

/- English proof (translation)
Introduce `p _ G P Q`. Rewrite using `[← (rel_equivalence G).eqvGen_iff]`. Conclude with `⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩`.
-/
theorem mk_eq_iff_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G),
    Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  intro p _ G P Q
  rw [← (rel_equivalence G).eqvGen_iff]
  exact ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

end GlobalTheory.LKCx.Form
