import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

/- English proof (translation)
Simplify using `only [sh, map_mul, MulOpposite.unop_mul]`.
-/
theorem sh_mul' (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

/- English proof (translation)
Simplify using `only [sh, map_one, MulOpposite.unop_one]`.
-/
theorem sh_one' : sh G (1 : G.C) = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

/- English proof (translation)
Introduce `p _ G`. Use `⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩` and prove the remaining obligations. Use `⟨1, 1, one_pos, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[sh_one']`. Simplify using the standard rewrite rules.

Take `⟨y, s, hs, hβ, hγ⟩` from `h`. Use `⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩` and prove the remaining obligations. Establish `e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1`. Rewrite using `[← sh_mul', Units.inv_mul, sh_one']`. Rewrite using `[hβ]`.

Simplify using `only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one, inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]`. Rewrite using `[hγ]`. Use `group`. Take `⟨y, s, hs, hβ, hγ⟩` from `h`. Take `⟨y', s', hs', hβ', hγ'⟩` from `h'`.

Use `⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hβ', hβ, Units.val_mul, sh_mul']`. Simplify using `only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]`. Rewrite using `[hγ', hγ]`. Use `group`.
-/
theorem rel_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  intro p _ G
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, ?_⟩
    · simp [sh_one']
    · simp
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        rw [← sh_mul', Units.inv_mul, sh_one']
      rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
        inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, sh_mul']
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]
    · rw [hγ', hγ]; group

end GlobalTheory.LKMid.Pair
