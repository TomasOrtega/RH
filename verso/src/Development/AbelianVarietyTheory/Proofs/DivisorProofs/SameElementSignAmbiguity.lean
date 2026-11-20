import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

/- English proof (translation)
The claim follows from `Module.Finite.trans G.F G.C`.
-/
theorem finiteQ (G : HTGroup p) : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C

/- English proof (translation)
Use `haveI := finiteQ G`. Establish `h` using `congrArg (Algebra.norm ℚ) P.sim`. Rewrite `h` using `[map_mul, map_mul, map_mul, Algebra.norm_algebraMap]`. Establish `hb : Algebra.norm ℚ (P.β : G.C) ≠ 0` using `(P.β.isUnit.map (Algebra.norm ℚ)).ne_zero`. Apply `mul_right_cancel₀ hb` to reduce the goal to its premises.

Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sim (P : Pair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  haveI := finiteQ G
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

/- English proof (translation)
Introduce `p _ G P P' hγ`. Use `haveI := finiteQ G`. Establish `h1` using `norm_sim P`. Establish `h2` using `norm_sim P'`. Rewrite `h2` using `[hγ, h1]`.

Establish `hN : Module.finrank ℚ G.C ≠ 0` using `Module.finrank_pos.ne'`. Break down `(pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩` into its components or cases. Conclude with `Or.inl (Units.ext h)`. Conclude with `Or.inr (Units.ext (by rw [h, Units.val_neg]))`.
-/
theorem c_eq_or_eq_neg : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G), P'.γ = P.γ → P'.c = P.c ∨ P'.c = -P.c := by
  intro p _ G P P' hγ
  haveI := finiteQ G
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

end GlobalTheory.LKMid.Pair
