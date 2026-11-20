import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

/- English proof (translation)
Introduce `k r z z' χε ε n hχ`. Take `⟨hχs, hχd, -⟩` from `hχ`. Take `⟨hsmC, hwb⟩` from `h2 k r (2 * (r + 1)) (fun g => ((Gf k r z z' g : ℝ) : ℂ)) (h1 k r z z')`. Establish `hsmR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => Gf k r z z' g)`. Establish `h` using `Complex.reCLM.contDiff.comp hsmC`.

Simplify `h` using `[Function.comp_def]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Complex.ofRealCLM.contDiff.comp (hχs.comp hsmR)`. Take `⟨C₀, hC₀⟩` from `hwb n`. Use `h3 k r (fun g => Gf k r z z' g) χε (fun _ => 2 * (r + 1)) n C₀ hsmR hχs hχd ?_` and prove the remaining obligations.

Introduce `u v hu hv hlen hne g hg`. Establish `hb` using `hC₀ u v hu hv hlen g hg`. Establish `h1g : 1 ≤ B.gN g` using `gN_ge_one hg`. Establish `hexp : ((2 * (r + 1) : ℕ) : ℝ) + ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ) ≤ ((((u ++ v).map (fun _ => 2 * (r + 1))).sum : ℕ) : ℝ)`. Establish `hl : 1 ≤ (u ++ v).length` using `List.length_pos_iff.mpr hne`.

Simplify using `only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero, add_zero]`. Conclude with `Nat.le_mul_of_pos_left _ hl` after adjusting the coercions. Establish `hpos : 0 < B.gN g ^ (((2 * (r + 1) : ℕ) : ℝ) + ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ))` using `Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h1g) _`. Establish `hC : 0 ≤ C₀` using `(mul_nonneg_iff_of_pos_right hpos).mp ((norm_nonneg _).trans hb)`. Conclude with `hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1g hexp) hC)`.
-/
theorem gfWB_of (h1 : GfPoly) (h2 : PolyB) (h3 : CompR) : GfWB := by
  intro k r z z' χε ε n hχ
  obtain ⟨hχs, hχd, -⟩ := hχ
  obtain ⟨hsmC, hwb⟩ :=
    h2 k r (2 * (r + 1)) (fun g => ((Gf k r z z' g : ℝ) : ℂ)) (h1 k r z z')
  have hsmR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => Gf k r z z' g) := by
    have h := Complex.reCLM.contDiff.comp hsmC
    simpa [Function.comp_def] using h
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hχs.comp hsmR)
  · obtain ⟨C₀, hC₀⟩ := hwb n
    refine h3 k r (fun g => Gf k r z z' g) χε (fun _ => 2 * (r + 1)) n C₀ hsmR hχs hχd ?_
    intro u v hu hv hlen hne g hg
    have hb := hC₀ u v hu hv hlen g hg
    have h1g : 1 ≤ B.gN g := gN_ge_one hg
    have hexp : ((2 * (r + 1) : ℕ) : ℝ) + ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ) ≤
        ((((u ++ v).map (fun _ => 2 * (r + 1))).sum : ℕ) : ℝ) := by
      have hl : 1 ≤ (u ++ v).length := List.length_pos_iff.mpr hne
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero,
        add_zero]
      exact_mod_cast Nat.le_mul_of_pos_left _ hl
    have hpos : 0 < B.gN g ^ (((2 * (r + 1) : ℕ) : ℝ) +
        ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h1g) _
    have hC : 0 ≤ C₀ := (mul_nonneg_iff_of_pos_right hpos).mp ((norm_nonneg _).trans hb)
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1g hexp) hC)

end PI.UnitaryCorollaryDerivatives
