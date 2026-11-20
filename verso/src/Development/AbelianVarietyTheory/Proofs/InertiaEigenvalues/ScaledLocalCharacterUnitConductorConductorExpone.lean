import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivial
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.RamShift

/- English proof (translation)
Introduce `E _ _ ϖ w hϖ`. Take `⟨ψ, hψ, hlc, hne⟩` from `GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one E w`. Establish `hcont : Continuous ψ` using `hlc.continuous`. Establish `hnorm : ∀ t, ‖ψ t‖ = 1` using `fun t => by`. Rewrite using `[hψ]`.

Conclude with `Circle.norm_coe _`. Establish `hne' : ∃ t, ψ t ≠ 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])`.

Take `⟨n, hn⟩` from `GlobalTheory.CharConductor.exists_conductor_exponent E w ψ hcont hnorm hne'`. Establish `hval : Valued.v (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = WithZero.exp n`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]`. Rewrite using `[← WithZero.exp, ← WithZero.exp_zsmul]`. Simplify using the standard rewrite rules.

Establish `key : CondOne w (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E)`. Introduce `x`. Establish `h1` using `hn ((((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) * x)`. Simplify using `only [hψ] at h1`. Rewrite `h1` using `[map_mul, hval]`.

Establish `h2 : WithZero.exp n * Valued.v x ≤ WithZero.exp n ↔ Valued.v x ≤ 1` using `by conv_lhs => rhs; rw [← mul_one (WithZero.exp n)]`. Conclude with `mul_le_mul_iff_right₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)`. Rewrite `h1` using `[h2]`. Conclude with `h1`. Unfold `condExp`.

Use `split_ifs with h1 h2`. Simplify using `using h1`. Conclude with `h2.choose_spec`. Conclude with `absurd ⟨-n, key⟩ h2`.
-/
theorem condOne_condExp : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)), IsUnifV E w (ϖ w : w.adicCompletion E) → GlobalTheory.RamShift.CondOne w ((ϖ w ^ GlobalTheory.RamShift.condExp ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  intro E _ _ ϖ w hϖ
  obtain ⟨ψ, hψ, hlc, hne⟩ := GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one E w
  have hcont : Continuous ψ := hlc.continuous
  have hnorm : ∀ t, ‖ψ t‖ = 1 := fun t => by
    rw [hψ]; exact Circle.norm_coe _
  have hne' : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_conductor_exponent E w ψ hcont hnorm hne'
  have hval : Valued.v (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = WithZero.exp n := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    rw [← WithZero.exp, ← WithZero.exp_zsmul]
    simp
  have key : CondOne w (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
    intro x
    have h1 := hn ((((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) * x)
    simp only [hψ] at h1
    rw [map_mul, hval] at h1
    have h2 : WithZero.exp n * Valued.v x ≤ WithZero.exp n ↔ Valued.v x ≤ 1 := by
      conv_lhs => rhs; rw [← mul_one (WithZero.exp n)]
      exact mul_le_mul_iff_right₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)
    rw [h2] at h1
    exact h1
  unfold condExp
  split_ifs with h1 h2
  · simpa using h1
  · exact h2.choose_spec
  · exact absurd ⟨-n, key⟩ h2

end GlobalTheory.RamShift
