import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaSelfH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondLeviFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpowRightEqPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapPNeg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand

namespace GlobalTheory.CompanionTheory.CapClsA

open GlobalTheory.CompanionTheory.PairMult

/- English proof (translation)
Introduce `n V _ _ E χ hE hg Y`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.CapelliNewton.capelli_of_gelfand V n E χ hE (fun k x => by rw [etr_eq_gelA]; exact hg (k + 1) x) Y v`. Simplify `h` using `[Formalism.QuantumDeterminants.capP]`.
-/
theorem capOne_newton : CapOne := by
  intro n V _ _ E χ hE hg Y
  refine LinearMap.ext fun v => ?_
  have h := GlobalTheory.CapelliNewton.capelli_of_gelfand V n E χ hE
    (fun k x => by rw [etr_eq_gelA]; exact hg (k + 1) x) Y v
  simpa [Formalism.QuantumDeterminants.capP] using h

/- English proof (translation)
Introduce `n V _ _ E χ hE hg Y`. Take `⟨hF, hq⟩` from `GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE`. Establish `h` using `capOne_newton n V (PositivityTheory.RgBcC.RealD.barF E) (fun a => -χ a) hF hg (-Y)`. Establish `hq'` using `hq (-Y + ((n : ℂ) - 1) / 2)`. Establish `harg : (n : ℂ) - 1 - (-Y + ((n : ℂ) - 1) / 2) = Y + ((n : ℂ) - 1) / 2` using `by ring`.

Rewrite `hq'` using `[harg]`. Establish `hne : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Establish `h2 : ((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) = ((-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y) • (1 : Module.End ℂ V)`.

Rewrite using `[← hq', ← capelliPoly_neg]`. Conclude with `h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, hne, one_smul]`. Use `_ = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by`.

Rewrite using `[h2, smul_smul, ← mul_assoc, hne, one_mul]`.
-/
theorem dualCap_newton : DualCap := by
  intro n V _ _ E χ hE hg Y
  obtain ⟨hF, hq⟩ := GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  have h := capOne_newton n V (PositivityTheory.RgBcC.RealD.barF E) (fun a => -χ a) hF hg (-Y)
  have hq' := hq (-Y + ((n : ℂ) - 1) / 2)
  have harg : (n : ℂ) - 1 - (-Y + ((n : ℂ) - 1) / 2) = Y + ((n : ℂ) - 1) / 2 := by ring
  rw [harg] at hq'
  have hne : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]; simp
  have h2 : ((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) =
      ((-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y) • (1 : Module.End ℂ V) := by
    rw [← hq', ← capelliPoly_neg]
    exact h
  calc Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)
      = ((-1 : ℂ) ^ n) • (((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)) := by
        rw [smul_smul, hne, one_smul]
    _ = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by
        rw [h2, smul_smul, ← mul_assoc, hne, one_mul]

/- English proof (translation)
Introduce `hAct` and use `GlobalTheory.CompanionTheory.CapClsProof.capCls_of hAct capOne_newton dualCap_newton`.
-/
theorem capCls_of_actUU : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := fun hAct =>
  GlobalTheory.CompanionTheory.CapClsProof.capCls_of hAct capOne_newton dualCap_newton

end GlobalTheory.CompanionTheory.CapClsA
