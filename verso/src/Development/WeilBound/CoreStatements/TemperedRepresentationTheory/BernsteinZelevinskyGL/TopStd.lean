import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLengthStatement

namespace PositivityTheory.Tls2.BZGL

/- English proof (translation)
Introduce `k _ _ _ _ r d _`. Use `⟨fun V _ _ π hπ hl => ?_, fun W _ _ ρ hρ hl => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.jacquet_module_finite_length k (Fin r) (Fin (∑ a, d a)) (fun a => Fin (d a)) finSigmaFinEquiv V π hπ hl`. Conclude with `GlobalTheory.T.parabolic_induction_finite_length k (Fin r) (Fin (∑ a, d a)) (fun a => Fin (d a)) finSigmaFinEquiv W ρ hρ hl`.
-/
theorem standardFunctorsFiniteLength_top : GlobalTheory.Published.StandardFunctorsFiniteLength := by
  intro k _ _ _ _ r d _
  refine ⟨fun V _ _ π hπ hl => ?_, fun W _ _ ρ hρ hl => ?_⟩
  · exact GlobalTheory.T.jacquet_module_finite_length k (Fin r) (Fin (∑ a, d a)) (fun a => Fin (d a)) finSigmaFinEquiv V π hπ hl
  · exact GlobalTheory.T.parabolic_induction_finite_length k (Fin r) (Fin (∑ a, d a)) (fun a => Fin (d a)) finSigmaFinEquiv W ρ hρ hl

end PositivityTheory.Tls2.BZGL
