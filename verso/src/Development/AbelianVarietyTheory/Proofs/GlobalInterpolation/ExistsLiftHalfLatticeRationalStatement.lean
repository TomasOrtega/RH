import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRational
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomT.exists_lift_halfAO` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsLiftHalfLatticeRational.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_lift_halfLattice_rational : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), A.AA.FG → A.AA ≠ ⊥ → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∃ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') := by
  first | exact @GlobalTheory.MomT.exists_lift_halfAO | exact GlobalTheory.MomT.exists_lift_halfAO | (intros; apply GlobalTheory.MomT.exists_lift_halfAO <;> assumption)
