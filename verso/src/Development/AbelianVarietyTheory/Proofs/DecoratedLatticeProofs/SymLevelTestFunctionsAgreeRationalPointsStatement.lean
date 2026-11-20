import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SymBridge.PhiAgreeProof.phiAgree` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSymLevelTestFunctionsAgreeRationalPoints.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.symLevelTestFunctions_agree_rationalPoints : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → PhiAgree P q ι σ₀ ψ₀ χ S := by
  first | exact @GlobalTheory.SymBridge.PhiAgreeProof.phiAgree | exact GlobalTheory.SymBridge.PhiAgreeProof.phiAgree | (intros; apply GlobalTheory.SymBridge.PhiAgreeProof.phiAgree <;> assumption)
