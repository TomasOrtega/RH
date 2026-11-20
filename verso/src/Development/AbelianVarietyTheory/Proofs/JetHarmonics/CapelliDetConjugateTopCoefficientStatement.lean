import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FCapelliDetConjugateTopCoefficient.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.capelliDet_conjugate_top_coefficient : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin (p + m)) (Fin (p + m)) ℂ) (δ : A) (ν : Fin (p + m) → Fin p → A) (u : ℂ), GlRel E → (∀ a k, (∑ d, Q (Fin.castAdd m k) d • E a d) * δ = δ * ((∑ d, Q (Fin.castAdd m k) d • E a d) + ν a k)) → (∀ a k, (∑ d, Q (Fin.natAdd p k) d • E a d) * δ = δ * ∑ d, Q (Fin.natAdd p k) d • E a d) → (∀ a k, ν a k * δ = δ * ν a k) → Q.det • ∑ s : Fin (p + 1), ((F7.lagCo (fun j : Fin (p + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) = δ ^ p * ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun k : Fin p => ν (σ (Fin.castAdd m k)) k).prod * (List.ofFn fun k : Fin m => ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod) := by
  first | exact @GlobalTheory.CapelliTop.top_coefficient | exact GlobalTheory.CapelliTop.top_coefficient | (intros; apply GlobalTheory.CapelliTop.top_coefficient <;> assumption)
