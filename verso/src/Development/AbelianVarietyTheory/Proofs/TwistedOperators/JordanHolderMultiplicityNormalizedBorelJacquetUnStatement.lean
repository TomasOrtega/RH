import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FJordanHolderMultiplicityNormalizedBorelJacquetUn.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_normalizedBorelJacquet_unramified : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  first | exact @GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult | exact GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult | (intros; apply GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult <;> assumption)
