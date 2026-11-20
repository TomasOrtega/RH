import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticePointsIntegralIdelesEquiv
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLatticePointsIntegralIdelesEquiv.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.exists_latticePoints_integralIdeles_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ → ∃ e : (Σ q : PicO c, modUnits (lattice c q.out)) ≃ {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c}, ∀ p, ∀ y : (Af E)ˣ, (y : Af E) = algebraMap E (Af E) (p.2.1.out) * (((Quotient.out p.1 : (Af E)ˣ)⁻¹ : (Af E)ˣ) : Af E) → (e p).1 = QuotientGroup.mk y := by
  first | exact @GlobalTheory.CMVal.LatBij.exists_equiv | exact GlobalTheory.CMVal.LatBij.exists_equiv | (intros; apply GlobalTheory.CMVal.LatBij.exists_equiv <;> assumption)
