import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealHermitianSelfDualOfLocalGenerator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.SelfDualIdeal.selfDual_of_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFractionalIdealHermitianSelfDualOfLocalGenerator.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.fractionalIdeal_hermitianSelfDual_of_local_generators : ∀ (D : D7) (h : D.host.E) (𝔞 : FI D) (u : (AE D)ˣ), (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ idV 𝔞 x ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) → (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (u : AE D) * cA D (u : AE D) * incA D h * a ∈ intAt D (· = x)) → ∀ d : D.host.E, d ∈ 𝔞 ↔ ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * h := by
  first | exact @GlobalTheory.FinPl.SelfDualIdeal.selfDual_of_local | exact GlobalTheory.FinPl.SelfDualIdeal.selfDual_of_local | (intros; apply GlobalTheory.FinPl.SelfDualIdeal.selfDual_of_local <;> assumption)
