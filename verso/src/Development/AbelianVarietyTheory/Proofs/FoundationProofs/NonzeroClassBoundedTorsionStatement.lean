import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroClassBoundedTorsion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNonzeroClassBoundedTorsion.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.nonzero_class_bounded_torsion : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → Y ∈ Z1 (Loc.colRep W) → (∀ s i, Y s i ∈ c.O) → Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) → ∃ k0 : ℕ, ∀ (n : ℕ) (a : Qbar l), a ∈ c.O → Cob1 c n W ⊤ (fun s => a • Y s) → Cg n (a * ((l : ℕ) : Qbar l) ^ k0) 0 := by
  first | exact @GlobalTheory.Ord2.GwCount.closed_multiplier | exact GlobalTheory.Ord2.GwCount.closed_multiplier | (intros; apply GlobalTheory.Ord2.GwCount.closed_multiplier <;> assumption)
