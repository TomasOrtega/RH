import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariants
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FUnramifiedH1CardInvariants.lean&line=309#L309)
-/
theorem _root_.GlobalTheory.T.unramified_h1_card_invariants : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (hρ : ContAction ρ), IsPlaceOver A v → Nat.card (H1ur ρ ((Ine (F := F) A).subgroupOf (Dec (F := F) A))) = Nat.card (H0 ρ) := by
  first | exact @GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 | exact GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 | (intros; apply GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 <;> assumption)
