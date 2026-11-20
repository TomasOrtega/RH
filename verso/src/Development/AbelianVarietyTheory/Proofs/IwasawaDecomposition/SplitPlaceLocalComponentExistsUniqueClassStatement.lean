import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocCompSplit.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSplitPlaceLocalComponentExistsUniqueClass.lean&line=289#L289)
-/
theorem _root_.GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L), ∃ σ, IsLocS π.S s σ ∧ ∀ (π' : NG.AutRep L n) (s' : SplitPlace L) (h : s'.w = s.w) σ', π.Iso π' → IsLocS π'.S s' σ' → HEq σ'.cl σ.cl := by
  first | exact @GlobalTheory.LocCompSplit.main | exact GlobalTheory.LocCompSplit.main | (intros; apply GlobalTheory.LocCompSplit.main <;> assumption)
