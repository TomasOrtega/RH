import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharpolyLatticeKillsSpan
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.charpoly_split_kills_span` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSplitCharpolyLatticeKillsSpan.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.split_charpoly_lattice_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  first | exact @GlobalTheory.charpoly_split_kills_span | exact GlobalTheory.charpoly_split_kills_span | (intros; apply GlobalTheory.charpoly_split_kills_span <;> assumption)
