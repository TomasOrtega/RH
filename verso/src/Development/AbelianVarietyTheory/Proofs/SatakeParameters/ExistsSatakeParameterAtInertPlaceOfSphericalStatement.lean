import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterAtInertPlaceOfSpherical
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SatExists.exists_satAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsSatakeParameterAtInertPlaceOfSpherical.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  first | exact @GlobalTheory.SatExists.exists_satAt | exact GlobalTheory.SatExists.exists_satAt | (intros; apply GlobalTheory.SatExists.exists_satAt <;> assumption)
