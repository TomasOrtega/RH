import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FWeilRepEquivOfCharpolyEq.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.weilRep_equiv_of_charpoly_eq : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)), (∀ σ : Weil h, (a.ρ σ).charpoly = (b.ρ σ).charpoly) → ∃ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), ∀ σ z, e (a.ρ σ z) = b.ρ σ (e z) := by
  first | exact @GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq | exact GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq | (intros; apply GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq <;> assumption)
