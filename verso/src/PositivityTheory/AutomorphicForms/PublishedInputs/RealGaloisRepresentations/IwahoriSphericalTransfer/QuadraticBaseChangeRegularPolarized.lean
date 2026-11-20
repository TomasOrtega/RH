import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BcRegAlgPolarizedPair
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BcPolar.bc_regAlg_polarizedPair` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=PositivityTheory%2FAutomorphicForms%2FPublishedInputs%2FRealGaloisRepresentations%2FIwahoriSphericalTransfer%2FBcRegAlgPolarizedPair.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.quadratic_base_change_regular_polarized : GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K], Module.finrank F K = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (χ : HChar F) (P : CuspSub K a), π.IsRegAlg → π.Polarized χ → IsBC π P → (CG.mk P).IsRegAlg ∧ ∃ χ' : HChar (maximalRealSubfield K), GlobalTheory.ContraPair.PolarizedPair P χ' := by
  first | exact @GlobalTheory.BcPolar.bc_regAlg_polarizedPair | exact GlobalTheory.BcPolar.bc_regAlg_polarizedPair | (intros; apply GlobalTheory.BcPolar.bc_regAlg_polarizedPair <;> assumption)
