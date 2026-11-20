import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalObjectsEveryFamilyWildStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem GlobalTheory.AdmissibleCore.main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.CoefDuty.TakenAll D → GlobalTheory.PtCore.ResAbsIrr D → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π := by
  intro hC D X hT hA hX i π hπ
  intro hZ
  obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (X.r i π) (X.ρ i π) (D.nd.chi i) e := ⟨e, fun g u => he g u⟩
  have hHG : IsHeckeGalois D.nd i π (X.r i π) := hX.good i π
  have hpt : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (X.ρ i π) := ⟨hX.cont i π, X.r i π, hHG, e, fun g u => he g u⟩
  have hirr := hA i π hπ (X.ρ i π) hpt
  have hLive : GlobalTheory.CoefDuty.Live D.nd i := ⟨π, hZ, X.r i π, X.ρ i π, hHG, hdec, hirr⟩
  obtain ⟨r₀, ρ₀, hg₀, hw₀⟩ := hT i hLive
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hg₀ hw₀ (X.r i) (X.ρ i) (hX.good i) π hZ hdec
  exact ⟨S, hS⟩
