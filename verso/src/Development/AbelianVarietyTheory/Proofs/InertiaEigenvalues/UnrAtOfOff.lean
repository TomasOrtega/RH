import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatMMemOfLeHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistUnrOff

/- English proof (translation)
Introduce `D δ hδ χ hc P hPQ hconj`. Rewrite using `[← GlobalTheory.LFun.unrAt_iff_of_chrEq hc P]`. Apply `GlobalTheory.GoodModUnr.unrAt_of_unrPl` to reduce the goal to its premises. Introduce `e f hp x hx h2 h3`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.IdemSupport.exists_comp D`.

Take `⟨-, ε, hε, rfl⟩` from `GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hp`. Establish `hoff` using `GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hδ.unram hδ.split (Finset.Subset.refl _)`. Use `hoff _ ε hε ?_ x hx h2 h3` and prove the remaining obligations. Introduce `PP hPP hu`. Break down `GlobalTheory.IdemSupport.eq_or_eq_cP hu.symm with h | h` into its components or cases.

Conclude with `hPQ (h ▸ hPP)`. Conclude with `hconj ⟨PP, hPP, (GlobalTheory.IdemSupport.isConjPl_iff PP P).2 h⟩`.
-/
theorem unrAt_of_off : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E), ChrEq δ.chi χ → ∀ P : Pl D.host.E, P ∉ δ.Q → (¬ ∃ P' ∈ δ.Q, Formalism.IndefR.Lev.IsConjPl P' P) → χ.UnrAt P := by
  intro D δ hδ χ hc P hPQ hconj
  rw [← GlobalTheory.LFun.unrAt_iff_of_chrEq hc P]
  apply GlobalTheory.GoodModUnr.unrAt_of_unrPl
  intro e f hp x hx h2 h3
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hp
  have hoff := GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hδ.unram hδ.split (Finset.Subset.refl _)
  refine hoff _ ε hε ?_ x hx h2 h3
  intro PP hPP hu
  rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu.symm with h | h
  · exact hPQ (h ▸ hPP)
  · exact hconj ⟨PP, hPP, (GlobalTheory.IdemSupport.isConjPl_iff PP P).2 h⟩

end GlobalTheory.TwistUnrOff
