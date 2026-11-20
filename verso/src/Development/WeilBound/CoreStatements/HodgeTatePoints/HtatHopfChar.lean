import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharactersStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopf
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.SectionCharValues

/- English proof (translation)
Introduce `R _ _ _ _ T _ _ Γ χ`. Establish `hA` using `PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder hHenselian hBaseChange hRegular R T Γ`. Establish `hm` using `char_mem_hopfOrder R T _ hA χ`. Take `⟨s, hs⟩` from `(PositivityTheory.HtPt.Htat.ValuationInjectivePi.mem_btOrder_iff Γ _).mp hm 1`. Use `⟨s, fun t => ?_⟩` and prove the remaining obligations.

Conclude with `(hs t _).trans (by simp)`.
-/
theorem exists_section_hasValues_char (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T]
      (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) := by
  intro R _ _ _ _ T _ _ Γ χ
  have hA := PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder hHenselian hBaseChange hRegular R T Γ
  have hm := char_mem_hopfOrder R T _ hA χ
  obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Htat.ValuationInjectivePi.mem_btOrder_iff Γ _).mp hm 1
  refine ⟨s, fun t => ?_⟩
  exact (hs t _).trans (by simp)

end PositivityTheory.HtPt.Htat.SectionCharValues

/- English proof (translation)
The claim follows from `@PositivityTheory.HtPt.Htat.SectionCharValues.exists_section_hasValues_char hHenselian hBaseChange hRegular`.
-/
theorem PositivityTheory.HtPt.Htat.ht_char_section_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) :=
  @PositivityTheory.HtPt.Htat.SectionCharValues.exists_section_hasValues_char hHenselian hBaseChange hRegular
