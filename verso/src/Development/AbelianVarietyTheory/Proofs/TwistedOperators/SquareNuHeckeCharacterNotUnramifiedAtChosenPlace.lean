import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Introduce `hnu`. Establish `hunder : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0` using `G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))`. Establish `hnotS1 : G.pl.v0 ∉ S1 D` using `G.ch.basePlace_not_mem_chiGridBadPlaces`. Establish `hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → PP.under (𝓞 D.host.F) ≠ (G.pl.w G.pl.v0).under (𝓞 D.host.F)`. Introduce `PP hPP`.

Rewrite using `[hunder]`. Break down `hPP with hP | hP` into its components or cases. Introduce `heq`. Apply `hnotS1` to reduce the goal to its premises. Take `⟨k, hk⟩` from `(hL.Pg PP).1 hP`.

Establish `hmem` using `GlobalTheory.LevelPlaces.mem_of_div L.C.P k PP hk`. Establish `hF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal`. Simplify using `using hmem`. Rewrite using `[← heq, S1_mem_OmF]`. Use `fin_cases k`.

Conclude with `Or.inl hF`. Conclude with `Or.inr (Or.inl hF)`. Conclude with `G.pl.levelPlace_ne_basePlace t PP hP`. Take `⟨hxi, hmu⟩` from `(GlobalTheory.levCh_unramified_places D T L μ₀ hL t).2.2.2 _ hoff`. Establish `hchi` using `(G.ch.lev0 (D.R.m - i) (by omega) (by omega) _ hunder).2`.

Apply `hchi` to reduce the goal to its premises. Introduce `x hx`. Establish `h` using `hnu x hx`. Simplify using `only [SqNum.nuH, div_eq_mul_inv, HChar.loc_mul, HChar.loc_inv, hmu j x hx, hxi x hx, one_mul] at h`. Conclude with `inv_eq_one.mp h`.
-/
theorem squareNuHeckeCharacter_not_unramified_at_chosenPlace {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ¬ (SqNum.nuH G t i j).UnrAt (G.pl.w G.pl.v0) := by
  intro hnu

  have hunder : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 :=
    G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hnotS1 : G.pl.v0 ∉ S1 D := G.ch.basePlace_not_mem_chiGridBadPlaces

  have hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t →
      PP.under (𝓞 D.host.F) ≠ (G.pl.w G.pl.v0).under (𝓞 D.host.F) := by
    intro PP hPP
    rw [hunder]
    rcases hPP with hP | hP
    · intro heq
      apply hnotS1
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
      have hmem := GlobalTheory.LevelPlaces.mem_of_div L.C.P k PP hk
      have hF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
        simpa using hmem
      rw [← heq, S1_mem_OmF]
      fin_cases k
      · exact Or.inl hF
      · exact Or.inr (Or.inl hF)
    · exact G.pl.levelPlace_ne_basePlace t PP hP
  obtain ⟨hxi, hmu⟩ := (GlobalTheory.levCh_unramified_places D T L μ₀ hL t).2.2.2 _ hoff

  have hchi := (G.ch.lev0 (D.R.m - i) (by omega) (by omega) _ hunder).2
  apply hchi
  intro x hx
  have h := hnu x hx
  simp only [SqNum.nuH, div_eq_mul_inv, HChar.loc_mul, HChar.loc_inv, hmu j x hx, hxi x hx, one_mul] at h
  exact inv_eq_one.mp h

end GlobalTheory.RowTest

end
