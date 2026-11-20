import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FrMemLetters
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics

/- English proof (translation)
Introduce `n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL s hs`. Establish `hr : 1 ≤ r` using `NeZero.pos r`. Take `⟨x0, hx0⟩` from `posTL_surj Fr hV hr hJ hnL s hs`. Use `⟨x0, hx0, fun x' hx' => ?_⟩` and prove the remaining obligations. Conclude with `posTL_inj Fr hV hr hJ hnL (hx'.trans hx0.symm)`.
-/
theorem geoTop : GeoTop := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL s hs
  have hr : 1 ≤ r := NeZero.pos r
  obtain ⟨x0, hx0⟩ := posTL_surj Fr hV hr hJ hnL s hs
  refine ⟨x0, hx0, fun x' hx' => ?_⟩
  exact posTL_inj Fr hV hr hJ hnL (hx'.trans hx0.symm)

/- English proof (translation)
Introduce `n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL x0 j u hu hx`. Establish `hr : 1 ≤ r` using `NeZero.pos r`. Establish `hu' : u < (Fr.LLset (segZ j)).card + r` using `by rw [← hnL]; exact hu`. Unfold `touchT`. Break down `hx with (⟨l, hl, hlt⟩ | ⟨m, hm, hlt⟩) | ⟨m, hm⟩` into its components or cases.

Substitute `hl` using the available equality. Establish `hl' : l.val < (Fr.LLset (segZ j)).card` using `by rw [← hnL]; exact l.isLt`. Use `⟨llPos Fr (segZ j) l.val, (LL_sub_letters hV hr _ _ (llPos_mem Fr (segZ j) l.val hl')).1, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← posU_ll (Fr := Fr) (segZ j) l.val hl']`. Conclude with `(posU_le_iff hV (segZ j) _ _ (by omega) hu').2 (by omega)`.

Substitute `hm` using the available equality. Establish `hm'` using `m.isLt`. Use `⟨Fr.fr (segZ j) (r - 1 - m.val), fr_mem_letters hV hr _ _ (by omega), rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← posU_fr (Fr := Fr) (segZ j) (r - 1 - m.val)]`. Use `(posU_le_iff hV (segZ j) _ _ (by omega) hu').2 ?_` and prove the remaining obligations.

Rewrite using `[← hnL]`. Use linear arithmetic over natural numbers and integers. Substitute `hm` using the available equality. Establish `hm'` using `m.isLt`. Take `⟨s, hs, hsh⟩` from `DdG.shift Fr hV.2.1 hJ (j - 1)`.

Rewrite `hsh` using `[sub_add_cancel]`. Use `⟨Fr.fr (segZ j - 1) (r - 1 - m.val), w_mem_letters hV hr _ _ (by omega), ?_, (w_lt_posU hV hr _ _ _ (by omega) hu').le⟩` and prove the remaining obligations. Use `show _ = posOf n' (Fr.fr (segZ (j - 1)) (r - 1 - m.val))`. Rewrite using `[(hsh (r - 1 - m.val)).1]`. Break down `hs with rfl | rfl` into its components or cases.

Rewrite using `[add_zero]`. Rewrite using `[DdG.posOf_add_n]`.
-/
theorem geoTouch : GeoTouch := by
  intro n' r _ _ Fr L₁ N₁ hV J _ nL hJ hnL x0 j u hu hx
  have hr : 1 ≤ r := NeZero.pos r
  have hu' : u < (Fr.LLset (segZ j)).card + r := by rw [← hnL]; exact hu
  unfold touchT
  rcases hx with (⟨l, hl, hlt⟩ | ⟨m, hm, hlt⟩) | ⟨m, hm⟩
  · subst hl
    have hl' : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL]; exact l.isLt
    refine ⟨llPos Fr (segZ j) l.val, (LL_sub_letters hV hr _ _ (llPos_mem Fr (segZ j) l.val hl')).1, rfl, ?_⟩
    rw [← posU_ll (Fr := Fr) (segZ j) l.val hl']
    exact (posU_le_iff hV (segZ j) _ _ (by omega) hu').2 (by omega)
  · subst hm
    have hm' := m.isLt
    refine ⟨Fr.fr (segZ j) (r - 1 - m.val), fr_mem_letters hV hr _ _ (by omega), rfl, ?_⟩
    rw [← posU_fr (Fr := Fr) (segZ j) (r - 1 - m.val)]
    refine (posU_le_iff hV (segZ j) _ _ (by omega) hu').2 ?_
    rw [← hnL]
    omega
  · subst hm
    have hm' := m.isLt
    obtain ⟨s, hs, hsh⟩ := DdG.shift Fr hV.2.1 hJ (j - 1)
    rw [sub_add_cancel] at hsh
    refine ⟨Fr.fr (segZ j - 1) (r - 1 - m.val), w_mem_letters hV hr _ _ (by omega), ?_,
      (w_lt_posU hV hr _ _ _ (by omega) hu').le⟩
    show _ = posOf n' (Fr.fr (segZ (j - 1)) (r - 1 - m.val))
    rw [(hsh (r - 1 - m.val)).1]
    rcases hs with rfl | rfl
    · rw [add_zero]
    · rw [DdG.posOf_add_n]

end Formalism.MainNotions.PairMembershipBlocks
