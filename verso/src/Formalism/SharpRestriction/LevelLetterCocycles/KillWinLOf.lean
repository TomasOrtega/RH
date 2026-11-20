import Formalism.SharpRestriction.LevelLetterCocycles.ExistsGammaPi0EqPi0Mul
import Formalism.SharpRestriction.LevelLetterCocycles.LocalInputsFromLiterature
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

/- English proof (translation)
Introduce `l _ K LL hG hCA h5`. Take `⟨⟨hdom, -, -⟩, -⟩` from `Formalism.MainNotions.N.T2.litGoodO l LL`. Use `haveI := hdom`. Establish `: FiniteDimensional ℚ_[l] ↥(K0 K)` using `((D.loc l).PD K).finK₀`. Use `haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩`.

Establish `hR : ToolsR.RingP ((HW l).W K 1 LL hG)` using `ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA`. Establish `hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hG)` using `tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5`. Establish `hV` using `Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL`. Establish `hvp : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (((((D.loc l).PD K).p : ℕ) : ↥(OL LL)))) = 1`. Rewrite using `[map_natCast, (D.loc l).PD_p K]`.

Conclude with `(D.loc l).v_l LL`. Establish `hKL` using `hAdm.2.1 l K LL hG hCA h5`. Conclude with `Formalism.MainNotions.UnusedSlot80.KWP.killWinFromCut ((HW l).W K 1 LL hG) hV.1 hV.2.1 hvp hR hKL (Formalism.MainNotions.UnusedSlot80.KF.psStable_of _ hR) hR.1 (Formalism.MainNotions.UnusedSlot80.RatW.ratCore_of _ hR hT hR.2.2.1 hR.1) (hInv l K LL hG hCA h5)`.
-/
theorem killWinL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG)) :
    KillWinL D HW := by
  intro l _ K LL hG hCA h5
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hR : ToolsR.RingP ((HW l).W K 1 LL hG) := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hG) := tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hvp : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (((((D.loc l).PD K).p : ℕ) : ↥(OL LL)))) = 1 := by
    rw [map_natCast, (D.loc l).PD_p K]; exact (D.loc l).v_l LL
  have hKL := hAdm.2.1 l K LL hG hCA h5
  exact Formalism.MainNotions.UnusedSlot80.KWP.killWinFromCut ((HW l).W K 1 LL hG) hV.1 hV.2.1 hvp hR hKL
    (Formalism.MainNotions.UnusedSlot80.KF.psStable_of _ hR) hR.1
    (Formalism.MainNotions.UnusedSlot80.RatW.ratCore_of _ hR hT hR.2.2.1 hR.1) (hInv l K LL hG hCA h5)

end Formalism.MainNotions.UnusedSlot80
