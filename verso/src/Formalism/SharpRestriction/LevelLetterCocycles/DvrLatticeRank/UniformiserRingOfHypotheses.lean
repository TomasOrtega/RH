import Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

/- English proof (translation)
Unfold `adm1 Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeLocal at h1`. Introduce `l _ hl K LL hG T hT`. Establish `h9` using `(h1 l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT`. Unfold `Formalism.MainNotions.DeltaInvariantLattices.p9 at h9`. Establish `hpe : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`.

Establish `hs : ((HW l).W K 1 LL hG).s = 1` using `by first`. Consider the case `exact (HW l).W_s K 1 LL hG`. Consider the case `exact (HW l).hs K 1 LL hG`. Consider the case `exact (HW l).s_eq K 1 LL hG`. Consider the case `exact (HW l).W_s`.

Consider the case `rfl`. Take `⟨-, ⟨π', E, hr, -⟩, -⟩` from `h9 hs (by rw [hpe]; exact hl)`. Use `⟨π', E, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `convert hr using 2 <;> first | rfl | (simp only [eK, sK, hpe]) | (unfold eK sK; simp [hpe])`.
-/
theorem uniformiser_ring_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) : p9R D HW := by
  unfold adm1 Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeLocal at h1
  intro l _ hl K LL hG T hT
  have h9 := (h1 l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT
  unfold Formalism.MainNotions.DeltaInvariantLattices.p9 at h9
  have hpe : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs : ((HW l).W K 1 LL hG).s = 1 := by
    first
    | exact (HW l).W_s K 1 LL hG
    | exact (HW l).hs K 1 LL hG
    | exact (HW l).s_eq K 1 LL hG
    | exact (HW l).W_s
    | rfl
  obtain ⟨-, ⟨π', E, hr, -⟩, -⟩ := h9 hs (by rw [hpe]; exact hl)
  refine ⟨π', E, ?_⟩
  convert hr using 2 <;> first | rfl | (simp only [eK, sK, hpe]) | (unfold eK sK; simp [hpe])

end Formalism.MainNotions.N.Ln34

end
