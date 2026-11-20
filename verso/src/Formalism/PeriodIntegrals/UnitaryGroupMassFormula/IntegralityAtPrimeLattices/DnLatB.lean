import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.UpLatLoc0Of
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DnLatKer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DnIncInt0Of

noncomputable section

open NumberField Ideal Matrix IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.UG

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Introduce `w hw hs v c g hg γ η κ hη hy hP B B' B₂ hB hB' hB₂ τ`. Use `split_ifs with hτ`. Substitute `hτ` using the available equality. Establish `hk` using `lk_locP T.atT T.cls0 v c`. Use `intInv_of_loc T.atT w hw hs v B₂ B' γ.1 hB₂ hB' ?_ ?_` and prove the remaining obligations.

Rewrite using `[hP, ← hk]`. Conclude with `le_locP' _ _`. Rewrite using `[hk, ← hP]`. Conclude with `le_locP' _ _`. Take `⟨v', rfl⟩ : ∃ v', (D.fm u).tauOf w v' = τ` from `⟨((D.fm u).tauOf w).symm τ, by simp⟩`.

Establish `hv' : v' ≠ v` using `fun h => hτ (h ▸ rfl)`. Establish `hA'` using `hA v v' hv' c ((D.fm u).dn 0 v c g) γ η κ hη hy`. Use `intInv_of_loc T.atT w hw hs v' B₂ B γ.1 hB₂ hB ?_ ?_` and prove the remaining obligations. Rewrite using `[hA']`. Conclude with `le_locP' _ _`.

Rewrite using `[← hA']`. Conclude with `le_locP' _ _`.
-/
theorem dnLatLoc0_of_away (T : Forms0 D u) (hA : AwayLat0 T) : DnLatLoc0 T := by
  intro w hw hs v c g hg γ η κ hη hy hP B B' B₂ hB hB' hB₂ τ
  split_ifs with hτ
  · subst hτ
    have hk := lk_locP T.atT T.cls0 v c
    refine intInv_of_loc T.atT w hw hs v B₂ B' γ.1 hB₂ hB' ?_ ?_
    · rw [hP, ← hk]
      exact le_locP' _ _
    · rw [hk, ← hP]
      exact le_locP' _ _
  · obtain ⟨v', rfl⟩ : ∃ v', (D.fm u).tauOf w v' = τ := ⟨((D.fm u).tauOf w).symm τ, by simp⟩
    have hv' : v' ≠ v := fun h => hτ (h ▸ rfl)
    have hA' := hA v v' hv' c ((D.fm u).dn 0 v c g) γ η κ hη hy
    refine intInv_of_loc T.atT w hw hs v' B₂ B γ.1 hB₂ hB ?_ ?_
    · rw [hA']
      exact le_locP' _ _
    · rw [← hA']
      exact le_locP' _ _

end PI.UnitaryGroupMassFormula.IAT

end
