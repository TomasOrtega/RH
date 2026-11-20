import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem good_twists_condition (D : D7) (N : NChoice D) (I : Formalism.MainNotions.TwIn D) (h : Formalism.MainNotions.TwGoodAt D N I) :
    Formalism.MainNotions.LocalQuadraticParts.TwistConductorsSplit D N := by
  classical
  intro w hw v hv
  obtain ⟨hs, hd, -⟩ := (h w hw).2.1
  refine ⟨(hs v hv).1, fun hp => ?_⟩
  have h0 : v ∈ D.ntw.S0 (N.twI w) := by
    have h1 := D.ntw.twistExcludedPlaces_contains_residueChar (N.twI w)
    rw [N.twI_l w] at h1
    exact_mod_cast h1 hp
  exact Finset.disjoint_left.mp hd hv (Finset.mem_union_left _ h0)

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem family_good_twists_condition {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TwGood Fm) : Formalism.MainNotions.LocalQuadraticParts.TwistConductorsFamily Fm := by
  obtain ⟨x0, H⟩ := h
  refine ⟨x0, fun x hx0 hx i => ?_⟩
  obtain ⟨-, N0, S, hG⟩ := H x hx0 hx i
  exact good_twists_condition _ _ _ hG

end Formalism.MainNotions.J

end
