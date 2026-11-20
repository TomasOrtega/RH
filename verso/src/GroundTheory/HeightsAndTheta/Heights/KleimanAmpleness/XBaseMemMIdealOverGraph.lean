import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

section Zero

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
Rewrite using `[Kleiman.primeOf_eq, RingHom.mem_ker]`. Simplify using `[Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, hi]`.
-/
theorem X_mem_primeOf_of_eq_zero {i : Fin (N + 1)} (hi : x i = 0) :
    (X i : Kleiman.Poly S N) ∈ Kleiman.primeOf (S := S) x := by
  rw [Kleiman.primeOf_eq, RingHom.mem_ker]
  simp [Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, hi]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `mConeMapOver S (graphVec x s) (X _) = 0`. Simplify using `[mConeMapOver, hi]`.
-/
theorem X_base_mem_mIdealOver_graph (s : Fin m → Ω) {i : Fin (N + 1)} (hi : x i = 0) :
    (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) S) ∈ mIdealOver S (graphVec x s) := by
  change mConeMapOver S (graphVec x s) (X _) = 0
  simp [mConeMapOver, hi]

end Zero

/- English proof (translation)
Introduce `k _ N Ω _ _ x Q n m s hgen`. Distinguish the cases in `hx : ∃ i, x i ≠ 0`. Prove the components needed by the constructor for the conclusion. Introduce `hnef W hW hle hrel`. Establish `hsub` using `(hC k N Ω x Q n m s hx hgen W hW hle 1).mp hrel`.

Rewrite using `[hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]`. Conclude with `hnef _ bot_le hsub`. Introduce `hnef pp _ hsub`. Take `⟨W, hW, hle, rfl⟩` from `hL k N Ω x Q n m s hx hgen pp 1 hsub`. Rewrite using `[← hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]`.

Conclude with `hnef W hW hle ((hC k N Ω x Q n m s hx hgen W hW hle 1).mpr hsub)`. Use `push Not at hx`. Prove the components needed by the constructor for the conclusion. Introduce `_ W hW hle _`. It suffices to derive a contradiction.

Take `⟨i, hi⟩` from `hW.relevant baseBlock`. Conclude with `hi (hle (X_base_mem_mIdealOver_graph s (hx i)))`. Introduce `_ pp _ hsub`. It suffices to derive a contradiction. Take `⟨i, hi⟩` from `hsub.relevant`.

Conclude with `hi (hsub.le (X_mem_primeOf_of_eq_zero (hx i)))`.
-/
theorem NefEq.proof (hC : CurveComap.Statement) (hL : CurveLift.Statement) (hD : DegEq.Statement) :
    NefEq.Statement := by
  intro k _ N Ω _ _ x Q n m s hgen
  by_cases hx : ∃ i, x i ≠ 0
  · constructor
    · intro hnef W hW hle hrel
      have hsub := (hC k N Ω x Q n m s hx hgen W hW hle 1).mp hrel
      rw [hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]
      exact hnef _ bot_le hsub
    · intro hnef pp _ hsub
      obtain ⟨W, hW, hle, rfl⟩ := hL k N Ω x Q n m s hx hgen pp 1 hsub
      rw [← hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]
      exact hnef W hW hle ((hC k N Ω x Q n m s hx hgen W hW hle 1).mpr hsub)
  · push Not at hx
    constructor
    · intro _ W hW hle _
      exfalso
      obtain ⟨i, hi⟩ := hW.relevant baseBlock
      exact hi (hle (X_base_mem_mIdealOver_graph s (hx i)))
    · intro _ pp _ hsub
      exfalso
      obtain ⟨i, hi⟩ := hsub.relevant
      exact hi (hsub.le (X_mem_primeOf_of_eq_zero (hx i)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
