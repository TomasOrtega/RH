import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

/- English proof (translation)
Introduce `D H l₂ Q hM hnot`. Establish `hprod : l₂.Mb * l₂.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Q.asIdeal`. Rewrite using `[l₂.prod, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hM`. Break down `Ideal.IsPrime.mul_le Q.isPrime |>.1 hprod with h | h` into its components or cases.

Conclude with `absurd h hnot`. Rewrite `h` using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Establish `hx'` using `h hx`. Use `show Formalism.L2.DIV.starOHom x ∈ Q.asIdeal`.

Establish `e : Formalism.L2.DIV.starOHom x = (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `hb` using `H.bar_eq x`. Simplify using `only [RingEquiv.coe_toRingHom] at hb ⊢`. Rewrite using `[hb]`.

Conclude with `Formalism.L2.DIV.starO_coe x`. Rewrite using `[e]`. Conclude with `hx'`.
-/
theorem mb_le_conjPl_of_not_le : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (Q : Formalism.L2.DIV.Pl D.host.E), ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ¬ l₂.Mb ≤ Q.asIdeal → l₂.Mb ≤ (Formalism.L2.DIV.conjPl Q).asIdeal := by
  intro D H l₂ Q hM hnot
  have hprod : l₂.Mb * l₂.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Q.asIdeal := by
    rw [l₂.prod, Ideal.span_le, Set.singleton_subset_iff]; exact hM
  rcases Ideal.IsPrime.mul_le Q.isPrime |>.1 hprod with h | h
  · exact absurd h hnot
  · rw [Ideal.map_le_iff_le_comap] at h
    intro x hx
    have hx' := h hx
    show Formalism.L2.DIV.starOHom x ∈ Q.asIdeal
    have e : Formalism.L2.DIV.starOHom x = (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) x := by
      apply RingOfIntegers.ext
      have hb := H.bar_eq x
      simp only [RingEquiv.coe_toRingHom] at hb ⊢
      rw [hb]
      exact Formalism.L2.DIV.starO_coe x
    rw [e]; exact hx'

end GlobalTheory.LevelSeries
