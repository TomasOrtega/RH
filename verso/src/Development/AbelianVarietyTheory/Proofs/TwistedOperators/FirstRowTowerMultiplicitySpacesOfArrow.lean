import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

/- English proof (translation)
Introduce `hmod hstep D q hs T L μ0 hL sc hc G W M hM M₀ h₀ n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `h`. Use `⟨parB (Ptw D) 0, M₀, (parRow_zero D sc.cGap).symm, h₀, fun _ w => w, fun t ht Φ => ⟨t, ht, fun ρ w => ⟨trivial, rfl⟩⟩⟩` and prove the remaining obligations.

Consider the case `succ n ih`. Introduce `h`. Take `⟨S, MA, hS, hA, vec, hvec⟩` from `ih (Nat.le_of_succ_le h)`. Take `⟨MB, hB⟩` from `hmod D q hs T L μ0 hL sc hc G W M hM (n + 1) h`. Take `⟨It, hIt⟩` from `hstep D q hs T L μ0 hL sc hc G W M hM n h S _ MA MB hS rfl hA hB`.

Use `⟨_, MB, rfl, hB, fun ρ w => It (ρ ⟨n, h⟩) (vec ρ w), fun t ht Φ => ?_⟩` and prove the remaining obligations. Take `⟨F, hF, hF'⟩` from `hvec t ht Φ`. Take `⟨F', hF1, hF2⟩` from `hIt F hF (Φ ⟨n, h⟩)`. Use `⟨F', hF1, fun ρ w => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hF' ρ w`.

Take `⟨h3, h4⟩` from `hF2 (ρ ⟨n, h⟩) (vec ρ w)`. Rewrite `h3`, `h4` using `[← h2]`. Conclude with `⟨⟨h1, h3⟩, h4⟩`.
-/
theorem rowTower_of_step : RowModels → RowStep → RowTower := by
  intro hmod hstep D q hs T L μ0 hL sc hc G W M hM M₀ h₀ n
  induction n with
  | zero =>
    intro h
    refine ⟨parB (Ptw D) 0, M₀, (parRow_zero D sc.cGap).symm, h₀, fun _ w => w, fun t ht Φ => ⟨t, ht, fun ρ w => ⟨trivial, rfl⟩⟩⟩
  | succ n ih =>
    intro h
    obtain ⟨S, MA, hS, hA, vec, hvec⟩ := ih (Nat.le_of_succ_le h)
    obtain ⟨MB, hB⟩ := hmod D q hs T L μ0 hL sc hc G W M hM (n + 1) h
    obtain ⟨It, hIt⟩ := hstep D q hs T L μ0 hL sc hc G W M hM n h S _ MA MB hS rfl hA hB
    refine ⟨_, MB, rfl, hB, fun ρ w => It (ρ ⟨n, h⟩) (vec ρ w), fun t ht Φ => ?_⟩
    obtain ⟨F, hF, hF'⟩ := hvec t ht Φ
    obtain ⟨F', hF1, hF2⟩ := hIt F hF (Φ ⟨n, h⟩)
    refine ⟨F', hF1, fun ρ w => ?_⟩
    obtain ⟨h1, h2⟩ := hF' ρ w
    obtain ⟨h3, h4⟩ := hF2 (ρ ⟨n, h⟩) (vec ρ w)
    rw [← h2] at h3 h4
    exact ⟨⟨h1, h3⟩, h4⟩

end GlobalTheory.SepRows
