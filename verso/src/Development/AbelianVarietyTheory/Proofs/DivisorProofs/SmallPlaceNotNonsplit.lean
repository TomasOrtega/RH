import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAtSmallPlaces

/- English proof (translation)
Introduce `D T Lc sc G μ₀ _ _ v ε hε hv hns`. Take `⟨e, he⟩` from `G.pl.w_split v hv`. Establish `hb` using `Formalism.IndefR.Fin.below_of_idemAt he`. Establish `hbv : Formalism.IndefR.Fin.belowPl (G.pl.w v) = v`. Use `HeightOneSpectrum.ext ?_` and prove the remaining obligations.

Establish `a` using `congrArg HeightOneSpectrum.asIdeal (G.pl.under_w hv)`. Rewrite using `[← a]`. Both sides reduce to the same expression. Rewrite `hb` using `[hbv]`. Use `hns.2 ⟨e, he.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[hb, Formalism.IndefR.Fin.placeIdem_eq hε]`. Both sides reduce to the same expression.
-/
theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ G.pl.S0 →
      ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ _ _ v ε hε hv hns
  obtain ⟨e, he⟩ := G.pl.w_split v hv
  have hb := Formalism.IndefR.Fin.below_of_idemAt he
  have hbv : Formalism.IndefR.Fin.belowPl (G.pl.w v) = v := by
    refine HeightOneSpectrum.ext ?_
    have a := congrArg HeightOneSpectrum.asIdeal (G.pl.under_w hv)
    rw [← a]
    rfl
  rw [hbv] at hb
  refine hns.2 ⟨e, he.1, ?_⟩
  rw [hb, Formalism.IndefR.Fin.placeIdem_eq hε]
  rfl

end GlobalTheory.SplitAtSmallPlaces
