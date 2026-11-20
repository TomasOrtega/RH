import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.TamePlaces

/- English proof (translation)
Introduce `P hP _`. Use `not_dvd_differentIdeal_iff.1 ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.DensityEuler.differentIdeal_eq_top D.sp.cm]`. Introduce `hd`. Conclude with `hP.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 hd))`.
-/
theorem extUnramAt (D : D7) (v : Pl D) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := by
  intro P hP _
  refine not_dvd_differentIdeal_iff.1 ?_
  rw [GlobalTheory.DensityEuler.differentIdeal_eq_top D.sp.cm]
  intro hd
  exact hP.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 hd))

/- English proof (translation)
Take `⟨e, he, hc, hs, -⟩` from `GlobalTheory.SplitIdem.exists_split_idempotent D v h2`. Establish `hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))` using `⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same D.host.F v 1, fun v' hv' => GlobalTheory.SplitIdem.evalV_singleV_ne D.host.F v 1 hv'⟩`. Conclude with `⟨e, _, ⟨he, hc, v, _, hε, hs⟩, hε, hs⟩`.
-/
theorem split_over_two (D : D7) (v : Pl D) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) :
    ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨e, he, hc, hs, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same D.host.F v 1,
      fun v' hv' => GlobalTheory.SplitIdem.evalV_singleV_ne D.host.F v 1 hv'⟩
  exact ⟨e, _, ⟨he, hc, v, _, hε, hs⟩, hε, hs⟩

/- English proof (translation)
Introduce `D v`. Use `⟨extUnramAt D v, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal`. Conclude with `Or.inr (split_over_two D v h2)`. Conclude with `Or.inl h2`.
-/
theorem tame : ∀ (D : D7) (v : Pl D), Tame D v := by
  intro D v
  refine ⟨extUnramAt D v, ?_⟩
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · exact Or.inr (split_over_two D v h2)
  · exact Or.inl h2

end GlobalTheory.FinPl.TamePlaces
