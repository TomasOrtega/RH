import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdC
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasuresStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_eq (x : AF F) : fstA F x = x.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem snd_eq (x : AF F) : sndA F x = x.2 := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idF_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε.1 = 1 := hε.1

open Classical in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idF_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) (v : HeightOneSpectrum (𝓞 F)) :
    ε.2 v = if v ∈ S then 1 else 0 := hε.2 v

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem idF_mul {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε * ε = ε := by
  classical
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_)
  · change ε.1 * ε.1 = ε.1
    rw [idF_fst hε, one_mul]
  · change ε.2 v * ε.2 v = ε.2 v
    rw [idF_snd hε v]
    split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem ker_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0) :
    y.1 = 0 := by
  have h : (ε * y).1 = 0 := by rw [hy]; rfl
  change ε.1 * y.1 = 0 at h
  rwa [idF_fst hε, one_mul] at h

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem ker_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : y.2 v = 0 := by
  classical
  have h : (ε * y).2 v = 0 := by rw [hy]; rfl
  change ε.2 v * y.2 v = 0 at h
  rwa [idF_snd hε v, if_pos hv, one_mul] at h

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem fix_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {h : AF F} (hh : ε * h = h)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : h.2 v = 0 := by
  classical
  have h' : (ε * h).2 v = h.2 v := by rw [hh]
  change ε.2 v * h.2 v = h.2 v at h'
  rw [idF_snd hε v, if_neg hv, zero_mul] at h'
  exact h'.symm

/- English proof (translation)
Chain the equalities or inequalities of the calculation.
-/
theorem fix_mul_ker {ε h y : AF F} (hε : ε * ε = ε) (hh : ε * h = h) (hy : ε * y = 0) : h * y = 0 := by
  calc h * y = (ε * h) * y := by rw [hh]
    _ = h * (ε * y) := by ring
    _ = 0 := by rw [hy, mul_zero]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
