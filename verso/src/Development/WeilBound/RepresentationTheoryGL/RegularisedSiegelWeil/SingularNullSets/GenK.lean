import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKI
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.DyadicFin

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

/- English proof (translation)
Introduce `D n`. Take `⟨S₀, hS₀⟩` from `LGenK.dyadic_fin D`. Use `⟨S₀, fun S hS A _ h1 hgen k hk => ?_⟩` and prove the remaining obligations. Establish `hS2 : ∀ v ∉ S, (2 : 𝓞 D.host.F) ∉ v.asIdeal` using `fun v hv h2 => hv (hS (hS₀ v h2))`. Take `⟨g1, g2, g3, g4, rfl, m1, n1, m2, i2, m3, w3, m4, n4⟩` from `LGenK.factor hS2 hk`.

Establish `a4` using `hgen g4 m4 (Or.inl n4) 1 h1`. Establish `a3` using `hgen g3 m3 (Or.inr (Or.inr w3)) _ a4`. Establish `a2` using `hgen g2 m2 (Or.inr (Or.inl i2)) _ a3`. Establish `a1` using `hgen g1 m1 (Or.inl n1) _ a2`. Simplify `a1` using `only [mul_one]`.
-/
theorem genK : GenK := by
  intro D n
  obtain ⟨S₀, hS₀⟩ := LGenK.dyadic_fin D
  refine ⟨S₀, fun S hS A _ h1 hgen k hk => ?_⟩
  have hS2 : ∀ v ∉ S, (2 : 𝓞 D.host.F) ∉ v.asIdeal := fun v hv h2 => hv (hS (hS₀ v h2))
  obtain ⟨g1, g2, g3, g4, rfl, m1, n1, m2, i2, m3, w3, m4, n4⟩ := LGenK.factor hS2 hk
  have a4 := hgen g4 m4 (Or.inl n4) 1 h1
  have a3 := hgen g3 m3 (Or.inr (Or.inr w3)) _ a4
  have a2 := hgen g2 m2 (Or.inr (Or.inl i2)) _ a3
  have a1 := hgen g1 m1 (Or.inl n1) _ a2
  simpa only [mul_one] using a1

end PositivityTheory.Rg.Rsw.L
