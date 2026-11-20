import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPowUnitsOfUnderEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RamQ

/- English proof (translation)
Take `⟨htw, hq, -⟩` from `GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host X.B.fields.K X.B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)`. Rewrite using `[hq]`. Use `⟨fun h => ⟨PP, rfl, h⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨P, hP, hn⟩ hu`. Apply `hn` to reduce the goal to its premises.

Introduce `x hx`. Establish `h1` using `GlobalTheory.Mem.Chr.twist_pow_units_of_under_eq X.B.R X.B.host I.S (I.xi a) htw P PP hP 1 (fun y hy => by rw [pow_one]; exact hu y hy) x hx`. Simplify using `using h1`.
-/
theorem not_unr_iff_under_mem (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
  obtain ⟨htw, hq, -⟩ := GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host X.B.fields.K X.B.embLL I.S (I.tup a) (I.xi a)
    (hI.xi_reads a)
  rw [hq]
  refine ⟨fun h => ⟨PP, rfl, h⟩, ?_⟩
  rintro ⟨P, hP, hn⟩ hu
  apply hn
  intro x hx
  have h1 := GlobalTheory.Mem.Chr.twist_pow_units_of_under_eq X.B.R X.B.host I.S (I.xi a) htw P PP hP 1
    (fun y hy => by rw [pow_one]; exact hu y hy) x hx
  simpa using h1

/- English proof (translation)
Rewrite using `[not_unr_iff_under_mem X px I hI a PP]`. Establish `hf` using `Formalism.L2.DIV.auxiliary_primes_finite X.B.fields.F X.B.fields.E X.B.fields.K (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) (I.tup a).2.1.1.1.1.2`. Establish `hsel : ∀ v, (I.sel v).under (𝓞 X.B.fields.F) = v` using `fun v => HeightOneSpectrum.ext (hI.sel_ok v)`. Establish `memQ : ∀ v ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K), I.sel v ∈ I.Q a` using `fun v hv => by`. Unfold `ColIn.Q`.

Rewrite using `[Formalism.L2.Col.QE, dif_pos hf]`. Conclude with `Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hv)`. Establish `under_of_mem : ∀ P ∈ I.Q a, P.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K)` using `fun P hP => by`. Take `⟨v, hv, hs, -⟩` from `ColIn.exists_of_mem_Q I hP`. Rewrite using `[← hs, hsel]`.

Conclude with `hv`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `key : ∀ Q P : Pl X.toD7.host.E, Q.under (𝓞 X.toD7.host.F) = P.under (𝓞 X.toD7.host.F) → Q = P ∨ Q = Formalism.DivisionValues.conjPl P` using `fun Q P h => GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h`. Establish `e : PP.under (𝓞 X.B.host.F) = (I.sel (PP.under (𝓞 X.B.host.F))).under (𝓞 X.B.fields.F)` using `(hsel _).symm`.

Break down `key PP (I.sel (PP.under (𝓞 X.B.host.F))) e with h | h` into its components or cases. Use `left`. Rewrite using `[h]`. Conclude with `memQ _ hv`. Use `right`.

Conclude with `⟨_, memQ _ hv, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩`. Introduce and unpack `(h | ⟨PP', h, hc⟩)`. Conclude with `under_of_mem _ h`. Establish `e : PP'.under (𝓞 X.B.host.F) = PP.under (𝓞 X.B.host.F)` using `GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc`. Rewrite using `[← e]`.

Conclude with `under_of_mem _ h`.
-/
theorem tupleTwist_ramified_iff_chosenPrime_or_conj_host (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP := by
  classical
  rw [not_unr_iff_under_mem X px I hI a PP]
  have hf := Formalism.L2.DIV.auxiliary_primes_finite X.B.fields.F X.B.fields.E X.B.fields.K (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K)
    (I.tup a).2.1.1.1.1.2
  have hsel : ∀ v, (I.sel v).under (𝓞 X.B.fields.F) = v := fun v => HeightOneSpectrum.ext (hI.sel_ok v)
  have memQ : ∀ v ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K), I.sel v ∈ I.Q a := fun v hv => by
    unfold ColIn.Q
    rw [Formalism.L2.Col.QE, dif_pos hf]
    exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hv)
  have under_of_mem : ∀ P ∈ I.Q a, P.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) :=
    fun P hP => by
      obtain ⟨v, hv, hs, -⟩ := ColIn.exists_of_mem_Q I hP
      rw [← hs, hsel]
      exact hv
  constructor
  · intro hv
    have key : ∀ Q P : Pl X.toD7.host.E, Q.under (𝓞 X.toD7.host.F) = P.under (𝓞 X.toD7.host.F) →
        Q = P ∨ Q = Formalism.DivisionValues.conjPl P := fun Q P h => GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have e : PP.under (𝓞 X.B.host.F) = (I.sel (PP.under (𝓞 X.B.host.F))).under (𝓞 X.B.fields.F) := (hsel _).symm
    rcases key PP (I.sel (PP.under (𝓞 X.B.host.F))) e with h | h
    · left
      rw [h]
      exact memQ _ hv
    · right
      exact ⟨_, memQ _ hv, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  · rintro (h | ⟨PP', h, hc⟩)
    · exact under_of_mem _ h
    · have e : PP'.under (𝓞 X.B.host.F) = PP.under (𝓞 X.B.host.F) := GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      rw [← e]
      exact under_of_mem _ h

/- English proof (translation)
Introduce `X px I hI a PP` and use `tupleTwist_ramified_iff_chosenPrime_or_conj_host X px I hI a PP`.
-/
theorem ram_iff : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (a : I.ι) (PP : Pl X.toD7.host.E),
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP :=
  fun X px I hI a PP => tupleTwist_ramified_iff_chosenPrime_or_conj_host X px I hI a PP

end GlobalTheory.Mem.Col2.RamQ

end
