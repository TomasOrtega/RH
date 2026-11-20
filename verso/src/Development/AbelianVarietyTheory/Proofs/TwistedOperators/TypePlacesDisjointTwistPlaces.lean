import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistPlaces

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hC t`. Establish `hL` using `hC.lev`. Rewrite using `[Finset.disjoint_left]`. Introduce `PP hPg hQ`. Take `⟨k, hk⟩` from `(hL.Pg PP).1 hPg`.

Take `⟨⟨q, hq, hcard, -, hne⟩, -⟩` from `hL.Q_pl t PP hQ`. Establish `hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal`. Establish `h` using `R.C.P.pb_over k`. Establish `hk' : PP.under (𝓞 D.host.K) = R.C.P.pb k` using `hk`. Rewrite using `[hk']`.

Conclude with `h`. Establish `hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`. Establish `h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal` using `hmemK`. Simplify using `using h2`. Use `haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)`.

Establish `: PP.asIdeal.IsPrime` using `PP.isPrime`. Use `haveI : Nontrivial (kP PP) := inferInstance`. Use `haveI : Fintype (kP PP) := Fintype.ofFinite _`. Establish `h0g : ((D.host.g k : ℕ) : kP PP) = 0`. Use `(Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hmemE` as an intermediate fact.

Simplify using `using this`. Establish `h0q : ((q : ℕ) : kP PP) = 0`. Rewrite using `[← hcard, Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero (kP PP)`. Establish `hd1 : ringChar (kP PP) ∣ D.host.g k` using `ringChar.dvd h0g`.

Establish `hd2 : ringChar (kP PP) ∣ q` using `ringChar.dvd h0q`. Establish `hcop : Nat.Coprime q (D.host.g k)` using `(Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)`. Establish `h1 : ringChar (kP PP) = 1` using `Nat.eq_one_of_dvd_coprimes hcop hd2 hd1`. Conclude with `CharP.ringChar_ne_one h1`.
-/
theorem typePlaces_disjoint_twistPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  rw [Finset.disjoint_left]
  intro PP hPg hQ
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := R.C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = R.C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : PP.asIdeal.IsPrime := PP.isPrime
  haveI : Nontrivial (kP PP) := inferInstance
  haveI : Fintype (kP PP) := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hmemE
    simpa using this
  have h0q : ((q : ℕ) : kP PP) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP PP)
  have hd1 : ringChar (kP PP) ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP PP) ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP PP) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1

end GlobalTheory.TwistPlaces
