import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

namespace GlobalTheory.UnderConj
open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

/- English proof (translation)
Introduce `D PP PP' hu hne`. Establish `key : PP' = conjSpec PP`. Assume the negation of the conclusion as `hc`. Take `⟨x, hx, hx1, hx2⟩` from `exists_mem_not_mem (Q := PP') (P := PP) (P' := conjSpec PP) (Ne.symm hne) hc`. Establish `hfix : star ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E)`.

Express the relevant statement in the definitionally equal form `star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)`. Rewrite using `[star_mul, star_star]`. Take `⟨a, ha⟩` from `(D.sp.cm.fixed _).1 hfix`. Establish `hint : IsIntegral ℤ a`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective, ha]`.

Conclude with `(x * Formalism.L2.Col.cO D.host.E x).isIntegral_coe`. Establish `e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ = x * Formalism.L2.Col.cO D.host.E x` using `RingOfIntegers.ext ha`. Establish `h1 : (⟨a, hint⟩ : 𝓞 D.host.F) ∈ (PP'.under (𝓞 D.host.F)).asIdeal`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP'.asIdeal`. Rewrite using `[e]`.

Conclude with `Ideal.mul_mem_right _ _ hx`. Rewrite `h1` using `[← hu]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP.asIdeal at h1`. Rewrite `h1` using `[e]`. Break down `PP.isPrime.mem_or_mem h1 with h | h` into its components or cases.

Conclude with `hx1 h`. Conclude with `hx2 h`. Rewrite using `[key]`. Conclude with `GlobalTheory.LevelPlaces.isConjPl_conjSpec PP`.
-/
theorem isConjPl_of_under_eq_of_ne : ∀ (D : D7) (PP PP' : Pl D.host.E), PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) →
    PP ≠ PP' → Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro D PP PP' hu hne
  have key : PP' = conjSpec PP := by
    by_contra hc
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem (Q := PP') (P := PP) (P' := conjSpec PP) (Ne.symm hne) hc
    have hfix : star ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) := by
      change star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul, star_star]
    obtain ⟨a, ha⟩ := (D.sp.cm.fixed _).1 hfix
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective, ha]
      exact (x * Formalism.L2.Col.cO D.host.E x).isIntegral_coe
    have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ = x * Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext ha
    have h1 : (⟨a, hint⟩ : 𝓞 D.host.F) ∈ (PP'.under (𝓞 D.host.F)).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP'.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    rw [← hu] at h1
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP.asIdeal at h1
    rw [e] at h1
    rcases PP.isPrime.mem_or_mem h1 with h | h
    · exact hx1 h
    · exact hx2 h
  rw [key]
  exact GlobalTheory.LevelPlaces.isConjPl_conjSpec PP

end GlobalTheory.UnderConj
