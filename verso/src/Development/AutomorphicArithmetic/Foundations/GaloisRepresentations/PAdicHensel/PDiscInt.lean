import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Coordinates
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PDiscInt

noncomputable section

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.G1

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem int_of_rat (z : 𝓞 E) (q : ℚ) (h : algebraMap (𝓞 E) E z = (q : E)) : ∃ n : ℤ, q = n := by
  have h1 : IsIntegral ℤ (algebraMap ℚ E q) := by
    have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E z) := RingOfIntegers.isIntegral_coe z
    rw [h] at h0
    simpa using h0
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨n, by simpa using hn.symm⟩

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem tr_coe (A : Arith E) : (A.ω : E) + (A.bar A.ω : 𝓞 E) = (A.tr : E) := by
  have h := congrArg (fun x : 𝓞 E => (x : E)) A.tr_eq
  simpa using h

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem nm_coe (A : Arith E) : (A.ω : E) * (A.bar A.ω : 𝓞 E) = (A.nm : E) := by
  have h := congrArg (fun x : 𝓞 E => (x : E)) A.nm_eq
  simpa using h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sq_coe (A : Arith E) : (A.ω : E) * A.ω = A.tr * A.ω - A.nm := by
  rw [← tr_coe A, ← nm_coe A]; ring

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem coords (A : Arith E) (z : E) (hz : z ∈ IntermediateField.adjoin ℚ {(A.ω : E)}) :
    ∃ α β : ℚ, z = (α : E) + (β : E) * A.ω :=
  _root_.UpperTheory.Reformulated.B.AdjoinSimpleRationalCoordinates.coords A z hz

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pDiscInt : DiscInt :=
  _root_.UpperTheory.Reformulated.B.Qk39.pDiscInt

end UpperTheory.Gal.G1
