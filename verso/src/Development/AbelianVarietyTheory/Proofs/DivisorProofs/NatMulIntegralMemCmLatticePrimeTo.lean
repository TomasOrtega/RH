import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatDen

/- English proof (translation)
Introduce `E _ _ l c y R hl hy hR hRc`. Take `⟨M, hM, hMz⟩` from `GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to E l ((y⁻¹ : (Af E)ˣ) : Af E) hl (fun w hw => by`. Establish `h1 : ((y⁻¹ : (Af E)ˣ) : Af E) w * (y : Af E) w = 1`. Establish `h` using `congrArg (fun a : Af E => a w) (Units.inv_mul y)`. Conclude with `h`.

Rewrite `h1` using `[hy w hw, mul_one]`. Rewrite using `[h1, map_one])`. Use `⟨M, hM, fun x hx => ?_⟩` and prove the remaining obligations. Use `show algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c`. Use `GlobalTheory.CMVal.LatEnt.mem_hatO_of_sub hR hRc (zero_mem _) fun P => ?_` and prove the remaining obligations.

Establish `e : (algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E)) P - (0 : Af E) P = (R : P.adicCompletion E) * (algebraMap E (P.adicCompletion E) x * (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P)`. Rewrite using `[show (0 : Af E) P = 0 from rfl, sub_zero, show (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P = algebraMap E (P.adicCompletion E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E) P from rfl]`. Use `show algebraMap E (P.adicCompletion E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) P = _`. Rewrite using `[map_mul, map_natCast, map_natCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hx1 : Valued.v (algebraMap E (P.adicCompletion E) x) ≤ 1`. Establish `h2 : Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x`. Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P]`. Both sides reduce to the same expression.

Rewrite using `[h2]`. Establish `: x = algebraMap (𝓞 E) E ⟨x, hx⟩` using `rfl`. Rewrite using `[this]`. Conclude with `P.valuation_le_one _`. Rewrite using `[e, map_mul, GlobalTheory.CMVal.LatEnt.radN, map_mul]`.

Conclude with `mul_le_of_le_one_right' (mul_le_one' hx1 (hMz P))`.
-/
theorem nat_mul_integral_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  intro E _ _ l c y R hl hy hR hRc
  obtain ⟨M, hM, hMz⟩ := GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to E l ((y⁻¹ : (Af E)ˣ) : Af E) hl (fun w hw => by
    have h1 : ((y⁻¹ : (Af E)ˣ) : Af E) w * (y : Af E) w = 1 := by
      have h := congrArg (fun a : Af E => a w) (Units.inv_mul y)
      exact h
    rw [hy w hw, mul_one] at h1
    rw [h1, map_one])
  refine ⟨M, hM, fun x hx => ?_⟩
  show algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c
  refine GlobalTheory.CMVal.LatEnt.mem_hatO_of_sub hR hRc (zero_mem _) fun P => ?_
  have e : (algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E)) P - (0 : Af E) P =
      (R : P.adicCompletion E) * (algebraMap E (P.adicCompletion E) x *
        (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P) := by
    rw [show (0 : Af E) P = 0 from rfl, sub_zero,
      show (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P =
        algebraMap E (P.adicCompletion E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E) P from rfl]
    show algebraMap E (P.adicCompletion E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) P = _
    rw [map_mul, map_natCast, map_natCast]
    push_cast
    ring
  have hx1 : Valued.v (algebraMap E (P.adicCompletion E) x) ≤ 1 := by
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P]
      rfl
    rw [h2]
    have : x = algebraMap (𝓞 E) E ⟨x, hx⟩ := rfl
    rw [this]
    exact P.valuation_le_one _
  rw [e, map_mul, GlobalTheory.CMVal.LatEnt.radN, map_mul]
  exact mul_le_of_le_one_right' (mul_le_one' hx1 (hMz P))

end GlobalTheory.HilbFam.LatDen
