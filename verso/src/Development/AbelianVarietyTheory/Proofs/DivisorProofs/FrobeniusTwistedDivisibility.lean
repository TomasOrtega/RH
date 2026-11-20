import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAddPPowMulLt
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LemY

/- English proof (translation)
The claim follows from `charP_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S)) p PerfectRing (FractionRing S) p := by haveI : CharP (FractionRing S) p := charP_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S)) p refine PerfectRing.ofSurjective _ p fun x => ?_ obt …`.
-/
theorem perfectRing_fractionRing (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S]
    [CharP S p] [PerfectRing S p] :
    haveI : CharP (FractionRing S) p :=
      charP_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S)) p
    PerfectRing (FractionRing S) p := by
  haveI : CharP (FractionRing S) p :=
    charP_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S)) p
  refine PerfectRing.ofSurjective _ p fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨a', rfl⟩ := surjective_frobenius S p a
  obtain ⟨b', rfl⟩ := surjective_frobenius S p b
  refine ⟨algebraMap S (FractionRing S) a' / algebraMap S (FractionRing S) b', ?_⟩
  simp [frobenius_def, div_pow, map_pow]

/- English proof (translation)
Introduce `p _ S _ _ _ _ _ d m U Z hm hZ i`. Set `K` to `FractionRing S`. Use `haveI : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective S K) p`. Use `haveI : PerfectRing K p := perfectRing_fractionRing p S`. Establish `hinj : Function.Injective (algebraMap S K)` using `IsFractionRing.injective S K`.

Use `set j : WittVector p S →+* WittVector p K := WittVector.map (algebraMap S K) with hj`. Establish `jinj : Function.Injective j` using `WittVector.map_injective _ hinj`. Establish `hm' : (j m).coeff 0 ≠ 0`. Rewrite using `[hj, WittVector.map_coeff]`. Conclude with `fun h => hm (hinj (by simpa using h))`.

Take `⟨u, hu⟩` from `WittVector.isUnit_of_coeff_zero_ne_zero (j m) hm'`. Set `Y : Fin d → WittVector p K` to `fun k => ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * j (Z k)`. Establish `hfj : ∀ x, WittVector.frobenius (j x) = j (WittVector.frobenius x)` using `fun x => (map_frobenius_charP p (algebraMap S K) x).symm`. Establish `hφu : WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * WittVector.frobenius (u : WittVector p K) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.

Establish `hY : ∀ k, WittVector.frobenius (Y k) = (U.map j *ᵥ Y) k`. Introduce `k`. Establish `e` using `congrArg j (hZ k)`. Rewrite `e` using `[map_mul, map_mul, ← hfj, ← hfj, map_mulVec_witt p (algebraMap S K) d U Z k, ← hu]`. Establish `hmv : (U.map j *ᵥ Y) k = ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * (U.map j *ᵥ fun l => j (Z l)) k`.

Simplify using `only [Y, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations. Rewrite using `[hmv]`. Simplify using `only [Y, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)), Units.inv_mul, one_mul]`. Use `_ = WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * (WittVector.frobenius (u : WittVector p K) * (U.map j *ᵥ fun l => j (Z l)) k)) := by`. Rewrite using `[e]`. Use `_ = (WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * WittVector.frobenius (u : WittVector p K)) * (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * (U.map j *ᵥ fun l => j (Z l)) k) := by ring`. Use `_ = _ := by rw [hφu, one_mul]`.

Take `⟨w, hw⟩` from `range_of_frobenius_eq p S K d U Y hY i`. Use `⟨w, jinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hu]`. Express the relevant statement in the definitionally equal form `j w = Y i at hw`. Rewrite using `[hw]`.

Simplify using `only [Y, ← mul_assoc, Units.mul_inv, one_mul]`.
-/
theorem dvd_of_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] (d : ℕ) (m : WittVector p S) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Z : Fin d → WittVector p S), m.coeff 0 ≠ 0 → (∀ i, m * WittVector.frobenius (Z i) = WittVector.frobenius m * (U *ᵥ Z) i) → ∀ i, m ∣ Z i := by
  intro p _ S _ _ _ _ _ d m U Z hm hZ i
  let K := FractionRing S
  haveI : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective S K) p
  haveI : PerfectRing K p := perfectRing_fractionRing p S
  have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  set j : WittVector p S →+* WittVector p K := WittVector.map (algebraMap S K) with hj
  have jinj : Function.Injective j := WittVector.map_injective _ hinj
  have hm' : (j m).coeff 0 ≠ 0 := by
    rw [hj, WittVector.map_coeff]
    exact fun h => hm (hinj (by simpa using h))
  obtain ⟨u, hu⟩ := WittVector.isUnit_of_coeff_zero_ne_zero (j m) hm'
  let Y : Fin d → WittVector p K := fun k => ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * j (Z k)
  have hfj : ∀ x, WittVector.frobenius (j x) = j (WittVector.frobenius x) := fun x =>
    (map_frobenius_charP p (algebraMap S K) x).symm

  have hφu : WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)
      * WittVector.frobenius (u : WittVector p K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hY : ∀ k, WittVector.frobenius (Y k) = (U.map j *ᵥ Y) k := by
    intro k
    have e := congrArg j (hZ k)
    rw [map_mul, map_mul, ← hfj, ← hfj, map_mulVec_witt p (algebraMap S K) d U Z k, ← hu] at e

    have hmv : (U.map j *ᵥ Y) k = ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)
        * (U.map j *ᵥ fun l => j (Z l)) k := by
      simp only [Y, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [hmv]
    simp only [Y, map_mul]
    calc WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * WittVector.frobenius (j (Z k))
        = WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)
          * (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * ((u : WittVector p K) * WittVector.frobenius (j (Z k)))) := by
          rw [← mul_assoc (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)), Units.inv_mul, one_mul]
      _ = WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K)
          * (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * (WittVector.frobenius (u : WittVector p K) * (U.map j *ᵥ fun l => j (Z l)) k)) := by
          rw [e]
      _ = (WittVector.frobenius ((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * WittVector.frobenius (u : WittVector p K))
          * (((u⁻¹ : (WittVector p K)ˣ) : WittVector p K) * (U.map j *ᵥ fun l => j (Z l)) k) := by ring
      _ = _ := by rw [hφu, one_mul]
  obtain ⟨w, hw⟩ := range_of_frobenius_eq p S K d U Y hY i
  refine ⟨w, jinj ?_⟩
  rw [map_mul, ← hu]
  change j w = Y i at hw
  rw [hw]
  simp only [Y, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.LemY
