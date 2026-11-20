import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/- English proof (translation)
Establish `hu0 : u ≠ 0`. Introduce `h`. Simplify using `[h] at hu`. Establish `hmem : ∀ w : v.adicCompletion ℚ, Valued.v w ≤ 1 → ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v w‖ ≤ 1`. Introduce `w hw`.

Establish `hw' : w ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))`. Rewrite using `[SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `hw`. Use `(Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hw'` as an intermediate fact. Simplify using `using this`.

Establish `h1` using `hmem u hu.le`. Establish `h2` using `hmem u⁻¹ (by rw [map_inv₀, hu, inv_one])`. Establish `h3 : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ * ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, mul_inv_cancel₀ hu0, map_one, norm_one]`. Establish `h4` using `norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u)`.

Establish `h5` using `norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹)`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem norm_padicEquiv_of_valued_eq_one (v : HeightOneSpectrum ℤ) (u : v.adicCompletion ℚ)
    (hu : Valued.v u = 1) : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hmem : ∀ w : v.adicCompletion ℚ, Valued.v w ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v w‖ ≤ 1 := by
    intro w hw
    have hw' : w ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hw
    have := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hw'
    simpa using this
  have h1 := hmem u hu.le
  have h2 := hmem u⁻¹ (by rw [map_inv₀, hu, inv_one])
  have h3 : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ *
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hu0, map_one, norm_one]
  have h4 := norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u)
  have h5 := norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹)
  nlinarith

/- English proof (translation)
Introduce `hP v`. Take `⟨m, κ, hκ⟩` from `hP (Rat.HeightOneSpectrum.primesEquiv v).1`. Use `⟨m, fun u => κ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u), ?_⟩` and prove the remaining obligations. Introduce `u u' hu hu' huu`. Take `⟨x, hx⟩` from `hκ _ _ (norm_padicEquiv_of_valued_eq_one v u hu) (norm_padicEquiv_of_valued_eq_one v u' hu') huu`.

Use `⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hx`. Rewrite `h` using `[map_mul, map_pow]`. Simplify using `using h`.
-/
theorem UpperTheory.Gal.G1.pZSqFin :
    PadicSqFin → ZSqFin := by
  intro hP v
  obtain ⟨m, κ, hκ⟩ := hP (Rat.HeightOneSpectrum.primesEquiv v).1
  refine ⟨m, fun u => κ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u), ?_⟩
  intro u u' hu hu' huu
  obtain ⟨x, hx⟩ := hκ _ _ (norm_padicEquiv_of_valued_eq_one v u hu)
    (norm_padicEquiv_of_valued_eq_one v u' hu') huu
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x, ?_⟩
  have h := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hx
  rw [map_mul, map_pow] at h
  simpa using h
