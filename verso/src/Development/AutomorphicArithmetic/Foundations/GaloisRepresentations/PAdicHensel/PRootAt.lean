import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ A q _ hs w hw`. Take `⟨_, r, k, hk⟩` from `hs`. Establish `hkE : (r : 𝓞 E) ^ 2 - (A.tr : 𝓞 E) * (r : 𝓞 E) + (A.nm : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E)`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 E) hk` after adjusting the coercions. Establish `hprod : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) = (q : 𝓞 E) * (-(k : 𝓞 E))`.

Establish `htr` using `A.tr_eq`. Establish `hnm` using `A.nm_eq`. Establish `h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0`. Rewrite using `[← htr, ← hnm]`. Expand and normalize the polynomial expressions, which then agree.

Use `push_cast`. Take the linear combination `h0 - hkE`. Establish `hmem : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) ∈ w.asIdeal`. Rewrite using `[hprod]`. Conclude with `w.asIdeal.mul_mem_right _ hw`.

Break down `w.isPrime.mem_or_mem hmem with h | h` into its components or cases. Conclude with `⟨r, ⟨k, hk⟩, h⟩`. Use `⟨A.tr - r, ⟨k, ?_⟩, h⟩` and prove the remaining obligations. Rewrite using `[← hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.G1.pRootAt :
    RootAt := by
  intro E _ _ _ A q _ hs w hw
  obtain ⟨_, r, k, hk⟩ := hs
  have hkE : (r : 𝓞 E) ^ 2 - (A.tr : 𝓞 E) * (r : 𝓞 E) + (A.nm : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hk
  have hprod : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) = (q : 𝓞 E) * (-(k : 𝓞 E)) := by
    have htr := A.tr_eq
    have hnm := A.nm_eq
    have h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
      rw [← htr, ← hnm]; ring
    push_cast
    linear_combination h0 - hkE
  have hmem : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) ∈ w.asIdeal := by
    rw [hprod]; exact w.asIdeal.mul_mem_right _ hw
  rcases w.isPrime.mem_or_mem hmem with h | h
  · exact ⟨r, ⟨k, hk⟩, h⟩
  · refine ⟨A.tr - r, ⟨k, ?_⟩, h⟩
    rw [← hk]; ring
