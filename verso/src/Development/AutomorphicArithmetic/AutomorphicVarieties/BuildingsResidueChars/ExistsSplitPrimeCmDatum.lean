import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecActRoots

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

/- English proof (translation)
Introduce `Ω _ _ _ U hU hc M hM`. Take `⟨N, hN, hNU⟩` from `UpperTheory.V.CF.kwAbs Ω U hU hc`. Take `⟨w, hw, hMw, hmod⟩` from `Nat.exists_prime_gt_modEq_one M (Nat.mul_ne_zero hM.ne' hN.ne')`. Establish `hwM : w ≡ 1 [MOD M]` using `Nat.ModEq.of_dvd (Dvd.intro N rfl) hmod`. Establish `hwN : w ≡ 1 [MOD N]` using `Nat.ModEq.of_dvd (Dvd.intro_left M rfl) hmod`.

Use `⟨w, hw, hMw, hwM, ?_⟩` and prove the remaining obligations. Introduce `A hA g hg`. Use `haveI : Fact (Nat.Prime w) := ⟨hw⟩`. Establish `hcop : N.Coprime w`. Establish `h` using `Nat.ModEq.gcd_eq hwN`.

Rewrite `h` using `[Nat.gcd_one_left]`. Conclude with `Nat.Coprime.symm h`. Take `⟨k, hk⟩` from `UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w A hA N hcop g hg`. Apply `hNU` to reduce the goal to its premises. Introduce `ζ hζ`.

Rewrite using `[hk ζ hζ]`. Establish `hpow : w ^ k % N = 1 % N`. Establish `h` using `Nat.ModEq.pow k hwN`. Rewrite `h` using `[one_pow]`. Then use the resulting hypothesis. Rewrite using `[← Nat.div_add_mod (w ^ k) N, pow_add, pow_mul, hζ, one_pow, one_mul, hpow]`.

Break down `Nat.lt_or_ge 1 N with h1 | h1` into its components or cases. Rewrite using `[Nat.mod_eq_of_lt h1, pow_one]`. Establish `hN1 : N = 1` using `by omega`. Substitute `hN1` using the available equality. Simplify using `only [pow_one] at hζ`.

Simplify using `[hζ]`.
-/
theorem UpperTheory.exists_splitPrime_cmDatum :
    UpperTheory.V.Sd.S3.SplitPrime := by
  intro Ω _ _ _ U hU hc M hM
  obtain ⟨N, hN, hNU⟩ := UpperTheory.V.CF.kwAbs Ω U hU hc
  obtain ⟨w, hw, hMw, hmod⟩ := Nat.exists_prime_gt_modEq_one M (Nat.mul_ne_zero hM.ne' hN.ne')
  have hwM : w ≡ 1 [MOD M] := Nat.ModEq.of_dvd (Dvd.intro N rfl) hmod
  have hwN : w ≡ 1 [MOD N] := Nat.ModEq.of_dvd (Dvd.intro_left M rfl) hmod
  refine ⟨w, hw, hMw, hwM, ?_⟩
  intro A hA g hg
  haveI : Fact (Nat.Prime w) := ⟨hw⟩
  have hcop : N.Coprime w := by
    have h := Nat.ModEq.gcd_eq hwN
    rw [Nat.gcd_one_left] at h
    exact Nat.Coprime.symm h
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w A hA N hcop g hg
  apply hNU
  intro ζ hζ
  rw [hk ζ hζ]
  have hpow : w ^ k % N = 1 % N := by
    have h := Nat.ModEq.pow k hwN
    rwa [one_pow] at h
  rw [← Nat.div_add_mod (w ^ k) N, pow_add, pow_mul, hζ, one_pow, one_mul, hpow]
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hN1 : N = 1 := by omega
    subst hN1
    simp only [pow_one] at hζ
    simp [hζ]
