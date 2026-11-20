import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `hCU E _ _ _ M hM t htc hg`. Take `⟨hin, e, he, hz⟩` from `id hg`. Establish `h1 : InCodiff (1 : E)`. Introduce `x`. Establish `hx : IsIntegral ℤ (Algebra.trace ℚ E (x : E))` using `Algebra.isIntegral_trace x.2`.

Take `⟨m, hm⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hx`. Conclude with `⟨m, by rw [one_mul, ← hm]; simp⟩`. Take `⟨N, hN⟩` from `exists_nat_gt (∑ τ : E →+* ℂ, |(τ t).re|)`. Establish `hbound : ∀ τ : E →+* ℂ, |(τ t).re| < N` using `fun τ => lt_of_le_of_lt (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ t).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)) hN`. Establish `hin' : InCodiff (t + (M : E) * (N : E))`.

Introduce `x`. Take `⟨a, ha⟩` from `hin x`. Take `⟨b, hb⟩` from `h1 x`. Use `⟨a + M * N * b, ?_⟩` and prove the remaining obligations. Establish `hs : (t + (M : E) * (N : E)) * (x : E) = t * x + ((M : ℚ) * (N : ℚ)) • (1 * (x : E))`.

Rewrite using `[Algebra.smul_def]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, map_add, map_smul, ha, hb]`. Simplify using the standard rewrite rules.

Take `⟨x, hx⟩` from `hz 1 h1`. Establish `hgen : GenCodiff M (t + (M : E) * (N : E))`. Use `hCU E M hM t _ hg hin' ?_` and prove the remaining obligations. Introduce `P hP hMP`. Establish `heP : (e : 𝓞 E) ∉ P`.

Introduce `h`. Establish `hc : ((e.gcdA M : ℤ) : 𝓞 E) * (e : 𝓞 E) + ((e.gcdB M : ℤ) : 𝓞 E) * (M : 𝓞 E) = 1`. Use `Nat.gcd_eq_gcd_ab e M` as an intermediate fact. Rewrite `this` using `[he.gcd_eq_one]`. Establish `h2 : ((e : ℤ) * e.gcdA M + (M : ℤ) * e.gcdB M) = 1`.

Rewrite using `[← this]`. Simplify using the standard rewrite rules. Establish `h3` using `congrArg (Int.cast : ℤ → 𝓞 E) h2`. Move the coercions through the operations in `at h3`. Rewrite using `[← h3]`.

Expand and normalize the polynomial expressions, which then agree. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hc]`. Conclude with `P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hMP)`. Use `⟨(e : 𝓞 E), (e : 𝓞 E) + (M : 𝓞 E) * ((N : 𝓞 E) * x), heP, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Conclude with `heP ((P.add_mem_iff_left (P.mul_mem_right _ hMP)).mp h)`. Establish `hx' : (e : E) = t * x` using `by simpa using hx`. Use `push_cast`. Take the linear combination `((M : E) * (N : E)) * hx'`.

Use `⟨t + (M : E) * (N : E), ?_, hgen, ?_⟩` and prove the remaining obligations. Simplify using `[htc]`. Introduce `τ`. Establish `hb` using `abs_lt.mp (hbound τ)`. Establish `hM1 : (1 : ℝ) ≤ M` using `by exact_mod_cast hM`.

Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Establish `hre : (τ (t + (M : E) * (N : E))).re = (τ t).re + (M : ℝ) * (N : ℝ)`. Simplify using the standard rewrite rules. Rewrite using `[hre]`. Use polynomial arithmetic with `[hb.1]`.
-/
theorem UpperTheory.Gal.W2.Seed.pPosGen :
    CodiffUnit → PosGen := by
  intro hCU E _ _ _ M hM t htc hg
  obtain ⟨hin, e, he, hz⟩ := id hg

  have h1 : InCodiff (1 : E) := by
    intro x
    have hx : IsIntegral ℤ (Algebra.trace ℚ E (x : E)) := Algebra.isIntegral_trace x.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    exact ⟨m, by rw [one_mul, ← hm]; simp⟩

  obtain ⟨N, hN⟩ := exists_nat_gt (∑ τ : E →+* ℂ, |(τ t).re|)
  have hbound : ∀ τ : E →+* ℂ, |(τ t).re| < N := fun τ =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ t).re|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)) hN
  have hin' : InCodiff (t + (M : E) * (N : E)) := by
    intro x
    obtain ⟨a, ha⟩ := hin x
    obtain ⟨b, hb⟩ := h1 x
    refine ⟨a + M * N * b, ?_⟩
    have hs : (t + (M : E) * (N : E)) * (x : E) = t * x + ((M : ℚ) * (N : ℚ)) • (1 * (x : E)) := by
      rw [Algebra.smul_def]; simp; ring
    rw [hs, map_add, map_smul, ha, hb]
    simp
  obtain ⟨x, hx⟩ := hz 1 h1
  have hgen : GenCodiff M (t + (M : E) * (N : E)) := by
    refine hCU E M hM t _ hg hin' ?_
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro h
      have hc : ((e.gcdA M : ℤ) : 𝓞 E) * (e : 𝓞 E) + ((e.gcdB M : ℤ) : 𝓞 E) * (M : 𝓞 E) = 1 := by
        have := Nat.gcd_eq_gcd_ab e M
        rw [he.gcd_eq_one] at this
        have h2 : ((e : ℤ) * e.gcdA M + (M : ℤ) * e.gcdB M) = 1 := by
          rw [← this]; simp
        have h3 := congrArg (Int.cast : ℤ → 𝓞 E) h2
        push_cast at h3
        rw [← h3]; ring
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one, ← hc]
      exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hMP)
    refine ⟨(e : 𝓞 E), (e : 𝓞 E) + (M : 𝓞 E) * ((N : 𝓞 E) * x), heP, ?_, ?_⟩
    · intro h
      exact heP ((P.add_mem_iff_left (P.mul_mem_right _ hMP)).mp h)
    · have hx' : (e : E) = t * x := by simpa using hx
      push_cast
      linear_combination ((M : E) * (N : E)) * hx'
  refine ⟨t + (M : E) * (N : E), ?_, hgen, ?_⟩
  · simp [htc]
  · intro τ
    have hb := abs_lt.mp (hbound τ)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hre : (τ (t + (M : E) * (N : E))).re = (τ t).re + (M : ℝ) * (N : ℝ) := by
      simp
    rw [hre]
    nlinarith [hb.1]
