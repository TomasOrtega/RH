import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

open Polynomial

namespace GlobalTheory.FractionRingRootRange

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hdeg hmon hz`. Rewrite `hz` using `[Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg, map_one]`.

Conclude with `absurd hz one_ne_zero`. Consider the case `succ n ih`. Introduce `p hdeg hmon hz`. Take `⟨a, ha⟩` from `h p hmon (by omega)`. Establish `hmul : (X - C a) * (p /ₘ (X - C a)) = p` using `mul_divByMonic_eq_iff_isRoot.mpr ha`.

Establish `hqmon : (p /ₘ (X - C a)).Monic` using `(monic_X_sub_C a).of_mul_monic_left (by rw [hmul]; exact hmon)`. Establish `hqdeg : (p /ₘ (X - C a)).natDegree = n`. Rewrite using `[natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]`. Use linear arithmetic over natural numbers and integers. Rewrite `hz` using `[← hmul, map_mul]`.

Simplify using `only [map_sub, aeval_X, aeval_C] at hz`. Break down `mul_eq_zero.mp hz with h1 | h1` into its components or cases. Conclude with `⟨a, (sub_eq_zero.mp h1).symm⟩`. Conclude with `ih _ hqdeg hqmon h1`.
-/
theorem root_mem_range {A B : Type} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B] [Algebra A B]
    (h : GlobalTheory.EtC.AIC A) (z : B) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → aeval z p = 0 → ∃ a : A, algebraMap A B a = z := by
  intro n
  induction n with
  | zero =>
    intro p hdeg hmon hz
    rw [Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg, map_one] at hz
    exact absurd hz one_ne_zero
  | succ n ih =>
    intro p hdeg hmon hz
    obtain ⟨a, ha⟩ := h p hmon (by omega)
    have hmul : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqmon : (p /ₘ (X - C a)).Monic :=
      (monic_X_sub_C a).of_mul_monic_left (by rw [hmul]; exact hmon)
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]
      omega
    rw [← hmul, map_mul] at hz
    simp only [map_sub, aeval_X, aeval_C] at hz
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqdeg hqmon h1

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_` and prove the remaining obligations. Establish `hdeg : p.degree ≠ 0` using `(Polynomial.degree_pos_of_irreducible hirr).ne'`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root (p.map (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A)))) (by rwa [degree_map])`. Establish `hpz : aeval z p = 0`. Rewrite using `[aeval_def, ← eval_map]`.

Conclude with `hz`. Take `⟨b, hbM, hb⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors A) p`. Establish `hbK : algebraMap A (FractionRing A) b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM`. Establish `hq0 : IsLocalization.integerNormalization (nonZeroDivisors A) p ≠ 0`. Introduce `h0`.

Establish `h1` using `congrArg (fun r => r.coeff p.natDegree) hb`. Simplify using `only [h0, Polynomial.map_zero, coeff_zero, coeff_smul, hmon.coeff_natDegree] at h1`. Rewrite `h1` using `[Algebra.smul_def, mul_one]`. Conclude with `hbK h1.symm`. Establish `hqz : aeval z (IsLocalization.integerNormalization (nonZeroDivisors A) p) = 0`.

Rewrite using `[← aeval_map_algebraMap (FractionRing A), hb, Algebra.smul_def, map_mul, hpz, mul_zero]`. Establish `inj : ∀ x : A, algebraMap A (AlgebraicClosure (FractionRing A)) x = 0 → x = 0`. Introduce `x hx`. Rewrite `hx` using `[IsScalarTower.algebraMap_apply A (FractionRing A), map_eq_zero]`. Conclude with `IsFractionRing.to_map_eq_zero_iff.mp hx`.

Establish `hw` using `integralNormalization_aeval_eq_zero hqz inj`. Establish `hmon' : (integralNormalization (IsLocalization.integerNormalization (nonZeroDivisors A) p)).Monic`. Conclude with `monic_integralNormalization hq0`. Take `⟨a, ha⟩` from `root_mem_range (B := AlgebraicClosure (FractionRing A)) h _ _ _ rfl hmon' hw`. Use `set c := (IsLocalization.integerNormalization (nonZeroDivisors A) p).leadingCoeff`.

Establish `hc : algebraMap A (FractionRing A) c ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `leadingCoeff_ne_zero.mpr hq0`. Establish `ha' : algebraMap A (AlgebraicClosure (FractionRing A)) a = algebraMap A (AlgebraicClosure (FractionRing A)) c * z`. Rewrite using `[ha]`.

Use `⟨algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) c, ?_⟩` and prove the remaining obligations. Establish `hcB : algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A)) (algebraMap A (FractionRing A) c) ≠ 0` using `(_root_.map_ne_zero _).mpr hc`. Establish `hx : algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A)) (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) c) = z`. Rewrite using `[map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha']`. Rewrite `hcB` using `[← IsScalarTower.algebraMap_apply]`.

Clear the denominators using the available nonvanishing facts. Apply `(algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).injective` to reduce the goal to its premises. Rewrite using `[map_zero, ← eval₂_hom, ← eval_map, hx]`. Conclude with `hz`.
-/
theorem isAlgClosed_fractionRing (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsAlgClosed (FractionRing A) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hdeg : p.degree ≠ 0 := (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))))
    (by rwa [degree_map])
  have hpz : aeval z p = 0 := by
    rw [aeval_def, ← eval_map]
    exact hz
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
  have hbK : algebraMap A (FractionRing A) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM
  have hq0 : IsLocalization.integerNormalization (nonZeroDivisors A) p ≠ 0 := by
    intro h0
    have h1 := congrArg (fun r => r.coeff p.natDegree) hb
    simp only [h0, Polynomial.map_zero, coeff_zero, coeff_smul, hmon.coeff_natDegree] at h1
    rw [Algebra.smul_def, mul_one] at h1
    exact hbK h1.symm
  have hqz : aeval z (IsLocalization.integerNormalization (nonZeroDivisors A) p) = 0 := by
    rw [← aeval_map_algebraMap (FractionRing A), hb, Algebra.smul_def, map_mul, hpz, mul_zero]
  have inj : ∀ x : A, algebraMap A (AlgebraicClosure (FractionRing A)) x = 0 → x = 0 := by
    intro x hx
    rw [IsScalarTower.algebraMap_apply A (FractionRing A), map_eq_zero] at hx
    exact IsFractionRing.to_map_eq_zero_iff.mp hx
  have hw := integralNormalization_aeval_eq_zero hqz inj
  have hmon' : (integralNormalization (IsLocalization.integerNormalization (nonZeroDivisors A) p)).Monic := by
    exact monic_integralNormalization hq0
  obtain ⟨a, ha⟩ := root_mem_range (B := AlgebraicClosure (FractionRing A)) h _ _ _ rfl hmon' hw
  set c := (IsLocalization.integerNormalization (nonZeroDivisors A) p).leadingCoeff
  have hc : algebraMap A (FractionRing A) c ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact leadingCoeff_ne_zero.mpr hq0
  have ha' : algebraMap A (AlgebraicClosure (FractionRing A)) a =
      algebraMap A (AlgebraicClosure (FractionRing A)) c * z := by
    rw [ha]
  refine ⟨algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) c, ?_⟩
  have hcB : algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A)) (algebraMap A (FractionRing A) c) ≠ 0 :=
    (_root_.map_ne_zero _).mpr hc
  have hx : algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))
      (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) c) = z := by
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha']
    rw [← IsScalarTower.algebraMap_apply] at hcB
    field_simp
  apply (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).injective
  rw [map_zero, ← eval₂_hom, ← eval_map, hx]
  exact hz

end GlobalTheory.FractionRingRootRange
