import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Introduce `L _ _ N hN hφ`. Take `⟨φ⟩` from `hφ`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩`. Use `haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ`.

Use `letI : Algebra L (CyclotomicField N ℚ) := φ.toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℚ L (CyclotomicField N ℚ) := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)`. Establish `key` using `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L) (CyclotomicField N ℚ) (𝓞 (CyclotomicField N ℚ))`. Establish `hdC` using `IsCyclotomicExtension.Rat.natAbs_discr N (CyclotomicField N ℚ)`. Establish `hfin : Module.finrank ℚ (CyclotomicField N ℚ) = N.totient` using `IsCyclotomicExtension.finrank (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat hN)`.

Establish `htow` using `Module.finrank_mul_finrank ℚ L (CyclotomicField N ℚ)`. Establish `hm : 0 < Module.finrank L (CyclotomicField N ℚ)` using `Module.finrank_pos`. Establish `hne` using `NumberField.discr_ne_zero (CyclotomicField N ℚ)`. Establish `hdL` using `NumberField.discr_ne_zero L`. Establish `h1 : (discr L).natAbs ^ Module.finrank L (CyclotomicField N ℚ) ≤ (discr (CyclotomicField N ℚ)).natAbs`.

Rewrite using `[key]`. Establish `h0 : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 (CyclotomicField N ℚ))) ≠ 0`. Introduce `h0`. Rewrite `key` using `[h0, zero_mul]`. Conclude with `hne (Int.natAbs_eq_zero.mp key)`.

Conclude with `Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0)`. Establish `h2 : (discr (CyclotomicField N ℚ)).natAbs ≤ (N ^ Module.finrank ℚ L) ^ Module.finrank L (CyclotomicField N ℚ)`. Rewrite using `[hdC, ← pow_mul, htow, hfin]`. Conclude with `Nat.div_le_self _ _`. Establish `h3 : (discr L).natAbs ≤ N ^ Module.finrank ℚ L` using `(Nat.pow_le_pow_iff_left hm.ne').mp (h1.trans h2)`.

Establish `hd0 : 0 < (discr L).natAbs` using `Int.natAbs_pos.mpr hdL`. Rewrite using `[← Real.log_pow]`. Apply `Real.log_le_log (by exact_mod_cast hd0)` to reduce the goal to its premises. Conclude with `h3` after adjusting the coercions.
-/
theorem UpperTheory.V.Win.disc :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ) →
      Real.log ((discr L).natAbs : ℝ) ≤ (Module.finrank ℚ L : ℝ) * Real.log (N : ℝ) := by
  intro L _ _ N hN hφ
  obtain ⟨φ⟩ := hφ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  letI : Algebra L (CyclotomicField N ℚ) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L (CyclotomicField N ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have key := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L)
    (CyclotomicField N ℚ) (𝓞 (CyclotomicField N ℚ))
  have hdC := IsCyclotomicExtension.Rat.natAbs_discr N (CyclotomicField N ℚ)
  have hfin : Module.finrank ℚ (CyclotomicField N ℚ) = N.totient :=
    IsCyclotomicExtension.finrank (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat hN)
  have htow := Module.finrank_mul_finrank ℚ L (CyclotomicField N ℚ)
  have hm : 0 < Module.finrank L (CyclotomicField N ℚ) := Module.finrank_pos
  have hne := NumberField.discr_ne_zero (CyclotomicField N ℚ)
  have hdL := NumberField.discr_ne_zero L
  have h1 : (discr L).natAbs ^ Module.finrank L (CyclotomicField N ℚ)
      ≤ (discr (CyclotomicField N ℚ)).natAbs := by
    rw [key]
    have h0 : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 (CyclotomicField N ℚ))) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at key
      exact hne (Int.natAbs_eq_zero.mp key)
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0)
  have h2 : (discr (CyclotomicField N ℚ)).natAbs
      ≤ (N ^ Module.finrank ℚ L) ^ Module.finrank L (CyclotomicField N ℚ) := by
    rw [hdC, ← pow_mul, htow, hfin]
    exact Nat.div_le_self _ _
  have h3 : (discr L).natAbs ≤ N ^ Module.finrank ℚ L :=
    (Nat.pow_le_pow_iff_left hm.ne').mp (h1.trans h2)
  have hd0 : 0 < (discr L).natAbs := Int.natAbs_pos.mpr hdL
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast hd0)
  exact_mod_cast h3
