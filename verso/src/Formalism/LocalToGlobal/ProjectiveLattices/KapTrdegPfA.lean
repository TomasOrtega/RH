import Mathlib

namespace Formalism.L2.Pj.TranscendenceDegreeLemmas

open Algebra

/- English proof (translation)
Take `⟨g, hg⟩` from `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A`. Set `: Algebra (MvPolynomial (Fin n) K) A` to `g.toRingHom.toAlgebra`. Establish `: IsScalarTower K (MvPolynomial (Fin n) K) A` using `IsScalarTower.of_algebraMap_eq' (g.comp_algebraMap).symm`. Establish `: Algebra.Etale (MvPolynomial (Fin n) K) A` using `hg`. Establish `hq : p.under (MvPolynomial (Fin n) K) = ⊥`.

Assume the negation of the conclusion as `hne`. Establish `: p.LiesOver (p.under (MvPolynomial (Fin n) K))` using `⟨rfl⟩`. Take `⟨P, hPlt, hP, -⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := p.under (MvPolynomial (Fin n) K)) p (bot_lt_iff_ne_bot.mpr hne)`. Conclude with `(not_le_of_gt hPlt) (hp.2 ⟨hP, bot_le⟩ hPlt.le)`. Establish `: p.LiesOver (⊥ : Ideal (MvPolynomial (Fin n) K))` using `⟨hq.symm⟩`.

Set `` to `Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin n) K)) p`. Establish `: Localization.AtPrime.IsLiesOverAlgebra (⊥ : Ideal (MvPolynomial (Fin n) K)) p` using `⟨rfl⟩`. Establish `: Algebra.FormallyUnramified A (Localization.AtPrime p)` using `Algebra.FormallyUnramified.of_isLocalization p.primeCompl`. Establish `: Algebra.IsUnramifiedAt (MvPolynomial (Fin n) K) p` using `Algebra.FormallyUnramified.comp (MvPolynomial (Fin n) K) A (Localization.AtPrime p)`. Establish `: Module.Finite (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField` using `inferInstance`.

Establish `: Algebra.IsAlgebraic (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField` using `inferInstance`. Establish `: Algebra.IsAlgebraic (MvPolynomial (Fin n) K) (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField` using `IsLocalization.isAlgebraic _ (nonZeroDivisors _)`. Establish `: FaithfulSMul (MvPolynomial (Fin n) K) (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)`. Establish `: IsScalarTower K (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField` using `inferInstance`. Establish `h1` using `trdeg_add_eq K (MvPolynomial (Fin n) K) (A := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField)`.

Establish `h2` using `trdeg_add_eq K (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField (A := p.ResidueField)`. Rewrite `h1` using `[trdeg_eq_zero (R := MvPolynomial (Fin n) K) (A := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField), add_zero]`. Rewrite `h2` using `[trdeg_eq_zero (R := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField) (A := p.ResidueField), add_zero]`. Rewrite using `[← h2, ← h1, MvPolynomial.trdeg_of_isDomain]`. Simplify using the standard rewrite rules.
-/
theorem trdeg_residueField_of_minimal {K A : Type} [Field K] [CommRing A] [Algebra K A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A) :
    Algebra.trdeg K p.ResidueField = n := by
  classical
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) A :=
    IsScalarTower.of_algebraMap_eq' (g.comp_algebraMap).symm
  have : Algebra.Etale (MvPolynomial (Fin n) K) A := hg
  have hq : p.under (MvPolynomial (Fin n) K) = ⊥ := by
    by_contra hne
    have : p.LiesOver (p.under (MvPolynomial (Fin n) K)) := ⟨rfl⟩
    obtain ⟨P, hPlt, hP, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥)
      (q := p.under (MvPolynomial (Fin n) K)) p (bot_lt_iff_ne_bot.mpr hne)
    exact (not_le_of_gt hPlt) (hp.2 ⟨hP, bot_le⟩ hPlt.le)
  have : p.LiesOver (⊥ : Ideal (MvPolynomial (Fin n) K)) := ⟨hq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin n) K)) p
  have : Localization.AtPrime.IsLiesOverAlgebra (⊥ : Ideal (MvPolynomial (Fin n) K)) p := ⟨rfl⟩
  have : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.of_isLocalization p.primeCompl
  have : Algebra.IsUnramifiedAt (MvPolynomial (Fin n) K) p :=
    Algebra.FormallyUnramified.comp (MvPolynomial (Fin n) K) A (Localization.AtPrime p)
  have : Module.Finite (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField := inferInstance
  have : Algebra.IsAlgebraic (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField :=
    inferInstance
  have : Algebra.IsAlgebraic (MvPolynomial (Fin n) K) (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : FaithfulSMul (MvPolynomial (Fin n) K) (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have : IsScalarTower K (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField := inferInstance
  have h1 := trdeg_add_eq K (MvPolynomial (Fin n) K) (A := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField)
  have h2 := trdeg_add_eq K (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField (A := p.ResidueField)
  rw [trdeg_eq_zero (R := MvPolynomial (Fin n) K) (A := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField), add_zero] at h1
  rw [trdeg_eq_zero (R := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField) (A := p.ResidueField), add_zero] at h2
  rw [← h2, ← h1, MvPolynomial.trdeg_of_isDomain]
  simp

end Formalism.L2.Pj.TranscendenceDegreeLemmas
