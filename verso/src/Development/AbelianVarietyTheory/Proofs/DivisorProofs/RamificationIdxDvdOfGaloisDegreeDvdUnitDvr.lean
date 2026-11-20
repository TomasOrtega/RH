import Mathlib
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.RamGalDVR

/- English proof (translation)
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `hint : IsIntegral F x` using `IsIntegral.of_finite F x`. Establish `hdvd` using `minpoly.degree_dvd hint`. Use `show (minpoly F x).Separable`. Rewrite using `[Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)]`.

Introduce `hd`. Use `set n := (minpoly F x).natDegree with hn`. Establish `hpos : 0 < n` using `minpoly.natDegree_pos hint`. Establish `hc` using `congrArg (fun p : Polynomial F => p.coeff (n - 1)) hd`. Simplify using `only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc`.

Rewrite `hc` using `[Nat.sub_add_cancel hpos]`. Establish `hlead : (minpoly F x).coeff n = 1` using `minpoly.monic hint`. Rewrite `hc` using `[hlead, one_mul]`. Establish `hn0 : (n : F) = 0`. Establish `: ((n - 1 : ℕ) : F) + 1 = ((n - 1 + 1 : ℕ) : F)` using `by push_cast; ring`.

Rewrite `hc` using `[this, Nat.sub_add_cancel hpos]`. Conclude with `hc`. Take `⟨c, hc'⟩` from `hdvd`. Conclude with `h (by rw [hc', Nat.cast_mul, hn0, zero_mul])`.
-/
theorem isSeparable_of_natCast_finrank_ne_zero' {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  refine ⟨fun x => ?_⟩
  have hint : IsIntegral F x := IsIntegral.of_finite F x
  have hdvd := minpoly.degree_dvd hint
  show (minpoly F x).Separable
  rw [Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  intro hd
  set n := (minpoly F x).natDegree with hn
  have hpos : 0 < n := minpoly.natDegree_pos hint
  have hc := congrArg (fun p : Polynomial F => p.coeff (n - 1)) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
  rw [Nat.sub_add_cancel hpos] at hc
  have hlead : (minpoly F x).coeff n = 1 := minpoly.monic hint
  rw [hlead, one_mul] at hc
  have hn0 : (n : F) = 0 := by
    have : ((n - 1 : ℕ) : F) + 1 = ((n - 1 + 1 : ℕ) : F) := by push_cast; ring
    rw [this, Nat.sub_add_cancel hpos] at hc
    exact hc
  obtain ⟨c, hc'⟩ := hdvd
  exact h (by rw [hc', Nat.cast_mul, hn0, zero_mul])

/- English proof (translation)
Use `letI := hF.toField`. Use `letI := hE.toField`. Conclude with `@isSeparable_of_natCast_finrank_ne_zero' F E _ _ ‹Algebra F E› ‹Module.Finite F E› h`.
-/
theorem isSeparable_of_isField {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    [Module.Finite F E] (hF : IsField F) (hE : IsField E)
    (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  letI := hF.toField
  letI := hE.toField
  exact @isSeparable_of_natCast_finrank_ne_zero' F E _ _ ‹Algebra F E› ‹Module.Finite F E› h

/- English proof (translation)
Introduce `S K L _ _ _ _ _ _ _ _ _ _ _ _ q _ hq hdeg`. Use `set B := integralClosure S L`. Establish `: IsFractionRing B L` using `integralClosure.isFractionRing_of_finite_extension K L`. Establish `: Module.Finite S B` using `IsIntegralClosure.finite S K L B`. Establish `: IsGaloisGroup (L ≃ₐ[K] L) S B` using `IsGaloisGroup.of_isFractionRing _ _ _ K L`.

Establish `hinj : Function.Injective (algebraMap S L)`. Rewrite using `[IsScalarTower.algebraMap_eq S K L]`. Conclude with `(algebraMap K L).injective.comp (IsFractionRing.injective S K)`. Establish `: FaithfulSMul S B` using `(faithfulSMul_iff_algebraMap_injective S _).2 (fun a b h => hinj (congrArg Subtype.val h))`. Establish `: Module.Flat S B` using `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)`.

Establish `hfund` using `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal S) B (L ≃ₐ[K] L)`. Rewrite `hfund` using `[IsGalois.card_aut_eq_finrank]`. Establish `hef : Ideal.ramificationIdxIn (maximalIdeal S) B * Ideal.inertiaDegIn (maximalIdeal S) B ∣ q` using `(Dvd.intro_left _ hfund).trans hdeg`. Establish `hlies : ∀ P : Ideal B, P.IsMaximal → P.LiesOver (maximalIdeal S)`. Introduce `P hP`.

Use `⟨?_⟩` and prove the remaining obligations. Establish `: (P.under S).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Conclude with `(IsLocalRing.eq_maximalIdeal this).symm`. Use `⟨fun P hP => ?_, fun P hP _ => ?_⟩` and prove the remaining obligations. Use `hlies P hP` as an intermediate fact.

Rewrite using `[← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal S) P (L ≃ₐ[K] L)]`. Conclude with `(Dvd.intro _ rfl).trans hef`. Use `hP` as an intermediate fact. Establish `: (maximalIdeal S).IsMaximal` using `IsLocalRing.maximalIdeal.isMaximal S`. Establish `hf : Module.finrank (S ⧸ maximalIdeal S) (B ⧸ P) ∣ q`.

Rewrite using `[← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal S) P, ← Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal S) P (L ≃ₐ[K] L)]`. Conclude with `(Dvd.intro_left _ rfl).trans hef`. Establish `: Module.Finite S (B ⧸ P)` using `inferInstance`. Establish `: Module.Finite (S ⧸ maximalIdeal S) (B ⧸ P)` using `Module.Finite.of_restrictScalars_finite S _ _`. Use `isSeparable_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance) ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hP) ?_` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hf`. Introduce `h0`. Establish `hu : IsUnit ((q : S) : S ⧸ maximalIdeal S)` using `hq.map (Ideal.Quotient.mk _)`. Rewrite `hu` using `[map_natCast, hc, Nat.cast_mul, h0, zero_mul]`. Conclude with `not_isUnit_zero hu`.
-/
theorem ramGal : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [IsGalois K L] (q : ℕ), 0 < q → IsUnit (q : S) →
    Module.finrank K L ∣ q →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) ∧
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ q _ hq hdeg
  set B := integralClosure S L
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : Module.Finite S B := IsIntegralClosure.finite S K L B
  have : IsGaloisGroup (L ≃ₐ[K] L) S B := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have hinj : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have : FaithfulSMul S B :=
    (faithfulSMul_iff_algebraMap_injective S _).2 (fun a b h => hinj (congrArg Subtype.val h))
  have : Module.Flat S B :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal S) B (L ≃ₐ[K] L)
  rw [IsGalois.card_aut_eq_finrank] at hfund
  have hef : Ideal.ramificationIdxIn (maximalIdeal S) B * Ideal.inertiaDegIn (maximalIdeal S) B ∣ q :=
    (Dvd.intro_left _ hfund).trans hdeg
  have hlies : ∀ P : Ideal B, P.IsMaximal → P.LiesOver (maximalIdeal S) := by
    intro P hP
    refine ⟨?_⟩
    have : (P.under S).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  refine ⟨fun P hP => ?_, fun P hP _ => ?_⟩
  · have := hlies P hP
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal S) P (L ≃ₐ[K] L)]
    exact (Dvd.intro _ rfl).trans hef
  · have := hP
    have : (maximalIdeal S).IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
    have hf : Module.finrank (S ⧸ maximalIdeal S) (B ⧸ P) ∣ q := by
      rw [← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal S) P,
        ← Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal S) P (L ≃ₐ[K] L)]
      exact (Dvd.intro_left _ rfl).trans hef
    have : Module.Finite S (B ⧸ P) := inferInstance
    have : Module.Finite (S ⧸ maximalIdeal S) (B ⧸ P) :=
      Module.Finite.of_restrictScalars_finite S _ _
    refine isSeparable_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hP) ?_
    obtain ⟨c, hc⟩ := hf
    intro h0
    have hu : IsUnit ((q : S) : S ⧸ maximalIdeal S) := hq.map (Ideal.Quotient.mk _)
    rw [map_natCast, hc, Nat.cast_mul, h0, zero_mul] at hu
    exact not_isUnit_zero hu

end GlobalTheory.RamGalDVR
