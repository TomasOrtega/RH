import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousOfValuationEq

open NumberField IsDedekindDomain

open WithZero

namespace GlobalTheory.DenseCompl

section DVR

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]

noncomputable def closedPoint (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    HeightOneSpectrum W :=
  ⟨IsLocalRing.maximalIdeal W, inferInstance, IsDiscreteValuationRing.not_a_field W⟩

/- English proof (translation)
Rewrite using `[← hπ.maximalIdeal_eq]`. Conclude with `IsLocalRing.eq_maximalIdeal v.isMaximal`.
-/
theorem asIdeal_eq_span {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) :
    v.asIdeal = Ideal.span {π} := by
  rw [← hπ.maximalIdeal_eq]
  exact IsLocalRing.eq_maximalIdeal v.isMaximal

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `v.intValuation_singleton hπ.ne_zero (asIdeal_eq_span hπ v)`.
-/
theorem valuation_uniformiser {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) :
    v.valuation Qq (algebraMap W Qq π) = exp (-1) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_singleton hπ.ne_zero (asIdeal_eq_span hπ v)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem, asIdeal_eq_span hπ v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `dvd_mul_right _ _`. Introduce `h`.

Establish `hπ0 : algebraMap W Qq π ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]`. Conclude with `hπ.ne_zero`. Take `⟨w, hw⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one Qq (q / algebraMap W Qq π ^ n) fun v' => by`. Establish `hv : v' = v` using `HeightOneSpectrum.ext ((asIdeal_eq_span hπ v').trans (asIdeal_eq_span hπ v).symm)`.

Substitute `hv` using the available equality. Rewrite using `[map_div₀, map_pow, valuation_uniformiser hπ v', ← WithZero.exp_nsmul, smul_neg, nsmul_one, div_le_iff₀ exp_pos, one_mul]`. Conclude with `h`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hw, mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]`.
-/
theorem exists_eq_pow_mul_iff {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) (q : Qq) (n : ℕ) :
    (∃ w : W, q = algebraMap W Qq (π ^ n * w)) ↔ v.valuation Qq q ≤ exp (-(n : ℤ)) := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      asIdeal_eq_span hπ v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  · intro h
    have hπ0 : algebraMap W Qq π ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]
      exact hπ.ne_zero
    obtain ⟨w, hw⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one Qq
      (q / algebraMap W Qq π ^ n) fun v' => by
        have hv : v' = v :=
          HeightOneSpectrum.ext ((asIdeal_eq_span hπ v').trans (asIdeal_eq_span hπ v).symm)
        subst hv
        rw [map_div₀, map_pow, valuation_uniformiser hπ v', ← WithZero.exp_nsmul, smul_neg, nsmul_one,
          div_le_iff₀ exp_pos, one_mul]
        exact h
    refine ⟨w, ?_⟩
    rw [map_mul, map_pow, hw, mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]

end DVR

/- English proof (translation)
Break down `eq_or_ne b 0 with rfl | hb0` into its components or cases. Assume the negation of the conclusion as `ha`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `ha le_rfl`.

Take `⟨n, hn⟩` from `GlobalTheory.Idele.exists_exp_neg_lt ha0`. Conclude with `absurd (h n zero_le') (not_le.2 hn)`. Establish `hl : log b ≤ 0`. Rewrite using `[← exp_le_exp, exp_log hb0, exp_zero]`. Conclude with `hb`.

Establish `hn : (((-log b).toNat : ℕ) : ℤ) = -log b` using `Int.toNat_of_nonneg (by omega)`. Establish `he : exp (-(((-log b).toNat : ℕ) : ℤ)) = b`. Rewrite using `[hn, neg_neg, exp_log hb0]`. Conclude with `(h _ he.ge).trans he.le`.
-/
theorem le_of_forall_le_exp {a b : ℤᵐ⁰} (hb : b ≤ 1)
    (h : ∀ n : ℕ, b ≤ exp (-(n : ℤ)) → a ≤ exp (-(n : ℤ))) : a ≤ b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · by_contra ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha le_rfl
    obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt ha0
    exact absurd (h n zero_le') (not_le.2 hn)
  · have hl : log b ≤ 0 := by
      rw [← exp_le_exp, exp_log hb0, exp_zero]
      exact hb
    have hn : (((-log b).toNat : ℕ) : ℤ) = -log b := Int.toNat_of_nonneg (by omega)
    have he : exp (-(((-log b).toNat : ℕ) : ℤ)) = b := by
      rw [hn, neg_neg, exp_log hb0]
    exact (h _ he.ge).trans he.le

/- English proof (translation)
The claim follows from `le_antisymm (le_of_forall_le_exp zero_le' fun n _ => h n) zero_le'`.
-/
theorem eq_zero_of_forall_le_exp {a : ℤᵐ⁰} (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ))) : a = 0 :=
  le_antisymm (le_of_forall_le_exp zero_le' fun n _ => h n) zero_le'

/- English proof (translation)
Use `continuous_of_continuousAt_zero f ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]`. Introduce `γ _`. Take `⟨a, ha⟩` from `hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)`. Establish `ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0`.

Simplify using `[ha]`. Use `⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx`. Simplify using `only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]`. Rewrite using `[hf, ← ha]`.

Conclude with `hx`.
-/
theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx

open scoped WithZeroTopology in

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension`. Consider the case `exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension`. Consider the case `(apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension ..)`.
-/
theorem exists_extension {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum R) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | (apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension ..)

end GlobalTheory.DenseCompl
