import Formalism.SharpRestriction.InertJacobiLevels.ExtraNch

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain IsLocalRing

/- English proof (translation)
Establish `key : ∀ y : K, w.valuation K y ≤ 1 → ∃ a s : R, s ∉ w.asIdeal ∧ y * algebraMap R K s = algebraMap R K a`. Introduce `y hy`. Establish `hmem : y ∈ Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors`. Establish `h1 : y ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w).toSubring` using `by show y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]`.

Conclude with `(Valuation.mem_valuationSubring_iff _ _).2 hy`. Rewrite `h1` using `[IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring]`. Conclude with `h1`. Use `haveI := Localization.subalgebra.isLocalization_ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors`. Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.mk'_surjective w.asIdeal.primeCompl (⟨y, hmem⟩ : Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors)`.

Use `⟨a, s, s.2, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun z : Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors => (z : K)) (IsLocalization.mk'_spec (Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors) a s)`. Establish `hs' : IsLocalization.mk' (Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors) a s = ⟨y, hmem⟩` using `hs`. Rewrite `h2` using `[hs']`. Simplify using `using h2`.

Establish `hone : ∀ s : R, s ∉ w.asIdeal → w.intValuation s = 1` using `fun s hs => le_antisymm (w.intValuation_le_one s) (not_lt.1 fun h => hs ((IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w s).1 h))`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨a, s, hs, has⟩` from `key x hx`. Take `⟨u, hu⟩` from `h3 s hs`.

Establish `hfa : f (algebraMap R K a) ∈ (algebraMap B FB).range`. Distinguish the cases in `ha : a ∈ w.asIdeal`. Take `⟨y, _, hy⟩` from `h1 a ha`. Conclude with `⟨y, hy⟩`. Take `⟨y, hy⟩` from `h3 a ha`.

Conclude with `⟨y, hy⟩`. Take `⟨b, hb⟩` from `hfa`. Use `⟨b * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Establish `hfx : f x * f (algebraMap R K s) = f (algebraMap R K a)` using `by rw [← map_mul, has]`. Rewrite using `[map_mul, hb, ← hfx, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]`.

Introduce and unpack `⟨b, hb⟩`. Assume the negation of the conclusion as `hx`. Use `push_neg at hx`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hx`. Establish `hinv : w.valuation K x⁻¹ < 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ hx`. Take `⟨a, s, hs, has⟩` from `key x⁻¹ hinv.le`.

Establish `hva : w.intValuation a < 1`. Establish `es : w.valuation K (algebraMap R K s) = 1`. Establish `e0 : w.valuation K (algebraMap R K s) = w.intValuation s` using `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w s`. Rewrite using `[e0, hone s hs]`. Establish `ev : w.valuation K (algebraMap R K a) = w.valuation K x⁻¹`.

Rewrite using `[← has, map_mul, es, mul_one]`. Establish `ea : w.valuation K (algebraMap R K a) = w.intValuation a` using `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w a`. Rewrite using `[← ea, ev]`. Conclude with `hinv`. Establish `ha : a ∈ w.asIdeal` using `(IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w a).1 hva`.

Take `⟨y, hy, hya⟩` from `h1 a ha`. Take `⟨u, hu⟩` from `h3 s hs`. Establish `e1 : f x⁻¹ * algebraMap B FB u = algebraMap B FB y`. Rewrite using `[hu, hya, ← map_mul, has]`. Establish `e2 : algebraMap B FB (b * y) = algebraMap B FB u`.

Rewrite using `[map_mul, ← e1, hb, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul]`. Establish `e3` using `hinj e2`. Establish `hmax : (u : B) ∈ maximalIdeal B` using `e3 ▸ Ideal.mul_mem_left _ b hy`. Conclude with `((IsLocalRing.mem_maximalIdeal _).1 hmax) u.isUnit`.
-/
theorem val_le_one_iff {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (w : HeightOneSpectrum R) {B FB : Type*} [CommRing B] [IsLocalRing B] [Field FB] [Algebra B FB]
    (hinj : Function.Injective (algebraMap B FB)) (f : K →+* FB)
    (h1 : ∀ x : R, x ∈ w.asIdeal → ∃ y ∈ maximalIdeal B, algebraMap B FB y = f (algebraMap R K x))
    (h3 : ∀ x : R, x ∉ w.asIdeal → ∃ y : Bˣ, algebraMap B FB y = f (algebraMap R K x)) (x : K) :
    w.valuation K x ≤ 1 ↔ f x ∈ (algebraMap B FB).range := by
  have key : ∀ y : K, w.valuation K y ≤ 1 →
      ∃ a s : R, s ∉ w.asIdeal ∧ y * algebraMap R K s = algebraMap R K a := by
    intro y hy
    have hmem : y ∈ Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors := by
      have h1 : y ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w).toSubring := by
        show y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w
        rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
        exact (Valuation.mem_valuationSubring_iff _ _).2 hy
      rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h1
      exact h1
    haveI := Localization.subalgebra.isLocalization_ofField K w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl
      (⟨y, hmem⟩ : Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors)
    refine ⟨a, s, s.2, ?_⟩
    have h2 := congrArg (fun z : Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors => (z : K))
      (IsLocalization.mk'_spec (Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors) a s)
    have hs' : IsLocalization.mk' (Localization.subalgebra.ofField K w.asIdeal.primeCompl
        w.asIdeal.primeCompl_le_nonZeroDivisors) a s = ⟨y, hmem⟩ := hs
    rw [hs'] at h2
    simpa using h2
  have hone : ∀ s : R, s ∉ w.asIdeal → w.intValuation s = 1 := fun s hs =>
    le_antisymm (w.intValuation_le_one s)
      (not_lt.1 fun h => hs ((IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w s).1 h))
  constructor
  · intro hx
    obtain ⟨a, s, hs, has⟩ := key x hx
    obtain ⟨u, hu⟩ := h3 s hs
    have hfa : f (algebraMap R K a) ∈ (algebraMap B FB).range := by
      by_cases ha : a ∈ w.asIdeal
      · obtain ⟨y, _, hy⟩ := h1 a ha
        exact ⟨y, hy⟩
      · obtain ⟨y, hy⟩ := h3 a ha
        exact ⟨y, hy⟩
    obtain ⟨b, hb⟩ := hfa
    refine ⟨b * ↑u⁻¹, ?_⟩
    have hfx : f x * f (algebraMap R K s) = f (algebraMap R K a) := by rw [← map_mul, has]
    rw [map_mul, hb, ← hfx, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rintro ⟨b, hb⟩
    by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hinv : w.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hx
    obtain ⟨a, s, hs, has⟩ := key x⁻¹ hinv.le
    have hva : w.intValuation a < 1 := by
      have es : w.valuation K (algebraMap R K s) = 1 := by
        have e0 : w.valuation K (algebraMap R K s) = w.intValuation s :=
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w s
        rw [e0, hone s hs]
      have ev : w.valuation K (algebraMap R K a) = w.valuation K x⁻¹ := by
        rw [← has, map_mul, es, mul_one]
      have ea : w.valuation K (algebraMap R K a) = w.intValuation a :=
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w a
      rw [← ea, ev]
      exact hinv
    have ha : a ∈ w.asIdeal := (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem w a).1 hva
    obtain ⟨y, hy, hya⟩ := h1 a ha
    obtain ⟨u, hu⟩ := h3 s hs
    have e1 : f x⁻¹ * algebraMap B FB u = algebraMap B FB y := by
      rw [hu, hya, ← map_mul, has]
    have e2 : algebraMap B FB (b * y) = algebraMap B FB u := by
      rw [map_mul, ← e1, hb, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul]
    have e3 := hinj e2
    have hmax : (u : B) ∈ maximalIdeal B := e3 ▸ Ideal.mul_mem_left _ b hy
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmax) u.isUnit

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible A`. Establish `hne : Ideal.span {(l : A)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ`. Establish `hyn : y ^ n ∈ Ideal.span {(l : A)}`.

Rewrite using `[hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]`. Conclude with `Ideal.pow_mem_pow hy n`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hyn`. Establish `hpow : g y ^ n ∈ maximalIdeal B`. Rewrite using `[← map_pow, ← hc, map_mul, map_natCast]`.

Conclude with `Ideal.mul_mem_left _ _ hl`. Conclude with `(maximalIdeal.isMaximal B).isPrime.mem_of_pow_mem n hpow`.
-/
theorem map_mem_maximalIdeal {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (g : A →+* B) (l : ℕ) (hl0 : (l : A) ≠ 0) (hl : (l : B) ∈ maximalIdeal B) (y : A)
    (hy : y ∈ maximalIdeal A) : g y ∈ maximalIdeal B := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hne : Ideal.span {(l : A)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hyn : y ^ n ∈ Ideal.span {(l : A)} := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
    exact Ideal.pow_mem_pow hy n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hyn
  have hpow : g y ^ n ∈ maximalIdeal B := by
    rw [← map_pow, ← hc, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ hl
  exact (maximalIdeal.isMaximal B).isPrime.mem_of_pow_mem n hpow

section Rec

variable (D : D7)

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[D.val_eq w x hx, Formalism.BasicNotions.vAdd]`. Establish `hv0 : (D.plEq w).valuation D.what₂.LL x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`.

Take `⟨n, hn⟩ : ∃ n : ℤ, (D.plEq w).valuation D.what₂.LL x = WithZero.exp n` from `⟨_, (WithZero.exp_log hv0).symm⟩`. Rewrite using `[hn, WithZero.log_exp, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Rewrite using `[show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_nonneg_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [D.val_eq w x hx, Formalism.BasicNotions.vAdd]
    have hv0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (D.plEq w).valuation D.what₂.LL x = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hv0).symm⟩
    rw [hn, WithZero.log_exp, ← WithZero.exp_zero, WithZero.exp_le_exp]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
    omega

/- English proof (translation)
Establish `h1` using `D.what₂.places.val_resChar w`. Establish `hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0` using `Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero`. Rewrite `h1` using `[D.val_eq w _ hne, Formalism.BasicNotions.vAdd]`. Establish `h2` using `WithTop.coe_injective h1`. Establish `hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0` using `(Valuation.ne_zero_iff _).2 hne`.

Take `⟨n, hn⟩ : ∃ n : ℤ, (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = WithZero.exp n` from `⟨_, (WithZero.exp_log hv0).symm⟩`. Rewrite `h2` using `[hn, WithZero.log_exp]`. Establish `hpos` using `D.what₂.places.ramIdx_pos w`. Establish `hlt : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1`. Rewrite using `[hn, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]`. Establish `e : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) = (D.plEq w).intValuation ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)` using `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _`. Rewrite using `[← e, map_natCast]`. Conclude with `hlt`.
-/
theorem resChar_mem (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have h1 := D.what₂.places.val_resChar w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  rw [D.val_eq w _ hne, Formalism.BasicNotions.vAdd] at h1
  have h2 := WithTop.coe_injective h1
  have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hne
  obtain ⟨n, hn⟩ : ∃ n : ℤ,
      (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = WithZero.exp n :=
    ⟨_, (WithZero.exp_log hv0).symm⟩
  rw [hn, WithZero.log_exp] at h2
  have hpos := D.what₂.places.ramIdx_pos w
  have hlt : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
    rw [hn, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
  have e : (D.plEq w).valuation D.what₂.LL
      (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) =
      (D.plEq w).intValuation ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _
  rw [← e, map_natCast]
  exact hlt

end Rec

end Formalism.MainNotions.Inhab

end
