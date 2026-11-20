import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowCong
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh11.pow_cong A ha hb h m`.
-/
private theorem pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qh11.pow_cong A ha hb h m

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))`.
-/
private theorem dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩`. Consider the case `succ n ih`. Use `⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `hg.2 _ (dec_le ih.1 hx)`.

Establish `h2` using `pow_cong A (dec_le ih.1 hx) (b := x ^ q ^ n) (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q`. Establish `h3` using `Valuation.map_add_lt A.valuation h1 h2`. Rewrite `h3` using `[sub_add_sub_cancel, ← pow_mul, ← pow_succ]`. Rewrite using `[pow_succ' g, AlgEquiv.mul_apply]`. Conclude with `h3`.
-/
private theorem isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) : IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (dec_le ih.1 hx)
    have h2 := pow_cong A (dec_le ih.1 hx) (b := x ^ q ^ n) (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `h1 : 1 ≤ A.valuation (g x)` using `not_lt.1 hc`. Establish `h2 : A.valuation (g x⁻¹) ≤ 1`. Rewrite using `[map_inv₀, map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ h1`.

Establish `h3` using `dec_le (inv_mem hg) h2`. Establish `e : g⁻¹ (g x⁻¹) = x⁻¹` using `g.symm_apply_apply _`. Rewrite `h3` using `[e, map_inv₀]`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h1`. Establish `h0 : 0 < A.valuation x` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0)`. Conclude with `absurd hx (not_lt.2 ((inv_le_one₀ h0).1 h3))`.
-/
private theorem dec_lt {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x < 1) : A.valuation (g x) < 1 := by
  by_contra hc
  have h1 : 1 ≤ A.valuation (g x) := not_lt.1 hc
  have h2 : A.valuation (g x⁻¹) ≤ 1 := by
    rw [map_inv₀, map_inv₀]
    exact inv_le_one_of_one_le₀ h1
  have h3 := dec_le (inv_mem hg) h2
  have e : g⁻¹ (g x⁻¹) = x⁻¹ := g.symm_apply_apply _
  rw [e, map_inv₀] at h3
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h1
  have h0 : 0 < A.valuation x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0)
  exact absurd hx (not_lt.2 ((inv_le_one₀ h0).1 h3))

/- English proof (translation)
Use `⟨mul_mem (inv_mem hh.1) hg.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h3` using `Valuation.map_sub_lt A.valuation (hg.2 _ hx) (hh.2 _ hx)`. Rewrite `h3` using `[sub_sub_sub_cancel_right]`. Establish `h4` using `dec_lt (inv_mem hh.1) h3`. Establish `e : h⁻¹ (h x) = x` using `h.symm_apply_apply x`.

Rewrite `h4` using `[map_sub, e]`. Conclude with `h4`.
-/
private theorem inv_mul_ine {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g h : G K Ω} (hg : IsFrob (F := K) A q g) (hh : IsFrob (F := K) A q h) : h⁻¹ * g ∈ Ine (F := K) A := by
  refine ⟨mul_mem (inv_mem hh.1) hg.1, fun x hx => ?_⟩
  have h3 := Valuation.map_sub_lt A.valuation (hg.2 _ hx) (hh.2 _ hx)
  rw [sub_sub_sub_cancel_right] at h3
  have h4 := dec_lt (inv_mem hh.1) h3
  have e : h⁻¹ (h x) = x := h.symm_apply_apply x
  rw [map_sub, e] at h4
  exact h4

/- English proof (translation)
Establish `hpr : Prime (p : 𝓞 ℚ)`. Establish `h : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ)` using `by simp`. Rewrite using `[e]`. Conclude with `(MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h`.

Establish `hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal` using `((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)`. Conclude with `(hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm`.
-/
private theorem asIdeal_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  have hpr : Prime (p : 𝓞 ℚ) := by
    have h : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  exact (hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm

/- English proof (translation)
Establish `h : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Rewrite using `[h, asIdeal_eq hp v hv, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]`. Simplify using the standard rewrite rules.
-/
private theorem normV_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    normV v = p := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [h, asIdeal_eq hp v hv, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
  simp

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ _ _ p h w v hp hw hv B hB σ hσ`. Establish `hcl : IsAlgClosure ℚ Ω` using `{ isAlgClosed := IsAlgClosure.isAlgClosed K isAlgebraic := Algebra.IsAlgebraic.trans ℚ K Ω }`. Establish `hu : (p : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal` using `by show algebraMap (𝓞 ℚ) (𝓞 K) (p : 𝓞 ℚ) ∈ w.asIdeal`. Rewrite using `[map_natCast]` and apply the resulting hypothesis. Establish `hvw : v = w.under (𝓞 ℚ)` using `HeightOneSpectrum.ext ((asIdeal_eq hp v hv).trans (asIdeal_eq hp _ hu).symm)`.

Establish `hBv : IsPlaceOver B v`. Rewrite using `[hvw]`. Introduce `x`. Rewrite using `[IsScalarTower.algebraMap_apply ℚ K Ω]`. Conclude with `hB (algebraMap (𝓞 ℚ) (𝓞 K) x)`.

Use `⟨hBv, ?_⟩` and prove the remaining obligations. Take `⟨τ, hτ⟩` from `exists_isFrob hBv`. Use `⟨τ, hτ, ?_⟩` and prove the remaining obligations. Rewrite `hτ` using `[normV_eq hp v hv]`. Establish `hσ' : IsFrob (F` using `ℚ) B (p ^ h) (σ.restrictScalars ℚ) := ⟨hσ.1, hσ.2⟩`.

Conclude with `inv_mul_ine hσ' (isFrob_pow hτ h)`.
-/
theorem UpperTheory.frobenius_pow_resDeg_place_norm :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (p h : ℕ) (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → (p : 𝓞 ℚ) ∈ v.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (p ^ h) σ → IsPlaceOver B v ∧ ∃ τ : G ℚ Ω, IsFrob B (normV v) τ ∧ (τ ^ h)⁻¹ * σ.restrictScalars ℚ ∈ Ine (F := ℚ) B := by
  intro K Ω _ _ _ _ _ _ _ p h w v hp hw hv B hB σ hσ
  have hcl : IsAlgClosure ℚ Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed K
      isAlgebraic := Algebra.IsAlgebraic.trans ℚ K Ω }
  have hu : (p : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    show algebraMap (𝓞 ℚ) (𝓞 K) (p : 𝓞 ℚ) ∈ w.asIdeal
    rwa [map_natCast]
  have hvw : v = w.under (𝓞 ℚ) :=
    HeightOneSpectrum.ext ((asIdeal_eq hp v hv).trans (asIdeal_eq hp _ hu).symm)
  have hBv : IsPlaceOver B v := by
    rw [hvw]
    intro x
    rw [IsScalarTower.algebraMap_apply ℚ K Ω]
    exact hB (algebraMap (𝓞 ℚ) (𝓞 K) x)
  refine ⟨hBv, ?_⟩
  obtain ⟨τ, hτ⟩ := exists_isFrob hBv
  refine ⟨τ, hτ, ?_⟩
  rw [normV_eq hp v hv] at hτ
  have hσ' : IsFrob (F := ℚ) B (p ^ h) (σ.restrictScalars ℚ) := ⟨hσ.1, hσ.2⟩
  exact inv_mul_ine hσ' (isFrob_pow hτ h)
