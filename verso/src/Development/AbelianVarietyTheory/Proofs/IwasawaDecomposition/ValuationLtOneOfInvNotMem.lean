import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import ReciprocityTheory.GaloisValuations.GlobalB

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open Pointwise

namespace GlobalTheory.WittFracPlace

/- English proof (translation)
Establish `hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1` using `fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)`. Establish `hmul : ∀ (m : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (m * x) < 1` using `fun m x hx => by`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hle m)) hx`. Prove the components needed by the constructor for the conclusion.

Introduce `hn`. Assume the negation of the conclusion as `hd`. Take `⟨a, b, hab⟩` from `((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hd`. Establish `e : (a : Ω) * p + b * n = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab`. Use `Valuation.map_add_lt _ (hmul a _ h) (hmul b _ hn)` as an intermediate fact.

Rewrite `this` using `[e, map_one]`. Conclude with `lt_irrefl _ this`. Introduce and unpack `⟨m, rfl⟩`. Rewrite using `[Int.cast_mul, mul_comm, Int.cast_natCast]`. Conclude with `hmul m _ h`.
-/
theorem valuation_intCast_lt_one_iff {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime)
    (h : A.valuation (p : Ω) < 1) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hmul : ∀ (m : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (m * x) < 1 := fun m x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle m)) hx
  constructor
  · intro hn
    by_contra hd
    obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hd
    have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    have := Valuation.map_add_lt _ (hmul a _ h) (hmul b _ hn)
    rw [e, map_one] at this
    exact lt_irrefl _ this
  · rintro ⟨m, rfl⟩
    rw [Int.cast_mul, mul_comm, Int.cast_natCast]
    exact hmul m _ h

/- English proof (translation)
Establish `hpr : (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)`. Set `v : HeightOneSpectrum (𝓞 ℚ)` to `⟨(Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom, Ideal.comap_isPrime _ _, fun hb => by`. Establish `h1 : (p : 𝓞 ℚ) ∈ (Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.subset_span rfl`.

Rewrite `h1` using `[hb, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by exact_mod_cast h1)⟩`. Establish `key : ∀ B : ValuationSubring Ω, B.valuation (p : Ω) < 1 → ∀ x : 𝓞 ℚ, B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ v.asIdeal`. Introduce `B hB x`. Take `⟨n, rfl⟩` from `Rat.ringOfIntegersEquiv.symm.surjective x`.

Establish `e : Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ)` using `eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n`. Establish `e2 : algebraMap ℚ Ω ((n : 𝓞 ℚ) : ℚ) = (n : Ω)` using `map_intCast ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) n`. Rewrite using `[e, e2, valuation_intCast_lt_one_iff B hp hB]`. Express the relevant statement in the definitionally equal form `_ ↔ (n : 𝓞 ℚ) ∈ Ideal.comap _ _`. Rewrite using `[Ideal.mem_comap, map_intCast, Int.cast_id, Ideal.mem_span_singleton]`.

Conclude with `ReciprocityTheory.Gal.exists_smul_eq_of_over (key A h) (key A' h')`.
-/
theorem exists_smul_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    (A A' : ValuationSubring Ω) (h : A.valuation (p : Ω) < 1) (h' : A'.valuation (p : Ω) < 1) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, g • A = A' := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨(Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom, Ideal.comap_isPrime _ _, fun hb => by
      have h1 : (p : 𝓞 ℚ) ∈ (Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom := by
        rw [Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
      rw [hb, Ideal.mem_bot] at h1
      exact hp.ne_zero (by exact_mod_cast h1)⟩
  have key : ∀ B : ValuationSubring Ω, B.valuation (p : Ω) < 1 →
      ∀ x : 𝓞 ℚ, B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ v.asIdeal := by
    intro B hB x
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    have e : Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ) := eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n
    have e2 : algebraMap ℚ Ω ((n : 𝓞 ℚ) : ℚ) = (n : Ω) :=
      map_intCast ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) n
    rw [e, e2, valuation_intCast_lt_one_iff B hp hB]
    change _ ↔ (n : 𝓞 ℚ) ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_intCast, Int.cast_id, Ideal.mem_span_singleton]
  exact ReciprocityTheory.Gal.exists_smul_eq_of_over (key A h) (key A' h')

/- English proof (translation)
Rewrite `h` using `[← A.valuation_le_one_iff, map_inv₀, not_le]`. Establish `h0 : A.valuation x ≠ 0` using `fun e => by simp [e] at h`. Conclude with `(one_lt_inv₀ (zero_lt_iff.2 h0)).1 h`.
-/
theorem valuation_lt_one_of_inv_notMem {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (h : x⁻¹ ∉ A) :
    A.valuation x < 1 := by
  rw [← A.valuation_le_one_iff, map_inv₀, not_le] at h
  have h0 : A.valuation x ≠ 0 := fun e => by simp [e] at h
  exact (one_lt_inv₀ (zero_lt_iff.2 h0)).1 h

/- English proof (translation)
Set `Ω` to `AlgebraicClosure L`. Establish `: Algebra.IsAlgebraic ℚ Ω` using `Algebra.IsAlgebraic.trans ℚ L Ω`. Establish `: IsAlgClosure ℚ Ω` using `⟨inferInstance, inferInstance⟩`. Set `ι : Ω →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Take `⟨A', hA'⟩` from `GlobalTheory.exists_valuationSubring_comap_eq (v.valuation L).valuationSubring (algebraMap L Ω)`.

Establish `hm : ∀ x : L, algebraMap L Ω x ∈ A' ↔ v.valuation L x ≤ 1` using `fun x => by`. Rewrite using `[← ValuationSubring.mem_comap, hA', Valuation.mem_valuationSubring_iff]`. Establish `h1 : (V.comap ι.toRingHom).valuation (p : Ω) < 1` using `valuation_lt_one_of_inv_notMem _ (by`. Rewrite using `[ValuationSubring.mem_comap, map_inv₀, map_natCast])` and apply the resulting hypothesis. Establish `h2 : A'.valuation (p : Ω) < 1` using `valuation_lt_one_of_inv_notMem _ (by`.

Establish `h3 : v.valuation L (p : L) < 1`. Use `(v.valuation_lt_one_iff_mem (K := L) (p : 𝓞 L)).2 hv` as an intermediate fact. Rewrite using `[← map_natCast (algebraMap (𝓞 L) L) p]`. Conclude with `this`. Establish `h4 : v.valuation L (p : L) ≠ 0` using `by simpa using hp.ne_zero`.

Rewrite using `[← map_natCast (algebraMap L Ω), ← map_inv₀, hm, map_inv₀, not_le]`. Conclude with `(one_lt_inv₀ (zero_lt_iff.2 h4)).2 h3)`. Take `⟨g, hg⟩` from `exists_smul_eq hp _ _ h1 h2`. Use `⟨(ι.toRingHom.comp g.symm.toRingEquiv.toRingHom).comp (algebraMap L Ω), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hm, ← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`.

Both sides reduce to the same expression.
-/
theorem exists_emb_inducing (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 L)) (hv : (p : 𝓞 L) ∈ v.asIdeal) (V : ValuationSubring ℂ) (hV : (p : ℂ)⁻¹ ∉ V) :
    ∃ e : L →+* ℂ, ∀ x, e x ∈ V ↔ v.valuation L x ≤ 1 := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ L Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let ι : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨A', hA'⟩ := GlobalTheory.exists_valuationSubring_comap_eq (v.valuation L).valuationSubring (algebraMap L Ω)
  have hm : ∀ x : L, algebraMap L Ω x ∈ A' ↔ v.valuation L x ≤ 1 := fun x => by
    rw [← ValuationSubring.mem_comap, hA', Valuation.mem_valuationSubring_iff]
  have h1 : (V.comap ι.toRingHom).valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    rwa [ValuationSubring.mem_comap, map_inv₀, map_natCast])
  have h2 : A'.valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    have h3 : v.valuation L (p : L) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := L) (p : 𝓞 L)).2 hv
      rw [← map_natCast (algebraMap (𝓞 L) L) p]
      exact this
    have h4 : v.valuation L (p : L) ≠ 0 := by simpa using hp.ne_zero
    rw [← map_natCast (algebraMap L Ω), ← map_inv₀, hm, map_inv₀, not_le]
    exact (one_lt_inv₀ (zero_lt_iff.2 h4)).2 h3)
  obtain ⟨g, hg⟩ := exists_smul_eq hp _ _ h1 h2
  refine ⟨(ι.toRingHom.comp g.symm.toRingEquiv.toRingHom).comp (algebraMap L Ω), fun x => ?_⟩
  rw [← hm, ← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/- English proof (translation)
Introduce `D p hp la`. Take `⟨j⟩` from `GlobalTheory.WittFracComplex.nonempty_ringHom_complex p`. Take `⟨V, -, -, -, hV⟩` from `GlobalTheory.exists_valuationSubring_dominating (V := WittVector p (AlgebraicClosure (ZMod p))) j`. Establish `hp' : (p : ℂ)⁻¹ ∉ V`. Rewrite using `[← map_natCast j, ← map_inv₀, hV]`.

Introduce and unpack `⟨a, ha⟩`. Establish `hinj` using `IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)`. Establish `h0 : (p : DV.KW p) ≠ 0` using `fun e => hp.out.ne_zero (by`. Use `congrArg j e` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`.

Conclude with `this)` after adjusting the coercions. Use `(WittVector.irreducible p (k := AlgebraicClosure (ZMod p))).not_isUnit (isUnit_iff_exists_inv.2 ⟨a, hinj ?_⟩)` and prove the remaining obligations. Rewrite using `[map_mul, ha, map_natCast, map_one, mul_inv_cancel₀ h0]`. Take `⟨e, he⟩` from `exists_emb_inducing D.what₂.LL hp.out la.1 la.2 V hp'`. Establish `: Countable D.what₂.LL` using `Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL).trans (by simp))`.

Take `⟨τ, hτ⟩` from `GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL e D.what₂.embLL`. Use `⟨τ.toRingHom.comp j, V.comap τ.symm.toRingHom, fun x => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← he, ← hτ, ValuationSubring.mem_comap]`. Simplify using the standard rewrite rules. Rewrite using `[← hV, ValuationSubring.mem_comap]`.

Simplify using the standard rewrite rules.
-/
theorem exists_jcPin : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p), ∃ jc : DV.KW p →+* ℂ, JcPin D p la jc := by
  intro D p hp la
  obtain ⟨j⟩ := GlobalTheory.WittFracComplex.nonempty_ringHom_complex p
  obtain ⟨V, -, -, -, hV⟩ :=
    GlobalTheory.exists_valuationSubring_dominating (V := WittVector p (AlgebraicClosure (ZMod p))) j
  have hp' : (p : ℂ)⁻¹ ∉ V := by
    rw [← map_natCast j, ← map_inv₀, hV]
    rintro ⟨a, ha⟩
    have hinj := IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)
    have h0 : (p : DV.KW p) ≠ 0 := fun e => hp.out.ne_zero (by
      have := congrArg j e
      rw [map_natCast, map_zero] at this
      exact_mod_cast this)
    refine (WittVector.irreducible p (k := AlgebraicClosure (ZMod p))).not_isUnit
      (isUnit_iff_exists_inv.2 ⟨a, hinj ?_⟩)
    rw [map_mul, ha, map_natCast, map_one, mul_inv_cancel₀ h0]
  obtain ⟨e, he⟩ := exists_emb_inducing D.what₂.LL hp.out la.1 la.2 V hp'
  have : Countable D.what₂.LL := Cardinal.mk_le_aleph0_iff.1
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL).trans (by simp))
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL e D.what₂.embLL
  refine ⟨τ.toRingHom.comp j, V.comap τ.symm.toRingHom, fun x => ?_, fun a => ?_⟩
  · rw [← he, ← hτ, ValuationSubring.mem_comap]
    simp
  · rw [← hV, ValuationSubring.mem_comap]
    simp

end GlobalTheory.WittFracPlace
