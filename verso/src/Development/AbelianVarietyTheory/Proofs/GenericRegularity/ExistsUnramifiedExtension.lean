import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero

open TensorProduct

namespace GlobalTheory.DVRBaseChange

/- English proof (translation)
Establish `hnu : ∀ x : W, ¬ IsUnit x ↔ π ∣ x` using `fun x => by`. Rewrite using `[← Ideal.mem_span_singleton, ← hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Set `J : Ideal W` to `⨅ n : ℕ, Ideal.span {π ^ n}`. Establish `hJ : ∀ x, x ∈ J ↔ ∀ n : ℕ, π ^ n ∣ x` using `fun x => by`. Simplify using `only [J, Ideal.mem_iInf, Ideal.mem_span_singleton]`.

Establish `hpow : ∀ n : ℕ, π ^ n ∉ J`. Introduce `n hn`. Take `⟨y, hy⟩` from `(hJ _).1 hn (n + 1)`. Establish `hu : IsUnit (1 - π * y)` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((hnu _).2 (dvd_mul_right _ _))`. Use `hπ ⟨n, ?_⟩` and prove the remaining obligations.

Establish `: π ^ n * (1 - π * y) = 0` using `by linear_combination hy`. Conclude with `(hu.mul_left_eq_zero).1 this`. Establish `hfac : ∀ x, x ∉ J → ∃ (n : ℕ) (u : W), IsUnit u ∧ x = π ^ n * u`. Introduce `x hx`. Establish `hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hx ((hJ x).2 fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (hc n))`. Establish `h1 : π ^ (Nat.find hex) ∣ x`. Break down `h : Nat.find hex with _ | m` into its components or cases.

Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hc`. Conclude with `Nat.find_min hex (m := m) (by omega) hc`. Take `⟨u, hu⟩` from `h1`. Use `⟨_, u, ?_, hu⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Take `⟨v, rfl⟩` from `(hnu u).1 hc`. Conclude with `Nat.find_spec hex ⟨v, hu.trans (by ring)⟩`. Establish `hprime : J.IsPrime`. Use `⟨fun h => hpow 0 (h ▸ Submodule.mem_top), fun {x y} hxy => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨n, u, hu, rfl⟩` from `hfac x hc.1`. Take `⟨m, v, hv, rfl⟩` from `hfac y hc.2`. Use `hpow (n + m) ?_` and prove the remaining obligations.

Rewrite using `[← J.mul_unit_mem_iff_mem (hu.mul hv)]`. Use `hxy using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hdom : IsDomain (W ⧸ J)` using `Ideal.Quotient.isDomain J`. Establish `hloc : IsLocalRing (W ⧸ J)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective`.

Establish `hirr : Irreducible (Ideal.Quotient.mk J π)`. Use `IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `using hpow 1`. Rewrite using `[← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, hm, Ideal.map_span, Set.image_singleton]`.

Use `⟨W ⧸ J, inferInstance, hdom, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩, Ideal.Quotient.mk J, hirr⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨n, u, hu, rfl⟩` from `hfac x (fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h))`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow]`. Conclude with `associated_mul_unit_right _ _ (hu.map _)`.
-/
theorem exists_dvr_quotient (W : Type) [CommRing W] [IsLocalRing W] (π : W)
    (hm : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ : ¬ IsNilpotent π) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : W →+* V), Irreducible (q π) := by
  classical
  have hnu : ∀ x : W, ¬ IsUnit x ↔ π ∣ x := fun x => by
    rw [← Ideal.mem_span_singleton, ← hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  let J : Ideal W := ⨅ n : ℕ, Ideal.span {π ^ n}
  have hJ : ∀ x, x ∈ J ↔ ∀ n : ℕ, π ^ n ∣ x := fun x => by
    simp only [J, Ideal.mem_iInf, Ideal.mem_span_singleton]
  have hpow : ∀ n : ℕ, π ^ n ∉ J := by
    intro n hn
    obtain ⟨y, hy⟩ := (hJ _).1 hn (n + 1)
    have hu : IsUnit (1 - π * y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((hnu _).2 (dvd_mul_right _ _))
    refine hπ ⟨n, ?_⟩
    have : π ^ n * (1 - π * y) = 0 := by linear_combination hy
    exact (hu.mul_left_eq_zero).1 this
  have hfac : ∀ x, x ∉ J → ∃ (n : ℕ) (u : W), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra hc
      push Not at hc
      exact hx ((hJ x).2 fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (hc n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · by_contra hc
        exact Nat.find_min hex (m := m) (by omega) hc
    obtain ⟨u, hu⟩ := h1
    refine ⟨_, u, ?_, hu⟩
    by_contra hc
    obtain ⟨v, rfl⟩ := (hnu u).1 hc
    exact Nat.find_spec hex ⟨v, hu.trans (by ring)⟩
  have hprime : J.IsPrime := by
    refine ⟨fun h => hpow 0 (h ▸ Submodule.mem_top), fun {x y} hxy => ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨n, u, hu, rfl⟩ := hfac x hc.1
    obtain ⟨m, v, hv, rfl⟩ := hfac y hc.2
    refine hpow (n + m) ?_
    rw [← J.mul_unit_mem_iff_mem (hu.mul hv)]
    convert hxy using 1
    ring
  have hdom : IsDomain (W ⧸ J) := Ideal.Quotient.isDomain J
  have hloc : IsLocalRing (W ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hirr : Irreducible (Ideal.Quotient.mk J π) := by
    refine IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ?_ ?_
    · rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      simpa using hpow 1
    · rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective, hm, Ideal.map_span, Set.image_singleton]
  refine ⟨W ⧸ J, inferInstance, hdom,
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩,
    Ideal.Quotient.mk J, hirr⟩
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, u, hu, rfl⟩ := hfac x (fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h))
  refine ⟨n, ?_⟩
  rw [map_mul, map_pow]
  exact associated_mul_unit_right _ _ (hu.map _)

/- English proof (translation)
Take `⟨p, hp⟩` from `Ideal.nonempty_minimalPrimes hne`. Establish `hpp : p.IsPrime` using `hp.1.1`. Set `W` to `Localization.AtPrime p`. Establish `hm : IsLocalRing.maximalIdeal W = Ideal.span {algebraMap S W π}`. Establish `h1` using `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes W p _ hp`.

Rewrite `h1` using `[← IsLocalization.map_radical p.primeCompl, hrad.radical, Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]`. Conclude with `h1.symm`. Establish `hn : ¬ IsNilpotent (algebraMap S W π)`. Introduce and unpack `⟨n, hn⟩`. Rewrite `hn` using `[← map_pow, IsLocalization.map_eq_zero_iff p.primeCompl]`.

Take `⟨⟨s, hs⟩, h⟩` from `hn`. Establish `key : ∀ (n : ℕ) (s : S), s * π ^ n = 0 → s = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro s h`.

Simplify using `using h`. Consider the case `succ n ih => intro s h; exact ih s (hreg _ (by linear_combination h))`. Conclude with `hs (by rw [key n s h]; exact p.zero_mem)`. Take `⟨V, i1, i2, i3, q, hq⟩` from `exists_dvr_quotient W _ hm hn`. Conclude with `⟨V, i1, i2, i3, q.comp (algebraMap S W), hq⟩`.
-/
theorem exists_dvr_of_isRadical (S : Type) [CommRing S] (π : S)
    (hrad : (Ideal.span {π}).IsRadical) (hne : Ideal.span {π} ≠ ⊤)
    (hreg : ∀ s, π * s = 0 → s = 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : S →+* V), Irreducible (q π) := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpp : p.IsPrime := hp.1.1
  let W := Localization.AtPrime p
  have hm : IsLocalRing.maximalIdeal W = Ideal.span {algebraMap S W π} := by
    have h1 := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes W p _ hp
    rw [← IsLocalization.map_radical p.primeCompl, hrad.radical,
      Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton] at h1
    exact h1.symm
  have hn : ¬ IsNilpotent (algebraMap S W π) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff p.primeCompl] at hn
    obtain ⟨⟨s, hs⟩, h⟩ := hn
    have key : ∀ (n : ℕ) (s : S), s * π ^ n = 0 → s = 0 := by
      intro n
      induction n with
      | zero => intro s h; simpa using h
      | succ n ih => intro s h; exact ih s (hreg _ (by linear_combination h))
    exact hs (by rw [key n s h]; exact p.zero_mem)
  obtain ⟨V, i1, i2, i3, q, hq⟩ := exists_dvr_quotient W _ hm hn
  exact ⟨V, i1, i2, i3, q.comp (algebraMap S W), hq⟩

/- English proof (translation)
Introduce `K F T _ _ _ _ _ _ _ _`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible T`. Set `m` to `IsLocalRing.maximalIdeal T`. Establish `hm : m = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`. Use `letI : Field (T ⧸ m) := Ideal.Quotient.field m`.

Set `g : T ⊗[K] F →ₐ[K] (T ⧸ m) ⊗[K] F` to `Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K m) (AlgHom.id K F)`. Establish `hker : RingHom.ker g = Ideal.span {ϖ ⊗ₜ[K] (1 : F)}`. Rewrite using `[Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective K m)]`. Establish `: RingHom.ker (Ideal.Quotient.mkₐ K m) = Ideal.span {ϖ}`. Rewrite using `[← hm]`.

Conclude with `Ideal.mk_ker`. Rewrite using `[this, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Establish `hred : IsReduced ((T ⧸ m) ⊗[K] F)` using `GlobalTheory.ReducedAlg.isReduced_field_tensor _ _`. Establish `hrad : (Ideal.span {ϖ ⊗ₜ[K] (1 : F)}).IsRadical`.

Rewrite using `[← hker]`. Conclude with `Ideal.isRadical_bot.comap _`. Establish `hne : Ideal.span {ϖ ⊗ₜ[K] (1 : F)} ≠ ⊤`. Rewrite using `[← hker]`. Conclude with `RingHom.ker_ne_top _`.

Establish `hreg : ∀ s : T ⊗[K] F, (ϖ ⊗ₜ[K] (1 : F)) * s = 0 → s = 0`. Introduce `s hs`. Establish `hinj : Function.Injective ((LinearMap.mulLeft K ϖ).rTensor F)` using `Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => mul_left_cancel₀ hϖ.ne_zero h)`. Establish `key : ∀ s : T ⊗[K] F, (LinearMap.mulLeft K ϖ).rTensor F s = (ϖ ⊗ₜ[K] (1 : F)) * s`. Introduce `s`.

Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add x y hx hy => rw [map_add, hx, hy, mul_add]`. Conclude with `hinj (by rw [key, hs, map_zero])`.

Take `⟨V, i1, i2, i3, q, hq⟩` from `exists_dvr_of_isRadical _ _ hrad hne hreg`. Set `i : T →+* V` to `q.comp Algebra.TensorProduct.includeLeftRingHom`. Establish `hi : Irreducible (i ϖ)` using `hq`. Use `⟨V, i1, i2, i3, i, q.comp (Algebra.TensorProduct.includeRight (R := K) (A := T)).toRingHom, ?_, ?_, ⟨?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Assume the negation of the conclusion as `h0`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ`. Rewrite `hx` using `[map_mul, map_pow]`. Conclude with `mul_ne_zero (u.isUnit.map i).ne_zero (pow_ne_zero n hi.ne_zero) hx`.

Introduce `ϖ' h'`. Conclude with `((IsDiscreteValuationRing.associated_of_irreducible T hϖ h').map i).irreducible hi`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Establish `: x ∈ m` using `h0`.

Rewrite `this` using `[hm, Ideal.mem_span_singleton]`. Conclude with `hi.not_isUnit (isUnit_of_dvd_unit (map_dvd i this) hx)`. Introduce `a`. Express the relevant statement in the definitionally equal form `q (algebraMap K T a ⊗ₜ[K] (1 : F)) = q ((1 : T) ⊗ₜ[K] algebraMap K F a)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
theorem exists_unramified_extension :
    ∀ (K F T : Type) [Field K] [CharZero K] [Field F] [Algebra K F] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra K T], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (i : T →+* V) (χ : F →+* V), Function.Injective i ∧ (∀ ϖ : T, Irreducible ϖ → Irreducible (i ϖ)) ∧ IsLocalHom i ∧ ∀ a : K, i (algebraMap K T a) = χ (algebraMap K F a) := by
  intro K F T _ _ _ _ _ _ _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  let m := IsLocalRing.maximalIdeal T
  have hm : m = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  let g : T ⊗[K] F →ₐ[K] (T ⧸ m) ⊗[K] F :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K m) (AlgHom.id K F)
  have hker : RingHom.ker g = Ideal.span {ϖ ⊗ₜ[K] (1 : F)} := by
    rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective K m)]
    have : RingHom.ker (Ideal.Quotient.mkₐ K m) = Ideal.span {ϖ} := by
      rw [← hm]; exact Ideal.mk_ker
    rw [this, Ideal.map_span, Set.image_singleton]
    rfl
  have hred : IsReduced ((T ⧸ m) ⊗[K] F) := GlobalTheory.ReducedAlg.isReduced_field_tensor _ _
  have hrad : (Ideal.span {ϖ ⊗ₜ[K] (1 : F)}).IsRadical := by
    rw [← hker]
    exact Ideal.isRadical_bot.comap _
  have hne : Ideal.span {ϖ ⊗ₜ[K] (1 : F)} ≠ ⊤ := by
    rw [← hker]
    exact RingHom.ker_ne_top _
  have hreg : ∀ s : T ⊗[K] F, (ϖ ⊗ₜ[K] (1 : F)) * s = 0 → s = 0 := by
    intro s hs
    have hinj : Function.Injective ((LinearMap.mulLeft K ϖ).rTensor F) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun a b h => mul_left_cancel₀ hϖ.ne_zero h)
    have key : ∀ s : T ⊗[K] F, (LinearMap.mulLeft K ϖ).rTensor F s = (ϖ ⊗ₜ[K] (1 : F)) * s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, hx, hy, mul_add]
    exact hinj (by rw [key, hs, map_zero])
  obtain ⟨V, i1, i2, i3, q, hq⟩ := exists_dvr_of_isRadical _ _ hrad hne hreg
  let i : T →+* V := q.comp Algebra.TensorProduct.includeLeftRingHom
  have hi : Irreducible (i ϖ) := hq
  refine ⟨V, i1, i2, i3, i, q.comp (Algebra.TensorProduct.includeRight (R := K) (A := T)).toRingHom,
    ?_, ?_, ⟨?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow] at hx
    exact mul_ne_zero (u.isUnit.map i).ne_zero (pow_ne_zero n hi.ne_zero) hx
  · intro ϖ' h'
    exact ((IsDiscreteValuationRing.associated_of_irreducible T hϖ h').map i).irreducible hi
  · intro x hx
    by_contra h0
    have : x ∈ m := h0
    rw [hm, Ideal.mem_span_singleton] at this
    exact hi.not_isUnit (isUnit_of_dvd_unit (map_dvd i this) hx)
  · intro a
    change q (algebraMap K T a ⊗ₜ[K] (1 : F)) = q ((1 : T) ⊗ₜ[K] algebraMap K F a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.DVRBaseChange
