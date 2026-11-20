import Mathlib

open scoped nonZeroDivisors TensorProduct WithZero

namespace GlobalTheory

section Ring

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/- English proof (translation)
Use `⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem p).mpr hap⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `q ⟨hq, haq⟩ hqp`. Assume the negation of the conclusion as `hne`. Establish `hlt : q < p` using `lt_of_le_not_ge hqp hne`. Establish `h1 : q.height < p.height` using `Ideal.height_strict_mono_of_isPrime hlt`.

Rewrite `h1` using `[hp, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot]`. Rewrite `haq` using `[h1, Ideal.span_singleton_le_iff_mem]`. Conclude with `ha haq`.
-/
theorem mem_minimalPrimes_span_singleton_of_height_eq_one {p : Ideal A} [p.IsPrime]
    (hp : p.height = 1) {a : A} (ha : a ≠ 0) (hap : a ∈ p) :
    p ∈ (Ideal.span {a}).minimalPrimes := by
  refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem p).mpr hap⟩, ?_⟩
  rintro q ⟨hq, haq⟩ hqp
  by_contra hne
  have hlt : q < p := lt_of_le_not_ge hqp hne
  have h1 : q.height < p.height := Ideal.height_strict_mono_of_isPrime hlt
  rw [hp, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
  rw [h1, Ideal.span_singleton_le_iff_mem] at haq
  exact ha haq

/- English proof (translation)
Use `((Ideal.span {a}).finite_minimalPrimes_of_isNoetherianRing.preimage (f := PrimeSpectrum.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hap⟩`. Conclude with `mem_minimalPrimes_span_singleton_of_height_eq_one hp ha hap`.
-/
theorem finite_height_eq_one_mem {a : A} (ha : a ≠ 0) :
    {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite := by
  refine ((Ideal.span {a}).finite_minimalPrimes_of_isNoetherianRing.preimage
    (f := PrimeSpectrum.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro p ⟨hp, hap⟩
  exact mem_minimalPrimes_span_singleton_of_height_eq_one hp ha hap

omit [IsNoetherianRing A] in

/- English proof (translation)
Rewrite using `[Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p B, hp]`. Both sides reduce to the same expression.
-/
theorem krullDimLE_one_of_height_eq_one (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.AtPrime B p] :
    Ring.KrullDimLE 1 B := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p B, hp]
  rfl

variable [IsIntegrallyClosed A]

/- English proof (translation)
Use `IsLocalization.AtPrime.isLocalRing B p` as an intermediate fact. Use `IsLocalization.isNoetherianRing p.primeCompl B inferInstance` as an intermediate fact. Establish `hic` using `isIntegrallyClosed_of_isLocalization B p.primeCompl p.primeCompl_le_nonZeroDivisors`. Establish `hd` using `krullDimLE_one_of_height_eq_one p hp B`. Establish `hf : ¬ IsField B` using `IsLocalization.AtPrime.not_isField A (p.ne_bot_of_height_eq_one hp) B`.

Establish `hm : IsLocalRing.maximalIdeal B ≠ ⊥` using `IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf`. Establish `key` using `(IsDiscreteValuationRing.TFAE B hf).out 3 0`. Use `key.mp ⟨hic, IsLocalRing.maximalIdeal B, ⟨hm, inferInstance⟩, fun P hP => ?_⟩` and prove the remaining obligations. Conclude with `IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_isPrime_bot.mp hd P hP.1 hP.2)`.
-/
theorem isDiscreteValuationRing_of_height_eq_one (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
    (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [IsLocalization.AtPrime B p] :
    IsDiscreteValuationRing B := by
  have := IsLocalization.AtPrime.isLocalRing B p
  have := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  have hic := isIntegrallyClosed_of_isLocalization B p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hd := krullDimLE_one_of_height_eq_one p hp B
  have hf : ¬ IsField B := IsLocalization.AtPrime.not_isField A (p.ne_bot_of_height_eq_one hp) B
  have hm : IsLocalRing.maximalIdeal B ≠ ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
  have key := (IsDiscreteValuationRing.TFAE B hf).out 3 0
  refine key.mp ⟨hic, IsLocalRing.maximalIdeal B, ⟨hm, inferInstance⟩, fun P hP => ?_⟩
  exact IsLocalRing.eq_maximalIdeal
    (Ring.krullDimLE_one_iff_of_isPrime_bot.mp hd P hP.1 hP.2)

/- English proof (translation)
Establish `hap : a ∈ p` using `(h a).mpr (dvd_mul_right a b)`. Set `K` to `FractionRing A`. Establish `ha' : algebraMap A K a ≠ 0` using `IsFractionRing.to_map_eq_zero_iff.not.mpr ha`. Take `⟨y, hy, k, hk, hyk⟩ : ∃ y ∈ p, ∃ k, k ∉ p ∧ y * b = a * k` from `by by_contra! H`. Establish `hint` using `isIntegral_of_smul_mem_submodule (A := K) (Submodule.map (Algebra.linearMap A K) p) ?_ ?_ (algebraMap A K b / algebraMap A K a) ?_`.

Take `⟨y, e⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Use `hp.ne_top ((Ideal.eq_top_iff_one p).mpr ((h 1).mpr ⟨y, ?_⟩))` and prove the remaining obligations. Apply `IsFractionRing.injective A K` to reduce the goal to its premises. Rewrite using `[one_mul, map_mul, e, mul_div_cancel₀ _ ha']`. Rewrite using `[Submodule.ne_bot_iff]`.

Conclude with `⟨_, ⟨a, hap, rfl⟩, ha'⟩`. Conclude with `Submodule.FG.map _ (IsNoetherian.noetherian _)`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Take `⟨k, hk⟩` from `(h m).mp hm`. Use `⟨k, by_contra fun hkp => H m hm k hkp hk, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap A K k = algebraMap A K b / algebraMap A K a * algebraMap A K m`. Rewrite using `[div_mul_eq_mul_div, ← map_mul, mul_comm b, hk, map_mul, mul_div_cancel_left₀ _ ha']`. Establish `hmin : p ∈ (Ideal.span {y}).minimalPrimes`. Use `⟨⟨hp, (Ideal.span_singleton_le_iff_mem p).mpr hy⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `q ⟨hq, hyq⟩ hqp m hm`.

Take `⟨k', hk'⟩` from `(h m).mp hm`. Establish `e : k * m = y * k'`. Apply `mul_left_cancel₀ ha` to reduce the goal to its premises. Take the linear combination `y * hk' - m * hyk`. Establish `: k * m ∈ q` using `e ▸ q.mul_mem_right _ ((Ideal.span_singleton_le_iff_mem q).mp hyq)`.

Conclude with `(hq.mem_or_mem this).resolve_left fun hkq => hk (hqp hkq)`. Use `le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hmin) ?_` and prove the remaining obligations. Rewrite using `[ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]`. Introduce and unpack `rfl`. Conclude with `ha hap`.
-/
theorem height_eq_one_of_forall_mem_iff_dvd {p : Ideal A} [hp : p.IsPrime] {a b : A} (ha : a ≠ 0)
    (h : ∀ r, r ∈ p ↔ a ∣ r * b) : p.height = 1 := by
  have hap : a ∈ p := (h a).mpr (dvd_mul_right a b)
  let K := FractionRing A
  have ha' : algebraMap A K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  obtain ⟨y, hy, k, hk, hyk⟩ : ∃ y ∈ p, ∃ k, k ∉ p ∧ y * b = a * k := by
    by_contra! H
    have hint := isIntegral_of_smul_mem_submodule (A := K)
      (Submodule.map (Algebra.linearMap A K) p) ?_ ?_ (algebraMap A K b / algebraMap A K a) ?_
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
      refine hp.ne_top ((Ideal.eq_top_iff_one p).mpr ((h 1).mpr ⟨y, ?_⟩))
      apply IsFractionRing.injective A K
      rw [one_mul, map_mul, e, mul_div_cancel₀ _ ha']
    · rw [Submodule.ne_bot_iff]
      exact ⟨_, ⟨a, hap, rfl⟩, ha'⟩
    · exact Submodule.FG.map _ (IsNoetherian.noetherian _)
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨k, hk⟩ := (h m).mp hm
      refine ⟨k, by_contra fun hkp => H m hm k hkp hk, ?_⟩
      change algebraMap A K k = algebraMap A K b / algebraMap A K a * algebraMap A K m
      rw [div_mul_eq_mul_div, ← map_mul, mul_comm b, hk, map_mul, mul_div_cancel_left₀ _ ha']
  have hmin : p ∈ (Ideal.span {y}).minimalPrimes := by
    refine ⟨⟨hp, (Ideal.span_singleton_le_iff_mem p).mpr hy⟩, ?_⟩
    rintro q ⟨hq, hyq⟩ hqp m hm
    obtain ⟨k', hk'⟩ := (h m).mp hm
    have e : k * m = y * k' := by
      apply mul_left_cancel₀ ha
      linear_combination y * hk' - m * hyk
    have : k * m ∈ q := e ▸ q.mul_mem_right _ ((Ideal.span_singleton_le_iff_mem q).mp hyq)
    exact (hq.mem_or_mem this).resolve_left fun hkq => hk (hqp hkq)
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hmin) ?_
  rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  rintro rfl
  exact ha hap

/- English proof (translation)
Take `⟨hpp, x, hx⟩` from `isAssociatedPrime_iff.mp hp`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Use `height_eq_one_of_forall_mem_iff_dvd (b := b) ha fun r => ?_` and prove the remaining obligations. Rewrite using `[hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`.
-/
theorem height_eq_one_of_mem_associatedPrimes {a : A} (ha : a ≠ 0) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})) : p.height = 1 := by
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine height_eq_one_of_forall_mem_iff_dvd (b := b) ha fun r => ?_
  rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

/- English proof (translation)
Establish `hann : Module.annihilator A (A ⧸ Ideal.span {a}) = Ideal.span {a}` using `Ideal.annihilator_quotient`. Prove the components needed by the constructor for the conclusion. Introduce `hp`. Use `⟨hp.1, height_eq_one_of_mem_associatedPrimes ha hp, ?_⟩` and prove the remaining obligations. Use `IsAssociatedPrime.annihilator_le hp` as an intermediate fact.

Rewrite `this` using `[Submodule.annihilator_top, hann]`. Conclude with `this (Ideal.mem_span_singleton_self a)`. Introduce and unpack `⟨_, hp, hap⟩`. Apply `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes` to reduce the goal to its premises. Rewrite using `[hann]`.

Conclude with `mem_minimalPrimes_span_singleton_of_height_eq_one hp ha hap`.
-/
theorem mem_associatedPrimes_iff_height_eq_one {a : A} (ha : a ≠ 0) {p : Ideal A} :
    p ∈ associatedPrimes A (A ⧸ Ideal.span {a}) ↔ p.IsPrime ∧ p.height = 1 ∧ a ∈ p := by
  have hann : Module.annihilator A (A ⧸ Ideal.span {a}) = Ideal.span {a} :=
    Ideal.annihilator_quotient
  constructor
  · intro hp
    refine ⟨hp.1, height_eq_one_of_mem_associatedPrimes ha hp, ?_⟩
    have := IsAssociatedPrime.annihilator_le hp
    rw [Submodule.annihilator_top, hann] at this
    exact this (Ideal.mem_span_singleton_self a)
  · rintro ⟨_, hp, hap⟩
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [hann]
    exact mem_minimalPrimes_span_singleton_of_height_eq_one hp ha hap

/- English proof (translation)
Assume the negation of the conclusion as `hab`. Establish `hb : Ideal.Quotient.mk (Ideal.span {a}) b ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]` and apply the resulting hypothesis. Take `⟨p, hp, hle⟩` from `exists_le_isAssociatedPrime_of_isNoetherianRing A _ hb`. Take `⟨_, h1, hap⟩` from `(mem_associatedPrimes_iff_height_eq_one ha).mp hp`.

Take `⟨s, hs, hsb⟩` from `h p h1 hap`. Use `hs (hle ?_)` and prove the remaining obligations. Rewrite using `[Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]` and apply the resulting hypothesis.
-/
theorem dvd_of_forall_height_eq_one {a b : A} (ha : a ≠ 0)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → ∃ s, s ∉ p ∧ a ∣ s * b) : a ∣ b := by
  by_contra hab
  have hb : Ideal.Quotient.mk (Ideal.span {a}) b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hb
  obtain ⟨_, h1, hap⟩ := (mem_associatedPrimes_iff_height_eq_one ha).mp hp
  obtain ⟨s, hs, hsb⟩ := h p h1 hap
  refine hs (hle ?_)
  rwa [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

end Ring

section Module

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.projective_def.mp (inferInstance : Module.Projective A M)`. Use `choose c hc using fun i : M => h (Finsupp.lapply i ∘ₗ s)`. Use `⟨∑ i ∈ (s m).support, c i • i, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← hs m, Finsupp.linearCombination_apply, Finsupp.sum]`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← hc i]`. Both sides reduce to the same expression.
-/
theorem exists_smul_eq_of_forall_dual_dvd_of_projective [Module.Projective A M] {a : A} {m : M}
    (h : ∀ φ : Module.Dual A M, a ∣ φ m) : ∃ m', a • m' = m := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  choose c hc using fun i : M => h (Finsupp.lapply i ∘ₗ s)
  refine ⟨∑ i ∈ (s m).support, c i • i, ?_⟩
  conv_rhs => rw [← hs m, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl

/- English proof (translation)
Use `choose c hc using h`. Set `ψ : Module.Dual A (Module.Dual A M)` to `{ toFun := c map_add' := fun φ φ' => mul_left_cancel₀ ha (by rw [mul_add, ← hc, ← hc, ← hc]; rfl) map_smul' := fun r φ => mul_left_cancel₀ ha (by`. Rewrite using `[RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hc, ← hc]`. Use the proof step `rfl) }`. Take `⟨m', hm'⟩` from `(Module.bijective_dual_eval A M).2 ψ`.

Use `⟨m', (Module.bijective_dual_eval A M).1 (LinearMap.ext fun φ => ?_)⟩` and prove the remaining obligations. Rewrite using `[map_smul, hm', LinearMap.smul_apply, Module.Dual.eval_apply, hc]`. Both sides reduce to the same expression.
-/
theorem exists_smul_eq_of_forall_dual_dvd_of_isReflexive [IsDomain A] [Module.IsReflexive A M]
    {a : A} (ha : a ≠ 0) {m : M} (h : ∀ φ : Module.Dual A M, a ∣ φ m) : ∃ m', a • m' = m := by
  choose c hc using h
  let ψ : Module.Dual A (Module.Dual A M) :=
    { toFun := c
      map_add' := fun φ φ' => mul_left_cancel₀ ha (by rw [mul_add, ← hc, ← hc, ← hc]; rfl)
      map_smul' := fun r φ => mul_left_cancel₀ ha (by
        rw [RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hc, ← hc]; rfl) }
  obtain ⟨m', hm'⟩ := (Module.bijective_dual_eval A M).2 ψ
  refine ⟨m', (Module.bijective_dual_eval A M).1 (LinearMap.ext fun φ => ?_)⟩
  rw [map_smul, hm', LinearMap.smul_apply, Module.Dual.eval_apply, hc]
  rfl

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {V : Type*} [AddCommGroup V] [Module A V]

/- English proof (translation)
Take `⟨m, hm⟩` from `hav`. Take `⟨m', hm'⟩` from `hM ha (m := m) fun φ => dvd_of_forall_height_eq_one ha fun p _ hp hap => by`. Take `⟨s, hs, n, hn⟩` from `h p hp hap`. Use `⟨s, hs, φ n, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul]`.

Use `congr 1`. Apply `hf` to reduce the goal to its premises. Rewrite using `[map_smul, map_smul, hm, hn, smul_comm]`. Use `⟨m', smul_right_injective V ha ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← map_smul, hm', hm]`.
-/
theorem mem_range_of_forall_height_eq_one_of_dual
    (hM : ∀ {a : A}, a ≠ 0 → ∀ {m : M}, (∀ φ : Module.Dual A M, a ∣ φ m) → ∃ m', a • m' = m)
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V] {v : V} {a : A}
    (ha : a ≠ 0) (hav : a • v ∈ LinearMap.range f)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p →
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f) :
    v ∈ LinearMap.range f := by
  obtain ⟨m, hm⟩ := hav
  obtain ⟨m', hm'⟩ := hM ha (m := m) fun φ => dvd_of_forall_height_eq_one ha fun p _ hp hap => by
    obtain ⟨s, hs, n, hn⟩ := h p hp hap
    refine ⟨s, hs, φ n, ?_⟩
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul]
    congr 1
    apply hf
    rw [map_smul, map_smul, hm, hn, smul_comm]
  refine ⟨m', smul_right_injective V ha ?_⟩
  simp only
  rw [← map_smul, hm', hm]

/- English proof (translation)
The claim follows from `mem_range_of_forall_height_eq_one_of_dual (fun _ _ => exists_smul_eq_of_forall_dual_dvd_of_projective) f hf ha hav h`.
-/
theorem mem_range_of_forall_height_eq_one_of_projective [Module.Projective A M]
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V] {v : V} {a : A}
    (ha : a ≠ 0) (hav : a • v ∈ LinearMap.range f)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p →
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f) :
    v ∈ LinearMap.range f :=
  mem_range_of_forall_height_eq_one_of_dual
    (fun _ _ => exists_smul_eq_of_forall_dual_dvd_of_projective) f hf ha hav h

/- English proof (translation)
The claim follows from `mem_range_of_forall_height_eq_one_of_dual (fun ha _ => exists_smul_eq_of_forall_dual_dvd_of_isReflexive ha) f hf ha hav h`.
-/
theorem mem_range_of_forall_height_eq_one_of_isReflexive [Module.IsReflexive A M]
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V] {v : V} {a : A}
    (ha : a ≠ 0) (hav : a • v ∈ LinearMap.range f)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p →
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f) :
    v ∈ LinearMap.range f :=
  mem_range_of_forall_height_eq_one_of_dual
    (fun ha _ => exists_smul_eq_of_forall_dual_dvd_of_isReflexive ha) f hf ha hav h

omit [IsNoetherianRing A] [IsIntegrallyClosed A] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun r hr => ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f (⟨r, hr.mem_nonZeroDivisors⟩ : A⁰))).1⟩`.
-/
theorem isTorsionFree_of_isLocalizedModule (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] :
    Module.IsTorsionFree A V :=
  ⟨fun r hr => ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units f (⟨r, hr.mem_nonZeroDivisors⟩ : A⁰))).1⟩

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in

/- English proof (translation)
The claim follows from `(IsLocalizedModule.injective_iff_isRegular A⁰ f).mpr fun c => (isRegular_iff_mem_nonZeroDivisors.mpr c.2).isSMulRegular`.
-/
theorem injective_of_isLocalizedModule_nonZeroDivisors [Module.IsTorsionFree A M]
    (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] : Function.Injective f :=
  (IsLocalizedModule.injective_iff_isRegular A⁰ f).mpr fun c =>
    (isRegular_iff_mem_nonZeroDivisors.mpr c.2).isSMulRegular

/- English proof (translation)
Use `⟨fun hv p _ _ => ⟨1, (Ideal.ne_top_iff_one p).mp Ideal.IsPrime.ne_top', by simpa⟩, fun h => ?_⟩` and prove the remaining obligations. Use `isTorsionFree_of_isLocalizedModule f` as an intermediate fact. Take `⟨⟨m, a⟩, e⟩` from `IsLocalizedModule.surj A⁰ f v`. Conclude with `mem_range_of_forall_height_eq_one_of_projective f (injective_of_isLocalizedModule_nonZeroDivisors f) (nonZeroDivisors.ne_zero a.2) ⟨m, e.symm⟩ fun p _ hp _ => h p hp`.
-/
theorem mem_range_iff_forall_height_eq_one_of_projective [Module.Projective A M]
    (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] (v : V) :
    v ∈ LinearMap.range f ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f := by
  refine ⟨fun hv p _ _ => ⟨1, (Ideal.ne_top_iff_one p).mp Ideal.IsPrime.ne_top', by simpa⟩,
    fun h => ?_⟩
  have := isTorsionFree_of_isLocalizedModule f
  obtain ⟨⟨m, a⟩, e⟩ := IsLocalizedModule.surj A⁰ f v
  exact mem_range_of_forall_height_eq_one_of_projective f
    (injective_of_isLocalizedModule_nonZeroDivisors f) (nonZeroDivisors.ne_zero a.2) ⟨m, e.symm⟩
    fun p _ hp _ => h p hp

/- English proof (translation)
Use `⟨fun hv p _ _ => ⟨1, (Ideal.ne_top_iff_one p).mp Ideal.IsPrime.ne_top', by simpa⟩, fun h => ?_⟩` and prove the remaining obligations. Use `isTorsionFree_of_isLocalizedModule f` as an intermediate fact. Take `⟨⟨m, a⟩, e⟩` from `IsLocalizedModule.surj A⁰ f v`. Conclude with `mem_range_of_forall_height_eq_one_of_isReflexive f (injective_of_isLocalizedModule_nonZeroDivisors f) (nonZeroDivisors.ne_zero a.2) ⟨m, e.symm⟩ fun p _ hp _ => h p hp`.
-/
theorem mem_range_iff_forall_height_eq_one_of_isReflexive [Module.IsReflexive A M]
    (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] (v : V) :
    v ∈ LinearMap.range f ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f := by
  refine ⟨fun hv p _ _ => ⟨1, (Ideal.ne_top_iff_one p).mp Ideal.IsPrime.ne_top', by simpa⟩,
    fun h => ?_⟩
  have := isTorsionFree_of_isLocalizedModule f
  obtain ⟨⟨m, a⟩, e⟩ := IsLocalizedModule.surj A⁰ f v
  exact mem_range_of_forall_height_eq_one_of_isReflexive f
    (injective_of_isLocalizedModule_nonZeroDivisors f) (nonZeroDivisors.ne_zero a.2) ⟨m, e.symm⟩
    fun p _ hp _ => h p hp

/- English proof (translation)
Introduce `v hv` and use `by obtain ⟨a, ha, hav⟩ := h₀ v hv simpa using mem_range_of_forall_height_eq_one_of_projective N'.subtype N'.subtype_injective (v := v) ha (by simpa) fun p _ hp _ => by simpa using h p hp v hv`.
-/
theorem le_of_forall_height_eq_one_of_projective [Module.IsTorsionFree A V]
    {N N' : Submodule A V} [Module.Projective A N']
    (h₀ : ∀ v ∈ N, ∃ a : A, a ≠ 0 ∧ a • v ∈ N')
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∀ v ∈ N, ∃ s, s ∉ p ∧ s • v ∈ N') :
    N ≤ N' := fun v hv => by
  obtain ⟨a, ha, hav⟩ := h₀ v hv
  simpa using mem_range_of_forall_height_eq_one_of_projective N'.subtype N'.subtype_injective
    (v := v) ha (by simpa) fun p _ hp _ => by simpa using h p hp v hv

/- English proof (translation)
Introduce `v hv` and use `by obtain ⟨a, ha, hav⟩ := h₀ v hv simpa using mem_range_of_forall_height_eq_one_of_isReflexive N'.subtype N'.subtype_injective (v := v) ha (by simpa) fun p _ hp _ => by simpa using h p hp v hv`.
-/
theorem le_of_forall_height_eq_one_of_isReflexive [Module.IsTorsionFree A V]
    {N N' : Submodule A V} [Module.IsReflexive A N']
    (h₀ : ∀ v ∈ N, ∃ a : A, a ≠ 0 ∧ a • v ∈ N')
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∀ v ∈ N, ∃ s, s ∉ p ∧ s • v ∈ N') :
    N ≤ N' := fun v hv => by
  obtain ⟨a, ha, hav⟩ := h₀ v hv
  simpa using mem_range_of_forall_height_eq_one_of_isReflexive N'.subtype N'.subtype_injective
    (v := v) ha (by simpa) fun p _ hp _ => by simpa using h p hp v hv

/- English proof (translation)
Take `⟨hpp, x, hx⟩` from `isAssociatedPrime_iff.mp hp`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hmem : ∀ r, r ∈ p ↔ r • v ∈ LinearMap.range f` using `fun r => by`. Rewrite using `[hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨a, ha, hav⟩` from `ht v`.

Assume the negation of the conclusion as `hne`. Use `hpp.ne_top ((Ideal.eq_top_iff_one p).mpr ((hmem 1).mpr ?_))` and prove the remaining obligations. Rewrite using `[one_smul]`. Use `mem_range_of_forall_height_eq_one_of_dual hM f hf ha hav fun q _ hq haq => ?_` and prove the remaining obligations. Use `by_contra! H`.

Establish `hle : p ≤ q` using `fun s hs => by_contra fun hsq => H s hsq ((hmem s).mp hs)`. Establish `hge` using `(mem_minimalPrimes_span_singleton_of_height_eq_one hq ha haq).2 ⟨hpp, (Ideal.span_singleton_le_iff_mem p).mpr ((hmem a).mpr hav)⟩ hle`. Conclude with `hne (le_antisymm hle hge ▸ hq)`.
-/
theorem height_eq_one_of_mem_associatedPrimes_coker_of_dual
    (hM : ∀ {a : A}, a ≠ 0 → ∀ {m : M}, (∀ φ : Module.Dual A M, a ∣ φ m) → ∃ m', a • m' = m)
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V]
    (ht : ∀ v : V, ∃ a : A, a ≠ 0 ∧ a • v ∈ LinearMap.range f) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (V ⧸ LinearMap.range f)) : p.height = 1 := by
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hmem : ∀ r, r ∈ p ↔ r • v ∈ LinearMap.range f := fun r => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
  obtain ⟨a, ha, hav⟩ := ht v
  by_contra hne
  refine hpp.ne_top ((Ideal.eq_top_iff_one p).mpr ((hmem 1).mpr ?_))
  rw [one_smul]
  refine mem_range_of_forall_height_eq_one_of_dual hM f hf ha hav fun q _ hq haq => ?_
  by_contra! H
  have hle : p ≤ q := fun s hs => by_contra fun hsq => H s hsq ((hmem s).mp hs)
  have hge := (mem_minimalPrimes_span_singleton_of_height_eq_one hq ha haq).2
    ⟨hpp, (Ideal.span_singleton_le_iff_mem p).mpr ((hmem a).mpr hav)⟩ hle
  exact hne (le_antisymm hle hge ▸ hq)

/- English proof (translation)
The claim follows from `height_eq_one_of_mem_associatedPrimes_coker_of_dual (fun _ _ => exists_smul_eq_of_forall_dual_dvd_of_projective) f hf ht hp`.
-/
theorem height_eq_one_of_mem_associatedPrimes_coker_of_projective [Module.Projective A M]
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V]
    (ht : ∀ v : V, ∃ a : A, a ≠ 0 ∧ a • v ∈ LinearMap.range f) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (V ⧸ LinearMap.range f)) : p.height = 1 :=
  height_eq_one_of_mem_associatedPrimes_coker_of_dual
    (fun _ _ => exists_smul_eq_of_forall_dual_dvd_of_projective) f hf ht hp

/- English proof (translation)
The claim follows from `height_eq_one_of_mem_associatedPrimes_coker_of_dual (fun ha _ => exists_smul_eq_of_forall_dual_dvd_of_isReflexive ha) f hf ht hp`.
-/
theorem height_eq_one_of_mem_associatedPrimes_coker_of_isReflexive [Module.IsReflexive A M]
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V]
    (ht : ∀ v : V, ∃ a : A, a ≠ 0 ∧ a • v ∈ LinearMap.range f) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (V ⧸ LinearMap.range f)) : p.height = 1 :=
  height_eq_one_of_mem_associatedPrimes_coker_of_dual
    (fun ha _ => exists_smul_eq_of_forall_dual_dvd_of_isReflexive ha) f hf ht hp

end Module

section Fraction

variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

noncomputable abbrev primeLocalSubalgebra (p : Ideal A) [p.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors

variable {K}

section AnyLocalization

variable (p : Ideal A) [p.IsPrime] (B : Type*) [CommRing B] [Algebra A B]
  [IsLocalization.AtPrime B p] [Algebra B K] [IsScalarTower A B K]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Take `⟨⟨m, s⟩, e⟩` from `IsLocalizedModule.surj p.primeCompl (TensorProduct.mk A B M 1) w`. Use `⟨s, s.2, m, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul]`.

Express the relevant statement in the definitionally equal form `_ = LinearMap.rTensor M _ (s • w)`. Rewrite using `[e]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨s, hs, m, e⟩`. Use `isTorsionFree_of_isLocalizedModule (TensorProduct.mk A K M 1)` as an intermediate fact.

Establish `hs0 : s ≠ 0` using `fun h => hs (h ▸ p.zero_mem)`. Use `⟨IsLocalization.mk' B (1 : A) (⟨s, hs⟩ : p.primeCompl) ⊗ₜ m, smul_right_injective _ hs0 ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← e, ← map_smul, TensorProduct.smul_tmul', Algebra.smul_def, IsLocalization.mk'_spec' B (1 : A) (⟨s, hs⟩ : p.primeCompl)]`. Simplify using the standard rewrite rules.
-/
theorem mem_range_rTensor_iff {M : Type*} [AddCommGroup M] [Module A M] (v : K ⊗[A] M) :
    v ∈ LinearMap.range ((IsScalarTower.toAlgHom A B K).toLinearMap.rTensor M) ↔
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range (TensorProduct.mk A K M 1) := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨m, s⟩, e⟩ := IsLocalizedModule.surj p.primeCompl (TensorProduct.mk A B M 1) w
    refine ⟨s, s.2, m, ?_⟩
    rw [← map_smul]
    change _ = LinearMap.rTensor M _ (s • w)
    rw [e]
    simp
  · rintro ⟨s, hs, m, e⟩
    have := isTorsionFree_of_isLocalizedModule (TensorProduct.mk A K M 1)
    have hs0 : s ≠ 0 := fun h => hs (h ▸ p.zero_mem)
    refine ⟨IsLocalization.mk' B (1 : A) (⟨s, hs⟩ : p.primeCompl) ⊗ₜ m,
      smul_right_injective _ hs0 ?_⟩
    simp only
    rw [← e, ← map_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      IsLocalization.mk'_spec' B (1 : A) (⟨s, hs⟩ : p.primeCompl)]
    simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Take `⟨⟨m, s⟩, e⟩` from `IsLocalization.surj p.primeCompl w`. Use `⟨s, s.2, m, ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply A B K, ← e, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def, mul_comm]`.

Introduce and unpack `⟨s, hs, m, e⟩`. Establish `hs0 : algebraMap A K s ≠ 0` using `IsFractionRing.to_map_eq_zero_iff.not.mpr fun h => hs (h ▸ p.zero_mem)`. Use `⟨IsLocalization.mk' B m (⟨s, hs⟩ : p.primeCompl), mul_left_cancel₀ hs0 ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def, ← Algebra.smul_def, ← e, Algebra.smul_def, IsScalarTower.algebraMap_apply A B K, ← map_mul, IsLocalization.mk'_spec' B m (⟨s, hs⟩ : p.primeCompl), ← IsScalarTower.algebraMap_apply]`.
-/
theorem mem_range_algebraMap_atPrime_iff (x : K) :
    x ∈ (algebraMap B K).range ↔ ∃ s, s ∉ p ∧ s • x ∈ (algebraMap A K).range := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨m, s⟩, e⟩ := IsLocalization.surj p.primeCompl w
    refine ⟨s, s.2, m, ?_⟩
    rw [IsScalarTower.algebraMap_apply A B K, ← e, map_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.smul_def, mul_comm]
  · rintro ⟨s, hs, m, e⟩
    have hs0 : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_eq_zero_iff.not.mpr fun h => hs (h ▸ p.zero_mem)
    refine ⟨IsLocalization.mk' B m (⟨s, hs⟩ : p.primeCompl), mul_left_cancel₀ hs0 ?_⟩
    rw [← Algebra.smul_def, ← Algebra.smul_def, ← e, Algebra.smul_def,
      IsScalarTower.algebraMap_apply A B K, ← map_mul,
      IsLocalization.mk'_spec' B m (⟨s, hs⟩ : p.primeCompl), ← IsScalarTower.algebraMap_apply]

end AnyLocalization

/- English proof (translation)
Rewrite using `[← mem_range_algebraMap_atPrime_iff p (primeLocalSubalgebra K p)]`. Conclude with `⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, h⟩ => h ▸ y.2⟩`.
-/
theorem mem_primeLocalSubalgebra_iff (p : Ideal A) [p.IsPrime] (x : K) :
    x ∈ primeLocalSubalgebra K p ↔ ∃ s, s ∉ p ∧ s • x ∈ (algebraMap A K).range := by
  rw [← mem_range_algebraMap_atPrime_iff p (primeLocalSubalgebra K p)]
  exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, h⟩ => h ▸ y.2⟩

/- English proof (translation)
Rewrite using `[mem_range_algebraMap_atPrime_iff p B, mem_primeLocalSubalgebra_iff]`.
-/
theorem mem_range_algebraMap_iff_mem_primeLocalSubalgebra (p : Ideal A) [p.IsPrime]
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.AtPrime B p] [Algebra B K]
    [IsScalarTower A B K] (x : K) :
    x ∈ (algebraMap B K).range ↔ x ∈ primeLocalSubalgebra K p := by
  rw [mem_range_algebraMap_atPrime_iff p B, mem_primeLocalSubalgebra_iff]

variable [IsNoetherianRing A]

variable (K) in

noncomputable def heightOneOrdHom (p : Ideal A) [p.IsPrime] (hp : p.height = 1) : K →*₀ ℤᵐ⁰ :=
  haveI := IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance
  haveI := krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)
  Ring.ordFrac (primeLocalSubalgebra K p)

noncomputable def heightOneOrd_vw (p : Ideal A) [p.IsPrime] (hp : p.height = 1) (x : K) : ℤ :=
  WithZero.log (heightOneOrdHom K p hp x)

omit [IsDomain A] [IsNoetherianRing A] in

/- English proof (translation)
Set `` to `(e : A →+* B).toAlgebra`. Rewrite using `[Ring.ord, Ring.ord, ← Module.length_eq_of_surjective (S := A) (R := B) e.surjective]`. Set `e' : A ≃ₐ[A] B` to `{ e with commutes' := fun _ => rfl }`. Conclude with `(Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) e' (by rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq.symm`.
-/
theorem ord_map_ringEquiv {B : Type*} [CommRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  let := (e : A →+* B).toAlgebra
  rw [Ring.ord, Ring.ord, ← Module.length_eq_of_surjective (S := A) (R := B) e.surjective]
  let e' : A ≃ₐ[A] B := { e with commutes' := fun _ => rfl }
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) e'
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq.symm

/- English proof (translation)
Use `IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance` as an intermediate fact. Use `krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)` as an intermediate fact. Establish `key : ∀ a : A, a ≠ 0 → Ring.ordFrac B (algebraMap A K a) = heightOneOrdHom K p hp (algebraMap A K a)`. Introduce `a ha`. Use `(FaithfulSMul.algebraMap_injective B K).isDomain` as an intermediate fact.

Set `e` to `IsLocalization.algEquiv p.primeCompl B (primeLocalSubalgebra K p)`. Establish `h1 : algebraMap A B a ≠ 0` using `(map_ne_zero_iff _ (IsLocalization.injective B p.primeCompl_le_nonZeroDivisors)).mpr ha`. Establish `h2 : algebraMap A (primeLocalSubalgebra K p) a ≠ 0` using `(map_ne_zero_iff _ (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors)).mpr ha`. Use `conv_lhs => rw [IsScalarTower.algebraMap_apply A B K]`. Use `conv_rhs => rw [IsScalarTower.algebraMap_apply A (primeLocalSubalgebra K p) K]`.

Rewrite using `[heightOneOrdHom, Ring.ordFrac_eq_ord _ h1, Ring.ordFrac_eq_ord _ h2, Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero h1), Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero h2), ← ord_map_ringEquiv e.toRingEquiv (algebraMap A B a)]`. Use `congr 2`. Conclude with `e.commutes a`. Use extensionality with `x`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := A) x`.

Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Rewrite using `[map_div₀, map_div₀, key a ha, key b (nonZeroDivisors.ne_zero hb)]`.
-/
theorem ordFrac_eq_heightOneOrdHom (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
    (B : Type*) [CommRing B] [Nontrivial B] [Algebra A B] [IsLocalization.AtPrime B p]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B] [Algebra B K] [IsScalarTower A B K]
    [IsFractionRing B K] : Ring.ordFrac B = heightOneOrdHom K p hp := by
  have := IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance
  have := krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)
  have key : ∀ a : A, a ≠ 0 →
      Ring.ordFrac B (algebraMap A K a) = heightOneOrdHom K p hp (algebraMap A K a) := by
    intro a ha
    have := (FaithfulSMul.algebraMap_injective B K).isDomain
    let e := IsLocalization.algEquiv p.primeCompl B (primeLocalSubalgebra K p)
    have h1 : algebraMap A B a ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective B p.primeCompl_le_nonZeroDivisors)).mpr ha
    have h2 : algebraMap A (primeLocalSubalgebra K p) a ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors)).mpr ha
    conv_lhs => rw [IsScalarTower.algebraMap_apply A B K]
    conv_rhs => rw [IsScalarTower.algebraMap_apply A (primeLocalSubalgebra K p) K]
    rw [heightOneOrdHom, Ring.ordFrac_eq_ord _ h1, Ring.ordFrac_eq_ord _ h2,
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero h1),
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero h2),
      ← ord_map_ringEquiv e.toRingEquiv (algebraMap A B a)]
    congr 2
    exact e.commutes a
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  by_cases ha : a = 0
  · simp [ha]
  rw [map_div₀, map_div₀, key a ha, key b (nonZeroDivisors.ne_zero hb)]

section Ord

variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)

/- English proof (translation)
The claim follows from `(WithZero.exp_log ((map_ne_zero _).mpr hx)).symm`.
-/
theorem heightOneOrdHom_eq_exp {x : K} (hx : x ≠ 0) :
    heightOneOrdHom K p hp x = WithZero.exp (heightOneOrd_vw p hp x) :=
  (WithZero.exp_log ((map_ne_zero _).mpr hx)).symm

/- English proof (translation)
Rewrite using `[heightOneOrd_vw, map_mul, WithZero.log_mul ((map_ne_zero _).mpr hx) ((map_ne_zero _).mpr hy)]`. Both sides reduce to the same expression.
-/
theorem heightOneOrd_vw_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    heightOneOrd_vw p hp (x * y) = heightOneOrd_vw p hp x + heightOneOrd_vw p hp y := by
  rw [heightOneOrd_vw, map_mul,
    WithZero.log_mul ((map_ne_zero _).mpr hx) ((map_ne_zero _).mpr hy)]
  rfl

/- English proof (translation)
Rewrite using `[heightOneOrd_vw, map_inv₀, WithZero.log_inv]`. Both sides reduce to the same expression.
-/
theorem heightOneOrd_vw_inv (x : K) :
    heightOneOrd_vw p hp x⁻¹ = -heightOneOrd_vw p hp x := by
  rw [heightOneOrd_vw, map_inv₀, WithZero.log_inv]
  rfl

/- English proof (translation)
Rewrite using `[div_eq_mul_inv, heightOneOrd_vw_mul p hp hx (inv_ne_zero hy), heightOneOrd_vw_inv, sub_eq_add_neg]`.
-/
theorem heightOneOrd_vw_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    heightOneOrd_vw p hp (x / y) = heightOneOrd_vw p hp x - heightOneOrd_vw p hp y := by
  rw [div_eq_mul_inv, heightOneOrd_vw_mul p hp hx (inv_ne_zero hy), heightOneOrd_vw_inv,
    sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[heightOneOrd_vw, map_zpow₀, WithZero.log_zpow]`. Both sides reduce to the same expression.
-/
theorem heightOneOrd_vw_zpow (x : K) (n : ℤ) :
    heightOneOrd_vw p hp (x ^ n) = n * heightOneOrd_vw p hp x := by
  rw [heightOneOrd_vw, map_zpow₀, WithZero.log_zpow]
  rfl

/- English proof (translation)
Use `IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance` as an intermediate fact. Use `krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)` as an intermediate fact. Rewrite using `[heightOneOrd_vw, heightOneOrdHom, IsScalarTower.algebraMap_apply A (primeLocalSubalgebra K p) K, Ring.ordFrac_of_isUnit (IsLocalization.map_units _ (⟨a, ha⟩ : p.primeCompl)), WithZero.log_one]`.
-/
theorem heightOneOrd_vw_algebraMap_of_notMem {a : A} (ha : a ∉ p) :
    heightOneOrd_vw p hp (algebraMap A K a) = 0 := by
  have := IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance
  have := krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)
  rw [heightOneOrd_vw, heightOneOrdHom,
    IsScalarTower.algebraMap_apply A (primeLocalSubalgebra K p) K,
    Ring.ordFrac_of_isUnit (IsLocalization.map_units _ (⟨a, ha⟩ : p.primeCompl)), WithZero.log_one]

/- English proof (translation)
Use `IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance` as an intermediate fact. Use `krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)` as an intermediate fact. Establish `h1 : 1 ≤ heightOneOrdHom K p hp x` using `Ring.ordFrac_ge_one_of_ne_zero (R := primeLocalSubalgebra K p) (x := ⟨x, h⟩) (fun e => hx (congrArg Subtype.val e))`. Rewrite `h1` using `[heightOneOrdHom_eq_exp p hp hx, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Then use the resulting hypothesis.
-/
theorem heightOneOrd_vw_nonneg_of_mem {x : K} (hx : x ≠ 0) (h : x ∈ primeLocalSubalgebra K p) :
    0 ≤ heightOneOrd_vw p hp x := by
  have := IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance
  have := krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)
  have h1 : 1 ≤ heightOneOrdHom K p hp x :=
    Ring.ordFrac_ge_one_of_ne_zero (R := primeLocalSubalgebra K p) (x := ⟨x, h⟩)
      (fun e => hx (congrArg Subtype.val e))
  rwa [heightOneOrdHom_eq_exp p hp hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1

end Ord

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := A) x`. Establish `hb0` using `nonZeroDivisors.ne_zero hb`. Establish `ha : a ≠ 0` using `by rintro rfl; simp at hx`. Use `((finite_height_eq_one_mem ha).union (finite_height_eq_one_mem hb0)).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, h⟩`.

Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, hp, true_and, not_or] at hn`. Apply `h` to reduce the goal to its premises. Rewrite using `[heightOneOrd_vw_div _ _ (IsFractionRing.to_map_eq_zero_iff.not.mpr ha) (IsFractionRing.to_map_eq_zero_iff.not.mpr hb0), heightOneOrd_vw_algebraMap_of_notMem _ _ hn.1, heightOneOrd_vw_algebraMap_of_notMem _ _ hn.2, sub_zero]`.
-/
theorem finite_heightOneOrd_vw_ne_zero {x : K} (hx : x ≠ 0) :
    {p : PrimeSpectrum A |
      ∃ hp : p.asIdeal.height = 1, heightOneOrd_vw p.asIdeal hp x ≠ 0}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  refine ((finite_height_eq_one_mem ha).union (finite_height_eq_one_mem hb0)).subset ?_
  rintro p ⟨hp, h⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, hp, true_and, not_or] at hn
  apply h
  rw [heightOneOrd_vw_div _ _ (IsFractionRing.to_map_eq_zero_iff.not.mpr ha)
    (IsFractionRing.to_map_eq_zero_iff.not.mpr hb0), heightOneOrd_vw_algebraMap_of_notMem _ _ hn.1,
    heightOneOrd_vw_algebraMap_of_notMem _ _ hn.2, sub_zero]

variable [IsIntegrallyClosed A]

/- English proof (translation)
The claim follows from `mem_range_of_forall_height_eq_one_of_projective (Algebra.linearMap A K) (IsFractionRing.injective A K) ha hax fun p _ hp hap => (mem_primeLocalSubalgebra_iff p x).mp (h p hp hap)`.
-/
theorem mem_range_algebraMap_of_forall_height_eq_one_mem {x : K} {a : A} (ha : a ≠ 0)
    (hax : a • x ∈ (algebraMap A K).range)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → x ∈ primeLocalSubalgebra K p) :
    x ∈ (algebraMap A K).range :=
  mem_range_of_forall_height_eq_one_of_projective (Algebra.linearMap A K)
    (IsFractionRing.injective A K) ha hax fun p _ hp hap =>
      (mem_primeLocalSubalgebra_iff p x).mp (h p hp hap)

/- English proof (translation)
The claim follows from `mem_range_algebraMap_of_forall_height_eq_one_mem (pow_ne_zero n ha) hax fun p hp h1 hap => h p h1 (hp.mem_of_pow_mem n hap)`.
-/
theorem mem_range_algebraMap_of_pow_smul_mem {x : K} {a : A} (ha : a ≠ 0) {n : ℕ}
    (hax : a ^ n • x ∈ (algebraMap A K).range)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p → x ∈ primeLocalSubalgebra K p) :
    x ∈ (algebraMap A K).range :=
  mem_range_algebraMap_of_forall_height_eq_one_mem (pow_ne_zero n ha) hax
    fun p hp h1 hap => h p h1 (hp.mem_of_pow_mem n hap)

/- English proof (translation)
Simplify using `only [mem_primeLocalSubalgebra_iff]`. Conclude with `mem_range_iff_forall_height_eq_one_of_projective (Algebra.linearMap A K) x`.
-/
theorem mem_range_algebraMap_iff_forall_height_eq_one (x : K) :
    x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → x ∈ primeLocalSubalgebra K p := by
  simp only [mem_primeLocalSubalgebra_iff]
  exact mem_range_iff_forall_height_eq_one_of_projective (Algebra.linearMap A K) x

variable (A K) in

/- English proof (translation)
Use `bot_unique fun x hx => Algebra.mem_bot.mpr ?_` and prove the remaining obligations. Conclude with `(mem_range_algebraMap_iff_forall_height_eq_one x).mpr fun p hp h1 => Algebra.mem_iInf.mp hx ⟨⟨p, hp⟩, h1⟩`.
-/
theorem iInf_primeLocalSubalgebra_height_eq_one :
    ⨅ p : {p : PrimeSpectrum A // p.asIdeal.height = 1}, primeLocalSubalgebra K p.1.asIdeal = ⊥ := by
  refine bot_unique fun x hx => Algebra.mem_bot.mpr ?_
  exact (mem_range_algebraMap_iff_forall_height_eq_one x).mpr fun p hp h1 =>
    Algebra.mem_iInf.mp hx ⟨⟨p, hp⟩, h1⟩

/- English proof (translation)
Rewrite using `[mem_range_iff_forall_height_eq_one_of_projective]`. Conclude with `forall_congr' fun p => forall_congr' fun _ => forall_congr' fun _ => (mem_range_rTensor_iff p (primeLocalSubalgebra K p) v).symm`.
-/
theorem mem_range_tensor_iff_forall_height_eq_one {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Projective A M] (v : K ⊗[A] M) :
    v ∈ LinearMap.range (TensorProduct.mk A K M 1) ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
        v ∈ LinearMap.range ((primeLocalSubalgebra K p).val.toLinearMap.rTensor M) := by
  rw [mem_range_iff_forall_height_eq_one_of_projective]
  exact forall_congr' fun p => forall_congr' fun _ => forall_congr' fun _ =>
    (mem_range_rTensor_iff p (primeLocalSubalgebra K p) v).symm

/- English proof (translation)
Rewrite using `[mem_range_iff_forall_height_eq_one_of_isReflexive]`. Conclude with `forall_congr' fun p => forall_congr' fun _ => forall_congr' fun _ => (mem_range_rTensor_iff p (primeLocalSubalgebra K p) v).symm`.
-/
theorem mem_range_tensor_iff_forall_height_eq_one_of_isReflexive {M : Type*} [AddCommGroup M]
    [Module A M] [Module.IsReflexive A M] (v : K ⊗[A] M) :
    v ∈ LinearMap.range (TensorProduct.mk A K M 1) ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
        v ∈ LinearMap.range ((primeLocalSubalgebra K p).val.toLinearMap.rTensor M) := by
  rw [mem_range_iff_forall_height_eq_one_of_isReflexive]
  exact forall_congr' fun p => forall_congr' fun _ => forall_congr' fun _ =>
    (mem_range_rTensor_iff p (primeLocalSubalgebra K p) v).symm

section Ord

variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)

omit [IsIntegrallyClosed A] in

/- English proof (translation)
Rewrite using `[← ordFrac_eq_heightOneOrdHom p hp B, Ring.ordFrac_eq_valuation_inv]`.
-/
theorem heightOneOrdHom_eq_valuation_inv (B : Type*) [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [IsLocalization.AtPrime B p] [Algebra B K]
    [IsScalarTower A B K] [IsFractionRing B K] (x : K) :
    heightOneOrdHom K p hp x = ((IsDiscreteValuationRing.maximalIdeal B).valuation K x)⁻¹ := by
  rw [← ordFrac_eq_heightOneOrdHom p hp B, Ring.ordFrac_eq_valuation_inv]

/- English proof (translation)
Use `isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)` as an intermediate fact. Rewrite using `[heightOneOrd_vw, ← ordFrac_eq_heightOneOrdHom p hp (primeLocalSubalgebra K p)]`. Conclude with `(congrArg WithZero.log (Ring.ordFrac_irreducible (K := K) hϖ)).trans (WithZero.log_exp 1)`.
-/
theorem heightOneOrd_vw_of_irreducible {ϖ : primeLocalSubalgebra K p} (hϖ : Irreducible ϖ) :
    heightOneOrd_vw p hp (ϖ : K) = 1 := by
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  rw [heightOneOrd_vw, ← ordFrac_eq_heightOneOrdHom p hp (primeLocalSubalgebra K p)]
  exact (congrArg WithZero.log (Ring.ordFrac_irreducible (K := K) hϖ)).trans (WithZero.log_exp 1)

/- English proof (translation)
Use `isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)` as an intermediate fact. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (primeLocalSubalgebra K p)`. Use `⟨(ϖ : K) ^ n, zpow_ne_zero n fun e => hϖ.ne_zero (Subtype.ext e), ?_⟩` and prove the remaining obligations. Rewrite using `[heightOneOrd_vw_zpow, heightOneOrd_vw_of_irreducible p hp hϖ, mul_one]`.
-/
theorem exists_heightOneOrd_vw_eq (n : ℤ) : ∃ x : K, x ≠ 0 ∧ heightOneOrd_vw p hp x = n := by
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (primeLocalSubalgebra K p)
  refine ⟨(ϖ : K) ^ n, zpow_ne_zero n fun e => hϖ.ne_zero (Subtype.ext e), ?_⟩
  rw [heightOneOrd_vw_zpow, heightOneOrd_vw_of_irreducible p hp hϖ, mul_one]

/- English proof (translation)
Use `⟨heightOneOrd_vw_nonneg_of_mem p hp hx, fun h => ?_⟩` and prove the remaining obligations. Use `isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)` as an intermediate fact. Establish `h1 : 1 ≤ heightOneOrdHom K p hp x`. Rewrite using `[heightOneOrdHom_eq_exp p hp hx, ← WithZero.exp_zero, WithZero.exp_le_exp]` and apply the resulting hypothesis. Rewrite `h1` using `[heightOneOrdHom_eq_valuation_inv p hp (primeLocalSubalgebra K p), one_le_inv₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hx))]`.

Take `⟨y, rfl⟩` from `IsDiscreteValuationRing.exists_lift_of_le_one h1`. Conclude with `y.2`.
-/
theorem mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg {x : K} (hx : x ≠ 0) :
    x ∈ primeLocalSubalgebra K p ↔ 0 ≤ heightOneOrd_vw p hp x := by
  refine ⟨heightOneOrd_vw_nonneg_of_mem p hp hx, fun h => ?_⟩
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  have h1 : 1 ≤ heightOneOrdHom K p hp x := by
    rwa [heightOneOrdHom_eq_exp p hp hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [heightOneOrdHom_eq_valuation_inv p hp (primeLocalSubalgebra K p),
    one_le_inv₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hx))] at h1
  obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h1
  exact y.2

/- English proof (translation)
Establish `ha' : algebraMap A K a ≠ 0` using `IsFractionRing.to_map_eq_zero_iff.not.mpr ha`. Use `⟨fun h => by_contra fun hn => h.ne' (heightOneOrd_vw_algebraMap_of_notMem p hp hn), fun hap => lt_of_not_ge fun h => ?_⟩` and prove the remaining obligations. Establish `h1 : (algebraMap A K a)⁻¹ ∈ primeLocalSubalgebra K p`. Rewrite using `[mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp (inv_ne_zero ha'), heightOneOrd_vw_inv]`. Use linear arithmetic over natural numbers and integers.

Take `⟨s, hs, c, e⟩` from `(mem_primeLocalSubalgebra_iff p _).mp h1`. Establish `: s = c * a`. Apply `IsFractionRing.injective A K` to reduce the goal to its premises. Rewrite using `[map_mul, e, Algebra.smul_def, inv_mul_cancel_right₀ ha']`. Conclude with `hs (this ▸ p.mul_mem_left c hap)`.
-/
theorem heightOneOrd_vw_algebraMap_pos_iff {a : A} (ha : a ≠ 0) :
    0 < heightOneOrd_vw p hp (algebraMap A K a) ↔ a ∈ p := by
  have ha' : algebraMap A K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  refine ⟨fun h => by_contra fun hn => h.ne' (heightOneOrd_vw_algebraMap_of_notMem p hp hn),
    fun hap => lt_of_not_ge fun h => ?_⟩
  have h1 : (algebraMap A K a)⁻¹ ∈ primeLocalSubalgebra K p := by
    rw [mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp (inv_ne_zero ha'),
      heightOneOrd_vw_inv]
    omega
  obtain ⟨s, hs, c, e⟩ := (mem_primeLocalSubalgebra_iff p _).mp h1
  have : s = c * a := by
    apply IsFractionRing.injective A K
    rw [map_mul, e, Algebra.smul_def, inv_mul_cancel_right₀ ha']
  exact hs (this ▸ p.mul_mem_left c hap)

/- English proof (translation)
Use `isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)` as an intermediate fact. Establish `h` using `Ring.ordFrac_add (R := primeLocalSubalgebra K p) x y hxy`. Rewrite `h` using `[ordFrac_eq_heightOneOrdHom p hp, heightOneOrdHom_eq_exp p hp hx, heightOneOrdHom_eq_exp p hp hy, heightOneOrdHom_eq_exp p hp hxy, min_le_iff, WithZero.exp_le_exp, WithZero.exp_le_exp]`. Conclude with `min_le_iff.mpr h`.
-/
theorem min_le_heightOneOrd_vw_add {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (heightOneOrd_vw p hp x) (heightOneOrd_vw p hp y) ≤ heightOneOrd_vw p hp (x + y) := by
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  have h := Ring.ordFrac_add (R := primeLocalSubalgebra K p) x y hxy
  rw [ordFrac_eq_heightOneOrdHom p hp, heightOneOrdHom_eq_exp p hp hx,
    heightOneOrdHom_eq_exp p hp hy, heightOneOrdHom_eq_exp p hp hxy, min_le_iff,
    WithZero.exp_le_exp, WithZero.exp_le_exp] at h
  exact min_le_iff.mpr h

end Ord

/- English proof (translation)
Rewrite using `[mem_range_algebraMap_iff_forall_height_eq_one]`. Conclude with `forall_congr' fun p => forall_congr' fun _ => forall_congr' fun hp => mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp hx`.
-/
theorem mem_range_algebraMap_iff_heightOneOrd_vw_nonneg {x : K} (hx : x ≠ 0) :
    x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1), 0 ≤ heightOneOrd_vw p hp x := by
  rw [mem_range_algebraMap_iff_forall_height_eq_one]
  exact forall_congr' fun p => forall_congr' fun _ => forall_congr' fun hp =>
    mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp hx

/- English proof (translation)
Establish `h` using `mem_range_algebraMap_iff_heightOneOrd_vw_nonneg (A := A) (div_ne_zero hx hy)`. Simplify using `only [heightOneOrd_vw_div _ _ hx hy, sub_nonneg] at h`. Rewrite using `[← h, RingHom.mem_range]`. Conclude with `exists_congr fun a => by rw [Algebra.smul_def, eq_div_iff hy]`.
-/
theorem exists_smul_eq_iff_heightOneOrd_vw_le {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ a : A, a • y = x) ↔ ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      heightOneOrd_vw p hp y ≤ heightOneOrd_vw p hp x := by
  have h := mem_range_algebraMap_iff_heightOneOrd_vw_nonneg (A := A) (div_ne_zero hx hy)
  simp only [heightOneOrd_vw_div _ _ hx hy, sub_nonneg] at h
  rw [← h, RingHom.mem_range]
  exact exists_congr fun a => by rw [Algebra.smul_def, eq_div_iff hy]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu⟩ p _ hp`. Establish `hu' : ((u⁻¹ : Aˣ) : A) • x = y` using `by rw [← hu, ← Units.smul_def, inv_smul_smul]`. Conclude with `le_antisymm ((exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hy hx).mp ⟨_, hu'⟩ p hp) ((exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hx hy).mp ⟨u, hu⟩ p hp)`. Introduce `h`.

Take `⟨a, ha⟩` from `(exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hx hy).mpr fun p _ hp => (h p hp).ge`. Take `⟨b, hb⟩` from `(exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hy hx).mpr fun p _ hp => (h p hp).le`. Establish `hab : a * b = 1`. Apply `IsFractionRing.injective A K` to reduce the goal to its premises. Apply `mul_right_cancel₀ hx` to reduce the goal to its premises.

Rewrite using `[← Algebra.smul_def, mul_smul, hb, ha, map_one, one_mul]`. Conclude with `⟨Units.mkOfMulEqOne a b hab, ha⟩`.
-/
theorem exists_unit_smul_eq_iff_heightOneOrd_vw_eq {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ u : Aˣ, u • y = x) ↔ ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      heightOneOrd_vw p hp x = heightOneOrd_vw p hp y := by
  constructor
  · rintro ⟨u, hu⟩ p _ hp
    have hu' : ((u⁻¹ : Aˣ) : A) • x = y := by rw [← hu, ← Units.smul_def, inv_smul_smul]
    exact le_antisymm
      ((exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hy hx).mp ⟨_, hu'⟩ p hp)
      ((exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hx hy).mp ⟨u, hu⟩ p hp)
  · intro h
    obtain ⟨a, ha⟩ := (exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hx hy).mpr
      fun p _ hp => (h p hp).ge
    obtain ⟨b, hb⟩ := (exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hy hx).mpr
      fun p _ hp => (h p hp).le
    have hab : a * b = 1 := by
      apply IsFractionRing.injective A K
      apply mul_right_cancel₀ hx
      rw [← Algebra.smul_def, mul_smul, hb, ha, map_one, one_mul]
    exact ⟨Units.mkOfMulEqOne a b hab, ha⟩

end Fraction

/- English proof (translation)
Use `⟨fun p _ hp => ⟨isDiscreteValuationRing_of_height_eq_one p hp _, isDiscreteValuationRing_of_height_eq_one p hp _, fun x hx => ?_⟩, mem_range_algebraMap_iff_forall_height_eq_one, fun M _ _ _ => ⟨injective_of_isLocalizedModule_nonZeroDivisors _, mem_range_tensor_iff_forall_height_e …` and prove the remaining obligations. Use `isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)` as an intermediate fact. Rewrite using `[WithZero.exp_neg, ← heightOneOrdHom_eq_exp p hp hx, heightOneOrdHom_eq_valuation_inv p hp (primeLocalSubalgebra K p), inv_inv]`.
-/
theorem normal_domain_height_one.{u, v, w} (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (K : Type v) [Field K] [Algebra A K]
    [IsFractionRing A K] :
    (∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      IsDiscreteValuationRing (Localization.AtPrime p) ∧
      ∃ _ : IsDiscreteValuationRing (primeLocalSubalgebra K p),
        ∀ x : K, x ≠ 0 → WithZero.exp (-heightOneOrd_vw p hp x) =
          (IsDiscreteValuationRing.maximalIdeal (primeLocalSubalgebra K p)).valuation K x) ∧
    (∀ x : K, x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → x ∈ primeLocalSubalgebra K p) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module A M] [Module.Projective A M],
      Function.Injective (TensorProduct.mk A K M 1) ∧
      ∀ v : K ⊗[A] M, v ∈ LinearMap.range (TensorProduct.mk A K M 1) ↔
        ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
          v ∈ LinearMap.range ((primeLocalSubalgebra K p).val.toLinearMap.rTensor M)) ∧
    (∀ x : K, x ≠ 0 → {p : PrimeSpectrum A |
      ∃ hp : p.asIdeal.height = 1, heightOneOrd_vw p.asIdeal hp x ≠ 0}.Finite) ∧
    (∀ x y : K, x ≠ 0 → y ≠ 0 →
      (∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
        heightOneOrd_vw p hp x = heightOneOrd_vw p hp y) → ∃ u : Aˣ, u • y = x) ∧
    (∀ a : A, a ≠ 0 → ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {a}), p.height = 1) := by
  refine ⟨fun p _ hp => ⟨isDiscreteValuationRing_of_height_eq_one p hp _,
      isDiscreteValuationRing_of_height_eq_one p hp _, fun x hx => ?_⟩,
    mem_range_algebraMap_iff_forall_height_eq_one,
    fun M _ _ _ => ⟨injective_of_isLocalizedModule_nonZeroDivisors _,
      mem_range_tensor_iff_forall_height_eq_one⟩,
    fun _ => finite_heightOneOrd_vw_ne_zero,
    fun _ _ hx hy => (exists_unit_smul_eq_iff_heightOneOrd_vw_eq hx hy).mpr,
    fun _ ha _ => height_eq_one_of_mem_associatedPrimes ha⟩
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  rw [WithZero.exp_neg, ← heightOneOrdHom_eq_exp p hp hx,
    heightOneOrdHom_eq_valuation_inv p hp (primeLocalSubalgebra K p), inv_inv]

/- English proof (translation)
Establish `: (Ideal.span {(2 : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible`. Conclude with `⟨Ideal.span {2}, inferInstance, IsPrincipalIdealRing.height_eq_one_of_isMaximal _ Int.not_isField, (heightOneOrd_vw_algebraMap_pos_iff _ _ two_ne_zero).mpr (Ideal.mem_span_singleton_self 2)⟩`.
-/
example : ∃ (p : Ideal ℤ) (_ : p.IsPrime) (hp : p.height = 1),
    0 < heightOneOrd_vw p hp (algebraMap ℤ ℚ 2) := by
  have : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  exact ⟨Ideal.span {2}, inferInstance,
    IsPrincipalIdealRing.height_eq_one_of_isMaximal _ Int.not_isField,
    (heightOneOrd_vw_algebraMap_pos_iff _ _ two_ne_zero).mpr (Ideal.mem_span_singleton_self 2)⟩

end GlobalTheory
