import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Take `⟨z, hz⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω) (hy.tower_top (A := A))`. Conclude with `hz ▸ z.2`.
-/
private theorem mem_of_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω) (hy.tower_top (A := A))
  exact hz ▸ z.2

open Polynomial in
/- English proof (translation)
Assume the negation of the conclusion as `hne`. Apply `hd` to reduce the goal to its premises. Take `⟨c, hc⟩` from `(f.map (algebraMap ℤ A)).binomExpansion ⟨a, ha⟩ (⟨b, hb⟩ - ⟨a, ha⟩)`. Establish `e : ∀ (g : ℤ[X]) (x : A), ((eval x (g.map (algebraMap ℤ A)) : A) : Ω) = aeval (x : Ω) g` using `fun g x => by`. Rewrite using `[eval_map_algebraMap]`.

Conclude with `(aeval_algHom_apply (A.subtype.toIntAlgHom) x g).symm`. Rewrite `hc` using `[add_sub_cancel, derivative_map]`. Establish `h2` using `congrArg (fun x : A => (x : Ω)) hc`. Move the coercions through the operations in `at h2`. Simplify using `only [e, fa, fb] at h2`.

Establish `h3 : aeval a (derivative f) = -(c : Ω) * (b - a)`. Apply `mul_right_cancel₀ (sub_ne_zero.2 hne)` to reduce the goal to its premises. Take the linear combination `-h2`. Rewrite using `[h3, map_mul, Valuation.map_neg]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (A.valuation_le_one c)) hab`.
-/
private theorem key {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : ℤ[X]) {a b : Ω} (ha : a ∈ A) (hb : b ∈ A)
    (fa : aeval a f = 0) (fb : aeval b f = 0) (hab : A.valuation (b - a) < 1)
    (hd : ¬ A.valuation (aeval a (derivative f)) < 1) : b = a := by
  by_contra hne
  apply hd
  obtain ⟨c, hc⟩ := (f.map (algebraMap ℤ A)).binomExpansion ⟨a, ha⟩ (⟨b, hb⟩ - ⟨a, ha⟩)
  have e : ∀ (g : ℤ[X]) (x : A), ((eval x (g.map (algebraMap ℤ A)) : A) : Ω) = aeval (x : Ω) g := fun g x => by
    rw [eval_map_algebraMap]
    exact (aeval_algHom_apply (A.subtype.toIntAlgHom) x g).symm
  rw [add_sub_cancel, derivative_map] at hc
  have h2 := congrArg (fun x : A => (x : Ω)) hc
  push_cast at h2
  simp only [e, fa, fb] at h2
  have h3 : aeval a (derivative f) = -(c : Ω) * (b - a) := by
    apply mul_right_cancel₀ (sub_ne_zero.2 hne)
    linear_combination -h2
  rw [h3, map_mul, Valuation.map_neg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (A.valuation_le_one c)) hab

open Polynomial in
/- English proof (translation)
Establish `hi : IsIntegral ℤ α` using `Algebra.IsIntegral.isIntegral α`. Establish `hne : aeval α (derivative (minpoly ℤ α)) ≠ 0`. Introduce `h`. Establish `h1` using `minpoly.isIntegrallyClosed_dvd hi h`. Establish `h2` using `minpoly.natDegree_pos hi`.

Establish `h3 : derivative (minpoly ℤ α) ≠ 0` using `fun h0 => by`. Use `natDegree_eq_zero_of_derivative_eq_zero h0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h4` using `natDegree_le_of_dvd h1 h3`. Establish `h5` using `natDegree_derivative_lt (p := minpoly ℤ α) (by omega)`.

Use linear arithmetic over natural numbers and integers. Use `set δ := aeval α (derivative (minpoly ℤ α)) with hδ`. Establish `hm : (Algebra.norm ℤ δ : 𝓞 E') ∈ Ideal.span {δ}`. Use `Ideal.absNorm_mem (Ideal.span {δ})` as an intermediate fact. Rewrite `this` using `[Ideal.absNorm_span_singleton]`.

Break down `Int.natAbs_eq (Algebra.norm ℤ δ) with h | h` into its components or cases. Rewrite using `[h]`. Simplify using `using this`. Rewrite using `[h]`. Simplify using `using this`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hm`. Use `⟨Algebra.norm ℤ δ, Algebra.norm_ne_zero_iff.2 hne, fun A hA σ hσ => ?_⟩` and prove the remaining obligations. Set `φ : 𝓞 E' →ₐ[ℤ] Ω` to `((algebraMap E' Ω).comp (algebraMap (𝓞 E') E')).toIntAlgHom`. Establish `hφ : ∀ x, φ x ∈ A` using `fun x => mem_of_int A ((Algebra.IsIntegral.isIntegral x).map φ)`. Set `ψ : Ω →ₐ[ℤ] Ω` to `σ.toRingEquiv.toRingHom.toIntAlgHom`.

Establish `fa : aeval (φ α) (minpoly ℤ α) = 0` using `by rw [aeval_algHom_apply, minpoly.aeval, map_zero]`. Express the relevant statement in the definitionally equal form `ψ (φ α) = φ α`. Use `key A (minpoly ℤ α) (hφ α) (mem_of_int A ((hi.map φ).map ψ)) fa (by rw [aeval_algHom_apply, fa, map_zero]) (hσ.2 _ ((A.valuation_le_one_iff _).2 (hφ α))) fun h => hA ?_` and prove the remaining obligations. Rewrite `h` using `[aeval_algHom_apply, ← hδ]`. Establish `e : ((Algebra.norm ℤ δ : ℤ) : Ω) = φ t * φ δ` using `by rw [← map_mul, ht, map_intCast]`.

Rewrite using `[e, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hφ t))) h`.
-/
private theorem fix_int {k E' Ω : Type} [Field k] [NumberField k] [Field E'] [NumberField E'] [Field Ω] [Algebra k Ω]
    [Algebra E' Ω] (α : 𝓞 E') : ∃ d : ℤ, d ≠ 0 ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (d : Ω) < 1 →
      ∀ σ ∈ Ine (F := k) A, σ (algebraMap E' Ω α) = algebraMap E' Ω α := by
  have hi : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hne : aeval α (derivative (minpoly ℤ α)) ≠ 0 := by
    intro h
    have h1 := minpoly.isIntegrallyClosed_dvd hi h
    have h2 := minpoly.natDegree_pos hi
    have h3 : derivative (minpoly ℤ α) ≠ 0 := fun h0 => by
      have := natDegree_eq_zero_of_derivative_eq_zero h0
      omega
    have h4 := natDegree_le_of_dvd h1 h3
    have h5 := natDegree_derivative_lt (p := minpoly ℤ α) (by omega)
    omega
  set δ := aeval α (derivative (minpoly ℤ α)) with hδ
  have hm : (Algebra.norm ℤ δ : 𝓞 E') ∈ Ideal.span {δ} := by
    have := Ideal.absNorm_mem (Ideal.span {δ})
    rw [Ideal.absNorm_span_singleton] at this
    rcases Int.natAbs_eq (Algebra.norm ℤ δ) with h | h
    · rw [h]; simpa using this
    · rw [h]; simpa using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  refine ⟨Algebra.norm ℤ δ, Algebra.norm_ne_zero_iff.2 hne, fun A hA σ hσ => ?_⟩
  let φ : 𝓞 E' →ₐ[ℤ] Ω := ((algebraMap E' Ω).comp (algebraMap (𝓞 E') E')).toIntAlgHom
  have hφ : ∀ x, φ x ∈ A := fun x => mem_of_int A ((Algebra.IsIntegral.isIntegral x).map φ)
  let ψ : Ω →ₐ[ℤ] Ω := σ.toRingEquiv.toRingHom.toIntAlgHom
  have fa : aeval (φ α) (minpoly ℤ α) = 0 := by rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  change ψ (φ α) = φ α
  refine key A (minpoly ℤ α) (hφ α) (mem_of_int A ((hi.map φ).map ψ)) fa
    (by rw [aeval_algHom_apply, fa, map_zero]) (hσ.2 _ ((A.valuation_le_one_iff _).2 (hφ α))) fun h => hA ?_
  rw [aeval_algHom_apply, ← hδ] at h
  have e : ((Algebra.norm ℤ δ : ℤ) : Ω) = φ t * φ δ := by rw [← map_mul, ht, map_intCast]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hφ t))) h

open Polynomial in
/- English proof (translation)
Establish `hm : ∀ {y : Ω}, y ^ N = 1 → y ∈ A` using `fun {y} hy => mem_of_int A (IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (hy ▸ isIntegral_one))`. Establish `hz' : (σ z) ^ N = 1` using `by rw [← map_pow, hz, map_one]`. Use `key A (X ^ N - 1) (hm hz) (hm hz') (by simp [hz]) (by simp [hz']) (hσ.2 _ ((A.valuation_le_one_iff _).2 (hm hz))) fun h => hA ?_` and prove the remaining obligations. Establish `e : (N : Ω) = z * aeval z (derivative (X ^ N - 1 : ℤ[X]))`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, map_natCast, map_pow, aeval_X]`.

Rewrite using `[mul_left_comm, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hz, mul_one]`. Rewrite using `[e, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hm hz))) h`.
-/
private theorem fix_root {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {N : ℕ} (hN : N ≠ 0)
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (N : Ω) < 1) {σ : G k Ω} (hσ : σ ∈ Ine (F := k) A) {z : Ω}
    (hz : z ^ N = 1) : σ z = z := by
  have hm : ∀ {y : Ω}, y ^ N = 1 → y ∈ A := fun {y} hy =>
    mem_of_int A (IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (hy ▸ isIntegral_one))
  have hz' : (σ z) ^ N = 1 := by rw [← map_pow, hz, map_one]
  refine key A (X ^ N - 1) (hm hz) (hm hz') (by simp [hz]) (by simp [hz'])
    (hσ.2 _ ((A.valuation_le_one_iff _).2 (hm hz))) fun h => hA ?_
  have e : (N : Ω) = z * aeval z (derivative (X ^ N - 1 : ℤ[X])) := by
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, map_natCast, map_pow, aeval_X]
    rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hz, mul_one]
  rw [e, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (hm hz))) h

/- English proof (translation)
Introduce `k E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective`. Use `⟨?_, fun N _ hc A hA σ hσ x => ?_⟩` and prove the remaining obligations. Use `choose d hd0 hd using fun α : 𝓞 E' => fix_int (k := k) (Ω := Ω) α`. Establish `hfin : ∀ i, {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {((d (RingOfIntegers.basis E' i) : ℤ) : 𝓞 E)}}.Finite` using `fun i => Ideal.finite_factors (by simpa using hd0 _)`.

Use `⟨(Set.finite_iUnion hfin).toFinset, fun v hv A hA σ hσ x => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Ideal.dvd_span_singleton] at hv`. Establish `h : (σ.toRingEquiv.toRingHom.comp (algebraMap E' Ω)).toRatAlgHom.toLinearMap = (algebraMap E' Ω).toRatAlgHom.toLinearMap` using `(integralBasis E').ext fun i => by`. Rewrite using `[integralBasis_apply]`. Use `hd _ A (fun h => hv i ((hA _).1 ?_)) σ hσ.2` and prove the remaining obligations.

Simplify using `using h`. Conclude with `LinearMap.congr_fun h x`. Establish `hx` using `hc.adjoin_roots x`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem y hy`.

Take `⟨n, hn, h0, hy⟩` from `hy`. Take `rfl : n = N` from `hn`. Conclude with `fix_root h0 A hA hσ.2 (by rw [← map_pow, hy, map_one])`. Consider the case `algebraMap r => rw [← IsScalarTower.algebraMap_apply]`. Conclude with `hσ.1 r`.

Consider the case `add a b _ _ ha hb => rw [map_add, map_add, ha, hb]`. Consider the case `mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]`.
-/
theorem UpperTheory.V.Base.ramFinite :
    ∀ (k E E' Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
      [Algebra k Ω] [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [Algebra k E] [IsScalarTower k E Ω] [IsScalarTower E E' Ω]
      [IsAlgClosure k Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω],
      (∃ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω) ∧
      ∀ (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} E E'] (A : ValuationSubring Ω), ¬ A.valuation (N : Ω) < 1 →
        galOf k E Ω ⊓ Ine (F := k) A ≤ galOf k E' Ω := by
  intro k E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  refine ⟨?_, fun N _ hc A hA σ hσ x => ?_⟩
  · choose d hd0 hd using fun α : 𝓞 E' => fix_int (k := k) (Ω := Ω) α
    have hfin : ∀ i, {v : HeightOneSpectrum (𝓞 E) |
        v.asIdeal ∣ Ideal.span {((d (RingOfIntegers.basis E' i) : ℤ) : 𝓞 E)}}.Finite := fun i =>
      Ideal.finite_factors (by simpa using hd0 _)
    refine ⟨(Set.finite_iUnion hfin).toFinset, fun v hv A hA σ hσ x => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Ideal.dvd_span_singleton] at hv
    have h : (σ.toRingEquiv.toRingHom.comp (algebraMap E' Ω)).toRatAlgHom.toLinearMap =
        (algebraMap E' Ω).toRatAlgHom.toLinearMap := (integralBasis E').ext fun i => by
      rw [integralBasis_apply]
      refine hd _ A (fun h => hv i ((hA _).1 ?_)) σ hσ.2
      simpa using h
    exact LinearMap.congr_fun h x
  · have hx := hc.adjoin_roots x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, h0, hy⟩ := hy
      obtain rfl : n = N := hn
      exact fix_root h0 A hA hσ.2 (by rw [← map_pow, hy, map_one])
    | algebraMap r => rw [← IsScalarTower.algebraMap_apply]; exact hσ.1 r
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
