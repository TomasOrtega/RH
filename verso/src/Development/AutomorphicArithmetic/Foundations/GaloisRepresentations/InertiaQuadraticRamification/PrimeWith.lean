import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroup

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion
open scoped Pointwise

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
private theorem pw_normV (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Simplify using `[zero_pow hM0.ne'] at hb`. Use `set u := a / b with hudef`.

Establish `hu : u ^ M = 1` using `by rw [hudef, div_pow, ha, hb, div_one]`. Establish `hu1 : u ≠ 1` using `fun h => hne ((div_eq_one_iff_eq hb0).1 h)`. Establish `hvb : A.valuation b = 1`. Establish `h1 : A.valuation b ^ M = 1` using `by rw [← map_pow, hb, map_one]`. Conclude with `(pow_eq_one_iff.1 h1).resolve_right hM0.ne'`.

Establish `hsub : A.valuation (u - 1) < 1`. Establish `he : u - 1 = (a - b) / b`. Rewrite using `[hudef]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[he, map_div₀, hvb, div_one]`.

Conclude with `hab`. Establish `hvu : A.valuation u = 1`. Use `Valuation.map_eq_of_sub_lt A.valuation (x := 1) (y := u) (by rwa [map_one])` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Establish `hsum : ∑ i ∈ Finset.range M, u ^ i = 0`.

Establish `h` using `geom_sum_mul u M`. Rewrite `h` using `[hu, sub_self]`. Conclude with `(mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu1)`. Establish `hMeq : (M : Ω) = ∑ i ∈ Finset.range M, (1 - u ^ i)`. Rewrite using `[Finset.sum_sub_distrib, hsum, sub_zero]`.

Simplify using the standard rewrite rules. Apply `hMv` to reduce the goal to its premises. Rewrite using `[hMeq]`. Use `Valuation.map_sum_lt _ one_ne_zero ?_` and prove the remaining obligations. Introduce `i _`.

Establish `he : 1 - u ^ i = -((∑ j ∈ Finset.range i, u ^ j) * (u - 1))`. Rewrite using `[geom_sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, Valuation.map_neg, map_mul]`. Establish `hle : A.valuation (∑ j ∈ Finset.range i, u ^ j) ≤ 1` using `Valuation.map_sum_le _ (fun j _ => by rw [map_pow, hvu, one_pow])`.

Rewrite using `[mul_comm]`. Conclude with `mul_lt_one_of_lt_of_le hsub hle`.
-/
private theorem eq_of_pow_eq_one_of_valuation_sub_lt_one' {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (M : ℕ) (hM0 : 0 < M)
    (hMv : ¬ A.valuation (M : Ω) < 1) (a b : Ω) (ha : a ^ M = 1) (hb : b ^ M = 1)
    (hab : A.valuation (a - b) < 1) : a = b := by
  by_contra hne
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp [zero_pow hM0.ne'] at hb
  set u := a / b with hudef
  have hu : u ^ M = 1 := by rw [hudef, div_pow, ha, hb, div_one]
  have hu1 : u ≠ 1 := fun h => hne ((div_eq_one_iff_eq hb0).1 h)
  have hvb : A.valuation b = 1 := by
    have h1 : A.valuation b ^ M = 1 := by rw [← map_pow, hb, map_one]
    exact (pow_eq_one_iff.1 h1).resolve_right hM0.ne'
  have hsub : A.valuation (u - 1) < 1 := by
    have he : u - 1 = (a - b) / b := by
      rw [hudef]
      field_simp
    rw [he, map_div₀, hvb, div_one]
    exact hab
  have hvu : A.valuation u = 1 := by
    have := Valuation.map_eq_of_sub_lt A.valuation (x := 1) (y := u) (by rwa [map_one])
    rwa [map_one] at this
  have hsum : ∑ i ∈ Finset.range M, u ^ i = 0 := by
    have h := geom_sum_mul u M
    rw [hu, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu1)
  have hMeq : (M : Ω) = ∑ i ∈ Finset.range M, (1 - u ^ i) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
    simp
  apply hMv
  rw [hMeq]
  refine Valuation.map_sum_lt _ one_ne_zero ?_
  intro i _
  have he : 1 - u ^ i = -((∑ j ∈ Finset.range i, u ^ j) * (u - 1)) := by
    rw [geom_sum_mul]
    ring
  rw [he, Valuation.map_neg, map_mul]
  have hle : A.valuation (∑ j ∈ Finset.range i, u ^ j) ≤ 1 :=
    Valuation.map_sum_le _ (fun j _ => by rw [map_pow, hvu, one_pow])
  rw [mul_comm]
  exact mul_lt_one_of_lt_of_le hsub hle

/- English proof (translation)
Use `A.valuation_le_one (z : A)` as an intermediate fact. Simplify using `using this`.
-/
private theorem valuation_intCast_le_one' {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (z : ℤ) :
    A.valuation (z : Ω) ≤ 1 := by
  have := A.valuation_le_one (z : A)
  simpa using this

/- English proof (translation)
Introduce `hm1`. Establish `hcop : Nat.gcd p m = 1` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hm`. Establish `h` using `Nat.gcd_eq_gcd_ab p m`. Rewrite `h` using `[hcop, Nat.cast_one]`. Establish `h' : (1 : Ω) = (p : Ω) * ((Nat.gcdA p m : ℤ) : Ω) + (m : Ω) * ((Nat.gcdB p m : ℤ) : Ω)`.

Use `congrArg (fun z : ℤ => (z : Ω)) h` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `: A.valuation (1 : Ω) < 1`. Rewrite using `[h']`.

Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_lt_of_le hpA (valuation_intCast_le_one' A _)`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_lt_of_le hm1 (valuation_intCast_le_one' A _)`.

Simplify using `at this`.
-/
private theorem not_valuation_natCast_lt_one_of_not_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p m : ℕ) (hp : p.Prime)
    (hpA : A.valuation (p : Ω) < 1) (hm : ¬ p ∣ m) : ¬ A.valuation (m : Ω) < 1 := by
  intro hm1
  have hcop : Nat.gcd p m = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have h := Nat.gcd_eq_gcd_ab p m
  rw [hcop, Nat.cast_one] at h
  have h' : (1 : Ω) = (p : Ω) * ((Nat.gcdA p m : ℤ) : Ω) + (m : Ω) * ((Nat.gcdB p m : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) h
    push_cast at this
    exact this
  have : A.valuation (1 : Ω) < 1 := by
    rw [h']
    apply Valuation.map_add_lt
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hpA (valuation_intCast_le_one' A _)
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hm1 (valuation_intCast_le_one' A _)
  simp at this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hn`. Assume the negation of the conclusion as `hnd`. Establish `hnd' : ¬ p ∣ n.natAbs`. Introduce `h`.

Conclude with `hnd (Int.natCast_dvd.2 h)`. Apply `not_valuation_natCast_lt_one_of_not_dvd A p n.natAbs hp hpA hnd'` to reduce the goal to its premises. Break down `Int.natAbs_eq n with h | h` into its components or cases. Rewrite `hn` using `[h]`. Simplify using `using hn`.

Rewrite `hn` using `[h]`. Simplify `hn` using `[Valuation.map_neg]`. Introduce and unpack `⟨c, rfl⟩`. Use `push_cast`. Rewrite using `[map_mul]`.

Conclude with `mul_lt_one_of_lt_of_le hpA (valuation_intCast_le_one' A _)`.
-/
private theorem valuation_intCast_lt_one_iff_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p : ℕ) (hp : p.Prime)
    (hpA : A.valuation (p : Ω) < 1) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra hnd
    have hnd' : ¬ p ∣ n.natAbs := by
      intro h
      exact hnd (Int.natCast_dvd.2 h)
    apply not_valuation_natCast_lt_one_of_not_dvd A p n.natAbs hp hpA hnd'
    rcases Int.natAbs_eq n with h | h
    · rw [h] at hn
      simpa using hn
    · rw [h] at hn
      simpa [Valuation.map_neg] using hn
  · rintro ⟨c, rfl⟩
    push_cast
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hpA (valuation_intCast_le_one' A _)

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n : ℤ, Rat.ringOfIntegersEquiv x = n` from `⟨_, rfl⟩`. Establish `h1 : x = (n : 𝓞 ℚ)`. Rewrite using `[← hn, ← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]`. Rewrite using `[hn]`. Substitute `h1` using the available equality.

Simplify using the standard rewrite rules.
-/
private theorem algebraMap_ratInt_eq_intCast_ringOfIntegersEquiv {Ω : Type} [Field Ω] [CharZero Ω] (x : 𝓞 ℚ) :
    algebraMap ℚ Ω (x : ℚ) = ((Rat.ringOfIntegersEquiv x : ℤ) : Ω) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Rat.ringOfIntegersEquiv x = n := ⟨_, rfl⟩
  have h1 : x = (n : 𝓞 ℚ) := by
    rw [← hn, ← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]
  rw [hn]
  subst h1
  simp

/- English proof (translation)
Introduce `hDec Y Ω _ _ _ _ _ δ q hq hδ g hg hgg M ζ hM hζ B`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ Y Ω`. Use `haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed Y, inferInstance⟩`. Use `haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`.

Take `⟨α, hα⟩` from `Field.exists_primitive_element ℚ Y`. Use `set X : Set Ω := insert δ (insert ζ (Set.range (fun j : Y →+* Ω => j α))) with hXdef`. Establish `hXfin : X.Finite` using `((Set.finite_range _).insert _).insert _`. Use `haveI : Finite X := hXfin.to_subtype`. Use `set K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ X with hKdef`.

Use `haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Use `set L : IntermediateField ℚ Ω := IntermediateField.normalClosure ℚ K Ω with hLdef`. Establish `hKL : K ≤ L` using `K.le_normalClosure`. Use `haveI : FiniteDimensional ℚ L := inferInstance`. Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`.

Use `haveI : IsGalois ℚ L := IsGalois.normalClosure ℚ K Ω`. Establish `hXL : ∀ x ∈ X, x ∈ L` using `fun x hx => hKL (IntermediateField.subset_adjoin ℚ X hx)`. Use `set gA : Ω ≃ₐ[ℚ] Ω := g.toRatAlgEquiv with hgA`. Establish `hgAapp : ∀ z, gA z = g z` using `fun z => rfl`. Use `set S : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | normV v ≤ B + M} with hSdef`.

Establish `hS : S.Finite`. Establish `hfin : (⋃ n ∈ Finset.range (B + M + 1), {I : Ideal (𝓞 ℚ) | Ideal.absNorm I = n}).Finite` using `Set.Finite.biUnion (Finset.finite_toSet _) (fun n _ => Ideal.finite_setOf_absNorm_eq n)`. Use `(hfin.preimage (f := fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal) ?_).subset ?_` and prove the remaining obligations. Introduce `a _ b _ hab`. Conclude with `HeightOneSpectrum.ext hab`.

Introduce `w hw`. Simplify using `only [hSdef, Set.mem_setOf_eq, pw_normV] at hw`. Simplify using `only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_coe, exists_prop]`. Conclude with `⟨_, by omega, rfl⟩`. Take `⟨v, hvS, -, B0, hB0, hIne, φ, hφ, hφg⟩` from `GlobalTheory.Published.chebotarevDegreeOne' ℚ Ω L (AlgEquiv.restrictNormalHom L gA) S hS`.

Use `set p := normV v with hpdef`. Establish `hp : p.Prime` using `by set e := Rat.ringOfIntegersEquiv with hedef set J : Ideal ℤ := Ideal.map e v.asIdeal with hJdef haveI : J.IsPrime := Ideal.map_isPrime_of_equiv e`. Establish `hJ0 : J ≠ ⊥` using `fun hJ => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective e.injective).1 hJ)`. Establish `hJp : Prime J` using `Ideal.prime_of_isPrime hJ0 inferInstance`. Establish `hcard : Ideal.absNorm v.asIdeal = Ideal.absNorm J`.

Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `Nat.card_congr (Ideal.quotientEquiv v.asIdeal J e rfl).toEquiv`. Rewrite using `[hpdef, pw_normV, hcard]`. Conclude with `(Int.prime_absNorm J).2 hJp`. Establish `hpB : B + M < p`.

Simplify using `only [hSdef, Set.mem_setOf_eq, not_le] at hvS`. Conclude with `hvS`. Establish `hφL : ∀ x ∈ L, φ x = g x`. Introduce `x hx`. Establish `h1` using `congrArg (fun τ => ((τ ⟨x, hx⟩ : L) : Ω)) hφg`.

Establish `h2 : φ x = gA x` using `by simpa only [AlgEquiv.restrictNormalHom_apply] using h1`. Conclude with `h2`. Establish `hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal`. Rewrite using `[hpdef, pw_normV]`. Conclude with `Ideal.absNorm_mem v.asIdeal`.

Establish `hB0p : B0.valuation (p : Ω) < 1`. Use `(hB0 ((p : ℕ) : 𝓞 ℚ)).2 hpv` as an intermediate fact. Simplify using `using this`. Establish `hcrit : ∀ (A' : ValuationSubring Ω), A'.valuation (p : Ω) < 1 → ∀ x : 𝓞 ℚ, (A'.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ (p : ℤ) ∣ Rat.ringOfIntegersEquiv x)`. Introduce `A' hA' x`.

Rewrite using `[algebraMap_ratInt_eq_intCast_ringOfIntegersEquiv]`. Conclude with `valuation_intCast_lt_one_iff_dvd A' p hp hA' _`. Establish `hM0 : ¬ B0.valuation (M : Ω) < 1` using `not_valuation_natCast_lt_one_of_not_dvd B0 p M hp hB0p (fun hd => by`. Use `Nat.le_of_dvd hM hd` as an intermediate fact. Use the proof step `omega)`.

Use `⟨p, hp, by omega, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφL ζ (hXL ζ (by simp [hXdef]))]`. Use `eq_of_pow_eq_one_of_valuation_sub_lt_one' B0 M hM hM0 _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_pow, hζ.pow_eq_one, map_one]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`.

Establish `hζ1 : B0.valuation ζ ≤ 1`. Establish `h1 : B0.valuation ζ ^ M = 1` using `by rw [← map_pow, hζ.pow_eq_one, map_one]`. Conclude with `le_of_eq ((pow_eq_one_iff.1 h1).resolve_right hM.ne')`. Conclude with `hφ.2 ζ hζ1`. Introduce `A hA h hhA hhδ y`.

Establish `hAv : IsPlaceOver A v` using `fun x => (hcrit A hA x).trans ((hcrit B0 hB0p x).symm.trans (hB0 x))`. Take `⟨σ, hσ⟩` from `ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hB0 hAv`. Use `set hA' : Ω ≃ₐ[ℚ] Ω := h.toRatAlgEquiv with hhA'`. Establish `hfixA : hA' • A = A`. Use extensionality with `z`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `h3` using `hhA (hA'⁻¹ • z)`. Establish `hz : h (hA'⁻¹ • z) = z` using `by show hA' (hA'.symm z) = z`. Conclude with `AlgEquiv.apply_symm_apply _ _`. Rewrite `h3` using `[hz]`.

Conclude with `h3.symm`. Use `set h' : G ℚ Ω := σ⁻¹ * hA' * σ with hh'`. Establish `hh'mem : h' ∈ Dec B0`. Use `MulAction.mem_stabilizer_iff.2 ?_` and prove the remaining obligations. Rewrite using `[hh', mul_smul, mul_smul, hσ, hfixA, ← hσ, inv_smul_smul]`.

Take `⟨k, hk⟩` from `hDec ℚ Ω B0 v hB0 φ hφ X hXfin (fun τ hτ x hx => ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (hIne hτ)) x (hXL x hx)) h' hh'mem`. Establish `hpowL : ∀ x ∈ L, (φ ^ k) x = (gA ^ k) x`. Introduce `x hx`. Establish `h1` using `congrArg (fun τ => ((τ ^ k) ⟨x, hx⟩ : Ω)) hφg`. Simplify using `only [← map_zpow, AlgEquiv.restrictNormalHom_apply] at h1`.

Conclude with `h1`. Establish `hstab : ∀ z : Ω, (gA ^ 2) z = z → ∀ m : ℤ, ((gA ^ 2) ^ m) z = z`. Introduce `z hz m`. Establish `hmem2 : gA ^ 2 ∈ MulAction.stabilizer (Ω ≃ₐ[ℚ] Ω) z` using `hz`. Conclude with `Subgroup.zpow_mem _ hmem2 m`.

Establish `hg2δ : (gA ^ 2) δ = δ`. Rewrite using `[pow_two, AlgEquiv.mul_apply, hgAapp, hgAapp, hg, map_neg, hg, neg_neg]`. Establish `hσδ : σ δ = δ ∨ σ δ = -δ`. Establish `h2 : (σ δ) ^ 2 = δ ^ 2` using `by rw [← map_pow, hδ, map_natCast]`. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.1 h2`.

Establish `hh'δ : h' δ = δ`. Establish `h2 : hA' (σ δ) = σ δ`. Apply the tactic sequence `rcases hσδ with h4 | h4 <;> rw [h4]`. Conclude with `hhδ`. Use `show h (-δ) = -δ`.

Rewrite using `[map_neg, hhδ]`. Use `show σ.symm (hA' (σ δ)) = δ`. Rewrite using `[h2]`. Conclude with `σ.symm_apply_apply δ`. Establish `hδX : δ ∈ X` using `by simp [hXdef]`.

Establish `hkδ : (gA ^ k) δ = δ` using `by rw [← hpowL δ (hXL δ hδX), ← hk δ hδX, hh'δ]`. Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`. Establish `: (q : Ω) = 0` using `by rw [← hδ]; ring`. Conclude with `(Nat.pos_iff_ne_zero.1 hq) (by exact_mod_cast this)` after adjusting the coercions.

Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : Even k := by`. Break down `Int.even_or_odd k with he | ⟨r, hr⟩` into its components or cases. Conclude with `he`. It suffices to derive a contradiction. Establish `e1 : gA ^ k = (gA ^ 2) ^ r * gA`.

Rewrite using `[hr, zpow_add_one, zpow_mul]`. Use `norm_cast`. Establish `h5 : (gA ^ k) δ = -δ`. Rewrite using `[e1, AlgEquiv.mul_apply, hgAapp, hg, map_neg, hstab δ hg2δ r]`. Rewrite `hkδ` using `[h5]`.

Conclude with `hδ0 (by linear_combination (-1/2 : Ω) * hkδ)`. Establish `hkpow : gA ^ k = (gA ^ 2) ^ r`. Rewrite using `[hr, ← two_mul, zpow_mul]`. Use `norm_cast`. Use `set j' : Y →+* Ω := (σ⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.toRingHom.comp (algebraMap Y Ω) with hj'`.

Establish `hj'X : j' α ∈ X` using `Or.inr (Or.inr ⟨j', rfl⟩)`. Establish `hg2j : (gA ^ 2) (j' α) = j' α`. Rewrite using `[pow_two, AlgEquiv.mul_apply, hgAapp, hgAapp]`. Conclude with `hgg j' α`. Establish `hh'j : h' (j' α) = j' α`.

Rewrite using `[hk _ hj'X, hpowL _ (hXL _ hj'X), hkpow]`. Conclude with `hstab _ hg2j r`. Establish `hα' : h (algebraMap Y Ω α) = algebraMap Y Ω α`. Establish `e2 : σ (j' α) = algebraMap Y Ω α` using `by show σ (σ.symm _) = _`. Conclude with `σ.apply_symm_apply _`.

Establish `e3 : σ (h' (j' α)) = hA' (σ (j' α))` using `by show σ (σ.symm (hA' (σ (j' α)))) = _`. Conclude with `σ.apply_symm_apply _`. Establish `h6 : σ (h' (j' α)) = σ (j' α)` using `by rw [hh'j]`. Rewrite `h6` using `[e3, e2]`. Conclude with `h6`.

Establish `hext : (hA'.toAlgHom.comp (IsScalarTower.toAlgHom ℚ Y Ω)) = IsScalarTower.toAlgHom ℚ Y Ω`. Apply `AlgHom.ext_of_adjoin_eq_top (s := {α})` to reduce the goal to its premises. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα]`. Conclude with `IntermediateField.top_toSubalgebra`. Introduce `z hz`.

Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality. Conclude with `hα'`. Establish `h7` using `congrArg (fun f => f y) hext`. Establish `h8 : hA' (algebraMap Y Ω y) = algebraMap Y Ω y` using `by simpa using h7`.

Conclude with `h8`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.primeWith :
    DecGen → PrimeWith := by
  intro hDec Y Ω _ _ _ _ _ δ q hq hδ g hg hgg M ζ hM hζ B
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ Y Ω
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed Y, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ Y
  set X : Set Ω := insert δ (insert ζ (Set.range (fun j : Y →+* Ω => j α))) with hXdef
  have hXfin : X.Finite := ((Set.finite_range _).insert _).insert _
  haveI : Finite X := hXfin.to_subtype
  set K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ X with hKdef
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  set L : IntermediateField ℚ Ω := IntermediateField.normalClosure ℚ K Ω with hLdef
  have hKL : K ≤ L := K.le_normalClosure
  haveI : FiniteDimensional ℚ L := inferInstance
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois ℚ L := IsGalois.normalClosure ℚ K Ω
  have hXL : ∀ x ∈ X, x ∈ L := fun x hx => hKL (IntermediateField.subset_adjoin ℚ X hx)
  set gA : Ω ≃ₐ[ℚ] Ω := g.toRatAlgEquiv with hgA
  have hgAapp : ∀ z, gA z = g z := fun z => rfl
  set S : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | normV v ≤ B + M} with hSdef
  have hS : S.Finite := by
    have hfin : (⋃ n ∈ Finset.range (B + M + 1),
        {I : Ideal (𝓞 ℚ) | Ideal.absNorm I = n}).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) (fun n _ => Ideal.finite_setOf_absNorm_eq n)
    refine (hfin.preimage (f := fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal) ?_).subset ?_
    · intro a _ b _ hab
      exact HeightOneSpectrum.ext hab
    · intro w hw
      simp only [hSdef, Set.mem_setOf_eq, pw_normV] at hw
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range,
        Finset.mem_coe, exists_prop]
      exact ⟨_, by omega, rfl⟩
  obtain ⟨v, hvS, -, B0, hB0, hIne, φ, hφ, hφg⟩ :=
    GlobalTheory.Published.chebotarevDegreeOne' ℚ Ω L (AlgEquiv.restrictNormalHom L gA) S hS
  set p := normV v with hpdef
  have hp : p.Prime := by
    set e := Rat.ringOfIntegersEquiv with hedef
    set J : Ideal ℤ := Ideal.map e v.asIdeal with hJdef
    haveI : J.IsPrime := Ideal.map_isPrime_of_equiv e
    have hJ0 : J ≠ ⊥ := fun hJ => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective e.injective).1 hJ)
    have hJp : Prime J := Ideal.prime_of_isPrime hJ0 inferInstance
    have hcard : Ideal.absNorm v.asIdeal = Ideal.absNorm J := by
      rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Submodule.cardQuot_apply]
      exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal J e rfl).toEquiv
    rw [hpdef, pw_normV, hcard]
    exact (Int.prime_absNorm J).2 hJp
  have hpB : B + M < p := by
    simp only [hSdef, Set.mem_setOf_eq, not_le] at hvS
    exact hvS
  have hφL : ∀ x ∈ L, φ x = g x := by
    intro x hx
    have h1 := congrArg (fun τ => ((τ ⟨x, hx⟩ : L) : Ω)) hφg
    have h2 : φ x = gA x := by simpa only [AlgEquiv.restrictNormalHom_apply] using h1
    exact h2
  have hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [hpdef, pw_normV]
    exact Ideal.absNorm_mem v.asIdeal
  have hB0p : B0.valuation (p : Ω) < 1 := by
    have := (hB0 ((p : ℕ) : 𝓞 ℚ)).2 hpv
    simpa using this
  have hcrit : ∀ (A' : ValuationSubring Ω), A'.valuation (p : Ω) < 1 → ∀ x : 𝓞 ℚ,
      (A'.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ (p : ℤ) ∣ Rat.ringOfIntegersEquiv x) := by
    intro A' hA' x
    rw [algebraMap_ratInt_eq_intCast_ringOfIntegersEquiv]
    exact valuation_intCast_lt_one_iff_dvd A' p hp hA' _
  have hM0 : ¬ B0.valuation (M : Ω) < 1 := not_valuation_natCast_lt_one_of_not_dvd B0 p M hp hB0p (fun hd => by
    have := Nat.le_of_dvd hM hd
    omega)
  refine ⟨p, hp, by omega, ?_, ?_⟩
  · rw [← hφL ζ (hXL ζ (by simp [hXdef]))]
    refine eq_of_pow_eq_one_of_valuation_sub_lt_one' B0 M hM hM0 _ _ ?_ ?_ ?_
    · rw [← map_pow, hζ.pow_eq_one, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · have hζ1 : B0.valuation ζ ≤ 1 := by
        have h1 : B0.valuation ζ ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
        exact le_of_eq ((pow_eq_one_iff.1 h1).resolve_right hM.ne')
      exact hφ.2 ζ hζ1
  · intro A hA h hhA hhδ y
    have hAv : IsPlaceOver A v := fun x =>
      (hcrit A hA x).trans ((hcrit B0 hB0p x).symm.trans (hB0 x))
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hB0 hAv
    set hA' : Ω ≃ₐ[ℚ] Ω := h.toRatAlgEquiv with hhA'
    have hfixA : hA' • A = A := by
      ext z
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have h3 := hhA (hA'⁻¹ • z)
      have hz : h (hA'⁻¹ • z) = z := by
        show hA' (hA'.symm z) = z
        exact AlgEquiv.apply_symm_apply _ _
      rw [hz] at h3
      exact h3.symm
    set h' : G ℚ Ω := σ⁻¹ * hA' * σ with hh'
    have hh'mem : h' ∈ Dec B0 := by
      refine MulAction.mem_stabilizer_iff.2 ?_
      rw [hh', mul_smul, mul_smul, hσ, hfixA, ← hσ, inv_smul_smul]
    obtain ⟨k, hk⟩ := hDec ℚ Ω B0 v hB0 φ hφ X hXfin
      (fun τ hτ x hx => ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (hIne hτ)) x (hXL x hx))
      h' hh'mem
    have hpowL : ∀ x ∈ L, (φ ^ k) x = (gA ^ k) x := by
      intro x hx
      have h1 := congrArg (fun τ => ((τ ^ k) ⟨x, hx⟩ : Ω)) hφg
      simp only [← map_zpow, AlgEquiv.restrictNormalHom_apply] at h1
      exact h1
    have hstab : ∀ z : Ω, (gA ^ 2) z = z → ∀ m : ℤ, ((gA ^ 2) ^ m) z = z := by
      intro z hz m
      have hmem2 : gA ^ 2 ∈ MulAction.stabilizer (Ω ≃ₐ[ℚ] Ω) z := hz
      exact Subgroup.zpow_mem _ hmem2 m
    have hg2δ : (gA ^ 2) δ = δ := by
      rw [pow_two, AlgEquiv.mul_apply, hgAapp, hgAapp, hg, map_neg, hg, neg_neg]
    have hσδ : σ δ = δ ∨ σ δ = -δ := by
      have h2 : (σ δ) ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, map_natCast]
      exact sq_eq_sq_iff_eq_or_eq_neg.1 h2
    have hh'δ : h' δ = δ := by
      have h2 : hA' (σ δ) = σ δ := by
        rcases hσδ with h4 | h4 <;> rw [h4]
        · exact hhδ
        · show h (-δ) = -δ
          rw [map_neg, hhδ]
      show σ.symm (hA' (σ δ)) = δ
      rw [h2]
      exact σ.symm_apply_apply δ
    have hδX : δ ∈ X := by simp [hXdef]
    have hkδ : (gA ^ k) δ = δ := by rw [← hpowL δ (hXL δ hδX), ← hk δ hδX, hh'δ]
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      have : (q : Ω) = 0 := by rw [← hδ]; ring
      exact_mod_cast (Nat.pos_iff_ne_zero.1 hq) (by exact_mod_cast this)
    obtain ⟨r, hr⟩ : Even k := by
      rcases Int.even_or_odd k with he | ⟨r, hr⟩
      · exact he
      · exfalso
        have e1 : gA ^ k = (gA ^ 2) ^ r * gA := by
          rw [hr, zpow_add_one, zpow_mul]
          norm_cast
        have h5 : (gA ^ k) δ = -δ := by
          rw [e1, AlgEquiv.mul_apply, hgAapp, hg, map_neg, hstab δ hg2δ r]
        rw [h5] at hkδ
        exact hδ0 (by linear_combination (-1/2 : Ω) * hkδ)
    have hkpow : gA ^ k = (gA ^ 2) ^ r := by
      rw [hr, ← two_mul, zpow_mul]
      norm_cast
    set j' : Y →+* Ω := (σ⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.toRingHom.comp (algebraMap Y Ω) with hj'
    have hj'X : j' α ∈ X := Or.inr (Or.inr ⟨j', rfl⟩)
    have hg2j : (gA ^ 2) (j' α) = j' α := by
      rw [pow_two, AlgEquiv.mul_apply, hgAapp, hgAapp]
      exact hgg j' α
    have hh'j : h' (j' α) = j' α := by
      rw [hk _ hj'X, hpowL _ (hXL _ hj'X), hkpow]
      exact hstab _ hg2j r
    have hα' : h (algebraMap Y Ω α) = algebraMap Y Ω α := by
      have e2 : σ (j' α) = algebraMap Y Ω α := by
        show σ (σ.symm _) = _
        exact σ.apply_symm_apply _
      have e3 : σ (h' (j' α)) = hA' (σ (j' α)) := by
        show σ (σ.symm (hA' (σ (j' α)))) = _
        exact σ.apply_symm_apply _
      have h6 : σ (h' (j' α)) = σ (j' α) := by rw [hh'j]
      rw [e3, e2] at h6
      exact h6
    have hext : (hA'.toAlgHom.comp (IsScalarTower.toAlgHom ℚ Y Ω)) = IsScalarTower.toAlgHom ℚ Y Ω := by
      apply AlgHom.ext_of_adjoin_eq_top (s := {α})
      · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          (Algebra.IsAlgebraic.isAlgebraic α), hα]
        exact IntermediateField.top_toSubalgebra
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hα'
    have h7 := congrArg (fun f => f y) hext
    have h8 : hA' (algebraMap Y Ω y) = algebraMap Y Ω y := by simpa using h7
    exact h8
