import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitTraceUnramifiedExtension

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Introduce `K K' d φ hU B ψ hψ hnt hO s Q hQm hQg hQr y`. Use `set Ψ : K'.O →+* B.A := ψ.comp (algebraMap K'.O K'.E) with hΨdef`. Establish `hΨφ : ∀ a : K.O, Ψ (intMap hU a) = algebraMap K.O B.A a`. Introduce `a`. Simplify using `only [Ψ, RingHom.comp_apply, intMap_spec, hψ]`.

Conclude with `(IsScalarTower.algebraMap_apply K.O K.E B.A a).symm`. Establish `hcomp : (algebraMap K'.O K'.E).comp (intMap hU) = φ.comp (algebraMap K.O K.E)`. Use extensionality with `a`. Simplify using `[intMap_spec]`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : K.O[X], aeval B.g f = ψ (algebraMap K'.O K'.E y) := by`.

Use `hO y` as an intermediate fact. Rewrite `this` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Conclude with `this`. Use `⟨f, y - f.eval₂ (intMap hU) s, ?_, ?_⟩` and prove the remaining obligations. Use `swap`.

Rewrite using `[map_sub, Polynomial.hom_eval₂, hcomp]`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `hz`. Establish `hzu : IsUnit (y - f.eval₂ (intMap hU) s)`. Assume the negation of the conclusion as `h`.

Conclude with `hz ((IsLocalRing.mem_maximalIdeal _).2 h)`. Use `set z := y - f.eval₂ (intMap hU) s with hzdef`. Use `set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hRdef`. Use `haveI := hnt`. Establish `hΨz : Ψ z = aeval B.g f - aeval (Ψ s) f`.

Rewrite using `[hzdef, map_sub, hf, Polynomial.hom_eval₂]`. Establish `: Ψ.comp (intMap hU) = algebraMap K.O B.A` using `by ext a; exact hΨφ a`. Rewrite using `[this]`. Both sides reduce to the same expression. Set `g' : R` to `⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩`.

Set `x' : R` to `⟨Ψ s, hO s⟩`. Take `⟨h, hh⟩` from `Polynomial.sub_dvd_eval_sub g' x' (f.map (algebraMap K.O R))`. Establish `hh' : Ψ z = (B.g - Ψ s) * (h : B.A)`. Rewrite using `[hΨz]`. Use `congrArg Subtype.val hh` as an intermediate fact.

Simplify using `only [Polynomial.eval_map_algebraMap, Subalgebra.coe_sub, Subalgebra.coe_mul, Polynomial.aeval_subalgebra_coe] at this`. Conclude with `this`. Take `⟨zu, hzu'⟩` from `hzu`. Set `zi : R` to `⟨Ψ ((zu⁻¹ : K'.Oˣ) : K'.O), hO _⟩`. Establish `hunit : (g' - x') * (h * zi) = 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, g', x', zi]`. Rewrite using `[← mul_assoc, ← hh', ← hzu', ← map_mul, Units.mul_inv, map_one]`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible K.O`. Establish `hmax : IsLocalRing.maximalIdeal K'.O = Ideal.span {intMap hU ϖ}`.

Rewrite using `[← map_maximalIdeal hU, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span, Set.image_singleton]`. Establish `hdvd : C (intMap hU ϖ) ∣ Q - (X - C s) ^ Q.natDegree`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`. Rewrite using `[← Ideal.mem_span_singleton, ← hmax, ← IsLocalRing.residue_eq_zero_iff, ← Polynomial.coeff_map, Polynomial.map_sub, hQr]`.

Simplify using the standard rewrite rules. Take `⟨R', hR'⟩` from `hdvd`. Establish `hev` using `congrArg (Polynomial.eval₂ Ψ B.g) hR'`. Rewrite `hev` using `[Polynomial.eval₂_sub, hQg, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, hΨφ]`. Establish `hRmem : ∀ P : K'.O[X], P.eval₂ Ψ B.g ∈ R`.

Introduce `P`. Rewrite using `[Polynomial.eval₂_eq_sum_range]`. Conclude with `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hO _) (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O B.g) _)`. Set `r : R` to `⟨R'.eval₂ Ψ B.g, hRmem R'⟩`. Establish `hpow : (g' - x') ^ Q.natDegree = -(algebraMap K.O R ϖ * r)`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subalgebra.coe_pow, Subalgebra.coe_sub, Subalgebra.coe_neg, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, g', x', r]`. Rewrite using `[← hev]`. Expand and normalize the polynomial expressions, which then agree. Use `set u := h * zi`.

Establish `hinv : algebraMap K.O R ϖ * (-(r * u ^ Q.natDegree)) = 1`. Establish `: ((g' - x') * u) ^ Q.natDegree = 1` using `by rw [hunit, one_pow]`. Rewrite `this` using `[mul_pow, hpow]`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.

Use `letI : Algebra K'.O B.A := Ψ.toAlgebra`. Establish `hgint : IsIntegral K'.O B.g` using `⟨Q, hQm, hQg⟩`. Establish `hRint : ∀ w ∈ R, IsIntegral K'.O w`. Introduce `w hw`. Proceed by induction on `hw using Algebra.adjoin_induction with`.

Consider the case `mem x hx => rw [Set.mem_singleton_iff.1 hx]`. Conclude with `hgint`. Consider the case `algebraMap a`. Rewrite using `[← hΨφ a]`. Conclude with `isIntegral_algebraMap (R := K'.O) (x := intMap hU a)`.

Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `mul x y _ _ hx hy => exact hx.mul hy`. Use `set v : R := -(r * u ^ Q.natDegree)`. Establish `hvint : IsIntegral K'.O (v : B.A)` using `hRint _ v.2`. Establish `hv1 : Ψ (intMap hU ϖ) * (v : B.A) = 1`.

Use `congrArg Subtype.val hinv` as an intermediate fact. Simplify `this` using `[hΨφ]`. Establish `hϖ0 : intMap hU ϖ ≠ 0` using `fun h0 => hϖ.ne_zero ((intMap_injective hU) (by rw [h0, map_zero]))`. Establish `hπ0 : algebraMap K'.O K'.E (intMap hU ϖ) ≠ 0`. Introduce `h0; exact hϖ0 (IsFractionRing.injective K'.O K'.E (by rw [h0, map_zero]))`.

Use `set t : K'.E := (algebraMap K'.O K'.E (intMap hU ϖ))⁻¹`. Establish `hψt : ψ t = v`. Establish `h1 : Ψ (intMap hU ϖ) * ψ t = 1`. Rewrite using `[hΨdef, RingHom.comp_apply, ← map_mul, mul_inv_cancel₀ hπ0, map_one]`. Combine the equalities or inequalities in the displayed calculation.

Set `ψA : K'.E →ₐ[K'.O] B.A` to `{ toRingHom := ψ, commutes' := fun _ => rfl }`. Establish `htint : IsIntegral K'.O t`. Rewrite using `[← isIntegral_algHom_iff ψA ψ.injective]`. Use `show IsIntegral K'.O (ψ t)`. Rewrite using `[hψt]`.

Conclude with `hvint`. Take `⟨b, hb⟩` from `IsIntegrallyClosed.isIntegral_iff.1 htint`. Establish `hb1 : intMap hU ϖ * b = 1`. Apply `IsFractionRing.injective K'.O K'.E` to reduce the goal to its premises. Rewrite using `[map_mul, hb, mul_inv_cancel₀ hπ0, map_one]`.

Establish `hmem : intMap hU ϖ ∈ IsLocalRing.maximalIdeal K'.O`. Rewrite using `[hmax]`. Conclude with `Ideal.subset_span rfl`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hmem ⟨⟨_, b, hb1, by rw [mul_comm]; exact hb1⟩, rfl⟩`.
-/
theorem residue_generates : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A), (∀ e, ψ (φ e) = algebraMap K.E B.A e) → Nontrivial B.A → (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ (s : K'.O) (Q : K'.O[X]), Q.Monic → Q.eval₂ (ψ.comp (algebraMap K'.O K'.E)) B.g = 0 → Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree → ∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z := by
  intro K K' d φ hU B ψ hψ hnt hO s Q hQm hQg hQr y
  set Ψ : K'.O →+* B.A := ψ.comp (algebraMap K'.O K'.E) with hΨdef
  have hΨφ : ∀ a : K.O, Ψ (intMap hU a) = algebraMap K.O B.A a := by
    intro a
    simp only [Ψ, RingHom.comp_apply, intMap_spec, hψ]
    exact (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hcomp : (algebraMap K'.O K'.E).comp (intMap hU) = φ.comp (algebraMap K.O K.E) := by
    ext a; simp [intMap_spec]
  obtain ⟨f, hf⟩ : ∃ f : K.O[X], aeval B.g f = ψ (algebraMap K'.O K'.E y) := by
    have := hO y
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  refine ⟨f, y - f.eval₂ (intMap hU) s, ?_, ?_⟩
  swap
  · rw [map_sub, Polynomial.hom_eval₂, hcomp]; ring

  by_contra hz
  have hzu : IsUnit (y - f.eval₂ (intMap hU) s) := by
    by_contra h; exact hz ((IsLocalRing.mem_maximalIdeal _).2 h)
  set z := y - f.eval₂ (intMap hU) s with hzdef
  set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hRdef
  haveI := hnt

  have hΨz : Ψ z = aeval B.g f - aeval (Ψ s) f := by
    rw [hzdef, map_sub, hf, Polynomial.hom_eval₂]
    have : Ψ.comp (intMap hU) = algebraMap K.O B.A := by ext a; exact hΨφ a
    rw [this]; rfl
  let g' : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  let x' : R := ⟨Ψ s, hO s⟩
  obtain ⟨h, hh⟩ := Polynomial.sub_dvd_eval_sub g' x' (f.map (algebraMap K.O R))
  have hh' : Ψ z = (B.g - Ψ s) * (h : B.A) := by
    rw [hΨz]
    have := congrArg Subtype.val hh
    simp only [Polynomial.eval_map_algebraMap, Subalgebra.coe_sub, Subalgebra.coe_mul,
      Polynomial.aeval_subalgebra_coe] at this
    exact this

  obtain ⟨zu, hzu'⟩ := hzu
  let zi : R := ⟨Ψ ((zu⁻¹ : K'.Oˣ) : K'.O), hO _⟩
  have hunit : (g' - x') * (h * zi) = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, g', x', zi]
    rw [← mul_assoc, ← hh', ← hzu', ← map_mul, Units.mul_inv, map_one]

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hmax : IsLocalRing.maximalIdeal K'.O = Ideal.span {intMap hU ϖ} := by
    rw [← map_maximalIdeal hU, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.map_span, Set.image_singleton]
  have hdvd : C (intMap hU ϖ) ∣ Q - (X - C s) ^ Q.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [← Ideal.mem_span_singleton, ← hmax, ← IsLocalRing.residue_eq_zero_iff, ← Polynomial.coeff_map,
      Polynomial.map_sub, hQr]
    simp
  obtain ⟨R', hR'⟩ := hdvd
  have hev := congrArg (Polynomial.eval₂ Ψ B.g) hR'
  rw [Polynomial.eval₂_sub, hQg, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, hΨφ] at hev
  have hRmem : ∀ P : K'.O[X], P.eval₂ Ψ B.g ∈ R := by
    intro P
    rw [Polynomial.eval₂_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ =>
      Subalgebra.mul_mem _ (hO _) (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O B.g) _)
  let r : R := ⟨R'.eval₂ Ψ B.g, hRmem R'⟩
  have hpow : (g' - x') ^ Q.natDegree = -(algebraMap K.O R ϖ * r) := by
    apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_sub, Subalgebra.coe_neg, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap, g', x', r]
    rw [← hev]; ring
  set u := h * zi
  have hinv : algebraMap K.O R ϖ * (-(r * u ^ Q.natDegree)) = 1 := by
    have : ((g' - x') * u) ^ Q.natDegree = 1 := by rw [hunit, one_pow]
    rw [mul_pow, hpow] at this
    rw [← this]; ring

  letI : Algebra K'.O B.A := Ψ.toAlgebra
  have hgint : IsIntegral K'.O B.g := ⟨Q, hQm, hQg⟩
  have hRint : ∀ w ∈ R, IsIntegral K'.O w := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hgint
    | algebraMap a =>
      rw [← hΨφ a]; exact isIntegral_algebraMap (R := K'.O) (x := intMap hU a)
    | add x y _ _ hx hy => exact hx.add hy
    | mul x y _ _ hx hy => exact hx.mul hy
  set v : R := -(r * u ^ Q.natDegree)
  have hvint : IsIntegral K'.O (v : B.A) := hRint _ v.2
  have hv1 : Ψ (intMap hU ϖ) * (v : B.A) = 1 := by
    have := congrArg Subtype.val hinv
    simpa [hΨφ] using this
  have hϖ0 : intMap hU ϖ ≠ 0 := fun h0 => hϖ.ne_zero ((intMap_injective hU) (by rw [h0, map_zero]))
  have hπ0 : algebraMap K'.O K'.E (intMap hU ϖ) ≠ 0 := by
    intro h0; exact hϖ0 (IsFractionRing.injective K'.O K'.E (by rw [h0, map_zero]))
  set t : K'.E := (algebraMap K'.O K'.E (intMap hU ϖ))⁻¹
  have hψt : ψ t = v := by
    have h1 : Ψ (intMap hU ϖ) * ψ t = 1 := by
      rw [hΨdef, RingHom.comp_apply, ← map_mul, mul_inv_cancel₀ hπ0, map_one]
    calc ψ t = ((v : B.A) * Ψ (intMap hU ϖ)) * ψ t := by rw [mul_comm (v : B.A), hv1, one_mul]
      _ = v := by rw [mul_assoc, h1, mul_one]
  let ψA : K'.E →ₐ[K'.O] B.A := { toRingHom := ψ, commutes' := fun _ => rfl }
  have htint : IsIntegral K'.O t := by
    rw [← isIntegral_algHom_iff ψA ψ.injective]
    show IsIntegral K'.O (ψ t)
    rw [hψt]; exact hvint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 htint
  have hb1 : intMap hU ϖ * b = 1 := by
    apply IsFractionRing.injective K'.O K'.E
    rw [map_mul, hb, mul_inv_cancel₀ hπ0, map_one]
  have hmem : intMap hU ϖ ∈ IsLocalRing.maximalIdeal K'.O := by
    rw [hmax]; exact Ideal.subset_span rfl
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem ⟨⟨_, b, hb1, by rw [mul_comm]; exact hb1⟩, rfl⟩

end GlobalTheory.UnitLemma.Unr
