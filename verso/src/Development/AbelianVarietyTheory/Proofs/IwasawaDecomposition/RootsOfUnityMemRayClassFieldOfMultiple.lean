import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayZeta

variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]

omit [NumberField M] [NumberField L] in

/- English proof (translation)
Take `⟨P, hP, hPo, hx⟩` from `h`. Use `⟨P.under (𝓞 M), inferInstance, inferInstance, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap (𝓞 M) (𝓞 L) (σ.restrictNormal M • x) = σ • algebraMap (𝓞 M) (𝓞 L) x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `σ.restrictNormal_commutes M x`.

Rewrite using `[Ideal.under, Ideal.mem_comap, map_sub, map_pow, h1]`. Conclude with `hx _`.
-/
theorem isFrob_restrictNormal [Normal K M] {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : GlobalTheory.NT.IsFrob L v σ) :
    GlobalTheory.NT.IsFrob M v (σ.restrictNormal M) := by
  obtain ⟨P, hP, hPo, hx⟩ := h
  refine ⟨P.under (𝓞 M), inferInstance, inferInstance, fun x => ?_⟩
  have h1 : algebraMap (𝓞 M) (𝓞 L) (σ.restrictNormal M • x) = σ • algebraMap (𝓞 M) (𝓞 L) x := by
    apply RingOfIntegers.ext
    exact σ.restrictNormal_commutes M x
  rw [Ideal.under, Ideal.mem_comap, map_sub, map_pow, h1]
  exact hx _

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors IntermediateField in
variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] in
/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hS : ∑ k ∈ Finset.range p, x ^ k * y ^ (p - 1 - k) = 0`. Use `geom_sum₂_mul x y p` as an intermediate fact. Rewrite `this` using `[hx, hy, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)`.

Establish `hmem : (p : R) * x ^ (p - 1) ∈ P`. Establish `: (p : R) * x ^ (p - 1) = ∑ k ∈ Finset.range p, (x ^ (p - 1) - x ^ k * y ^ (p - 1 - k))`. Rewrite using `[Finset.sum_sub_distrib, hS, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_zero]`. Rewrite using `[this]`. Use `Ideal.sum_mem _ fun k hk => ?_` and prove the remaining obligations.

Establish `hk' : k + (p - 1 - k) = p - 1`. Use `Finset.mem_range.mp hk` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨c, hc⟩` from `sub_dvd_pow_sub_pow x y (p - 1 - k)`. Establish `: x ^ (p - 1) - x ^ k * y ^ (p - 1 - k) = x ^ k * ((x - y) * c)`.

Rewrite using `[← hc, mul_sub, ← pow_add, hk']`. Rewrite using `[this]`. Conclude with `P.mul_mem_left _ (P.mul_mem_right _ hxy)`. Break down `Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h` into its components or cases. Conclude with `hp h`.

Establish `hx0 : x ∈ P` using `Ideal.IsPrime.mem_of_pow_mem ‹_› _ h`. Establish `: (1 : R) ∈ P`. Rewrite using `[← hx]`. Break down `Nat.eq_zero_or_pos p with rfl | hp0` into its components or cases. Simplify using `at hp`.

Conclude with `P.pow_mem_of_mem hx0 _ hp0`. Conclude with `Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr this)`.
-/
private theorem eq_of_pow_eq_one_of_sub_mem_prime {R : Type} [CommRing R] [IsDomain R] (P : Ideal R)
    [P.IsPrime] (p : ℕ) (hp : (p : R) ∉ P) {x y : R} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have hS : ∑ k ∈ Finset.range p, x ^ k * y ^ (p - 1 - k) = 0 := by
    have := geom_sum₂_mul x y p
    rw [hx, hy, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hmem : (p : R) * x ^ (p - 1) ∈ P := by
    have : (p : R) * x ^ (p - 1) = ∑ k ∈ Finset.range p, (x ^ (p - 1) - x ^ k * y ^ (p - 1 - k)) := by
      rw [Finset.sum_sub_distrib, hS, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_zero]
    rw [this]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk' : k + (p - 1 - k) = p - 1 := by
      have := Finset.mem_range.mp hk; omega
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow x y (p - 1 - k)
    have : x ^ (p - 1) - x ^ k * y ^ (p - 1 - k) = x ^ k * ((x - y) * c) := by
      rw [← hc, mul_sub, ← pow_add, hk']
    rw [this]
    exact P.mul_mem_left _ (P.mul_mem_right _ hxy)
  rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
  · exact hp h
  · have hx0 : x ∈ P := Ideal.IsPrime.mem_of_pow_mem ‹_› _ h
    have : (1 : R) ∈ P := by
      rw [← hx]
      rcases Nat.eq_zero_or_pos p with rfl | hp0
      · simp at hp
      · exact P.pow_mem_of_mem hx0 _ hp0
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr this)

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors IntermediateField in
variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] in

/- English proof (translation)
Introduce `K M L _ _ _ _ _ _ _ _ _ _ _ 𝔮 p hp hq hM hgen hnorm ζ hζ`. Take `⟨hab, hunr, -, hray⟩` from `hM`. Use `haveI : IsGalois K M := hab.toIsGalois`. Establish `hpow : ∀ a b : ℕ, a ≡ b [MOD p] → ζ ^ a = ζ ^ b`. Introduce `a b h`.

Rewrite using `[← Nat.mod_add_div a p, ← Nat.mod_add_div b p, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow, one_pow, (h : a % p = b % p)]`. Establish `hζint : IsIntegral ℤ ζ` using `IsIntegral.of_pow (Nat.pos_of_ne_zero hp) (hζ ▸ isIntegral_one)`. Set `z : 𝓞 L` to `⟨ζ, hζint⟩`. Establish `hz : z ^ p = 1`. Conclude with `NumberField.RingOfIntegers.ext hζ`.

Establish `hfrob : ∀ (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)), ¬ v.asIdeal ∣ 𝔮 → _root_.GlobalTheory.NT.IsFrob L v σ → σ ζ = ζ ^ Ideal.absNorm v.asIdeal`. Introduce `σ v hv hF`. Take `⟨P, hP, hlies, hx⟩` from `hF`. Establish `hpP : ((p : ℕ) : 𝓞 L) ∉ P`. Introduce `hmem`.

Apply `hv` to reduce the goal to its premises. Rewrite using `[Ideal.dvd_iff_le]`. Use `hq.trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, Ideal.over_def P v.asIdeal, Ideal.under, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `hmem`.

Establish `h1 : (σ • z) ^ p = 1` using `by rw [← smul_pow', hz, smul_one]`. Use `eq_of_pow_eq_one_of_sub_mem_prime P p hpP h1 (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (hx z)` as an intermediate fact. Conclude with `congrArg (fun w : 𝓞 L => (w : L)) this`. Set `Q : (L ≃ₐ[K] L) → Prop` to `fun σ => ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧ (∀ χ : (M ≃ₐ[K] M) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal M χ I = (χ (AlgEquiv.restrictNormalHom M σ) : ℂ)) ∧ σ ζ = ζ ^ Ideal.absNorm I`. Establish `hmul : ∀ σ τ, Q σ → Q τ → Q (σ * τ)`.

Introduce and unpack `σ τ ⟨I, hI0, hIq, hIχ, hIζ⟩ ⟨J, hJ0, hJq, hJχ, hJζ⟩`. Use `⟨I * J, fun h => (Ideal.mul_eq_bot.mp h).elim hI0 hJ0, hIq.mul_left hJq, fun χ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.GlobalTheory.NT.Model.heckeIdeal_mul M χ hI0 hJ0, hIχ, hJχ, map_mul, map_mul, Units.val_mul]`. Rewrite using `[AlgEquiv.mul_apply, hJζ, map_pow, hIζ, ← pow_mul, map_mul]`. Establish `hone : Q 1`.

Use `⟨1, by rw [Ideal.one_eq_top]; exact top_ne_bot, isCoprime_one_left, fun χ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.GlobalTheory.NT.Model.heckeIdeal_top, map_one, map_one, Units.val_one]`. Rewrite using `[map_one, pow_one, AlgEquiv.one_apply]`. Establish `hgenQ : ∀ σ ∈ {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧ _root_.GlobalTheory.NT.IsFrob L v σ}, Q σ`. Introduce and unpack `σ ⟨v, hv, hF⟩`.

Use `⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_, hfrob σ v hv hF⟩` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `hne`. Apply `hv` to reduce the goal to its premises. Rewrite using `[Ideal.dvd_iff_le]`.

Use `v.isMaximal.eq_of_le hne le_sup_left` as an intermediate fact. Rewrite using `[this]`. Conclude with `le_sup_right`. Rewrite using `[_root_.GlobalTheory.NT.Model.heckeIdeal_prime, _root_.GlobalTheory.NT.heckeVal_of_unramIn M χ (hunr v hv) (_root_.GlobalTheory.RayMaximal.isFrob_restrictNormal (L := M) hF)]`. Both sides reduce to the same expression.

Establish `hall : ∀ σ, Q σ`. Introduce `σ`. Establish `hσ : σ ∈ Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧ _root_.GlobalTheory.NT.IsFrob L v σ}` using `hgen ▸ Subgroup.mem_top σ`. Proceed by induction on `hσ using Subgroup.closure_induction with`. Consider the case `mem σ hσ => exact hgenQ σ hσ`.

Consider the case `one => exact hone`. Consider the case `mul σ τ _ _ hσ hτ => exact hmul σ τ hσ hτ`. Consider the case `inv σ _ hσ`. Establish `hpowQ : ∀ n : ℕ, Q (σ ^ n)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simpa using hone`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `hmul _ _ ih hσ`. Establish `: σ⁻¹ = σ ^ (orderOf σ - 1)`.

Use `(eq_inv_of_mul_eq_one_left ?_).symm` and prove the remaining obligations. Rewrite using `[← pow_succ, Nat.sub_add_cancel (orderOf_pos σ), pow_orderOf_eq_one]`. Rewrite using `[this]`. Conclude with `hpowQ _`. Use `haveI := IsGalois.tower_top_of_isGalois K M L`.

Rewrite using `[InfiniteGalois.mem_range_algebraMap_iff_fixed]`. Introduce `τ`. Take `⟨I, hI0, hIq, hIχ, hIζ⟩` from `hall (τ.restrictScalars K)`. Establish `hres : AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1`. Use extensionality with `m`.

Apply `(algebraMap M L).injective` to reduce the goal to its premises. Use `show algebraMap M L ((τ.restrictScalars K).restrictNormal M m) = _`. Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Simplify using the standard rewrite rules. Take `⟨α, β, hαβ, hI⟩` from `(hray I hI0 hIq).mp fun χ => by`.

Rewrite using `[hIχ, hres, map_one, Units.val_one]`. Use `hpow _ _ (hnorm I α β hαβ hI)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Conclude with `hIζ.trans this`.
-/
theorem _root_.GlobalTheory.Mem.RayZeta.root_mem_rayField : ∀ (K M L : Type) [Field K] [NumberField K]
    [Field M] [NumberField M] [Field L] [NumberField L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] [IsGalois K L] (𝔮 : Ideal (𝓞 K))
    (p : ℕ), p ≠ 0 →
    𝔮 ≤ Ideal.span {(p : 𝓞 K)} → _root_.GlobalTheory.Mem.Fld.IsRayField K M 𝔮 →
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ} = ⊤ →
    (∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), _root_.GlobalTheory.NT.RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} →
      Ideal.absNorm I ≡ 1 [MOD p]) → ∀ ζ : L, ζ ^ p = 1 → ζ ∈ Set.range (algebraMap M L) := by
  intro K M L _ _ _ _ _ _ _ _ _ _ _ 𝔮 p hp hq hM hgen hnorm ζ hζ
  obtain ⟨hab, hunr, -, hray⟩ := hM
  haveI : IsGalois K M := hab.toIsGalois
  have hpow : ∀ a b : ℕ, a ≡ b [MOD p] → ζ ^ a = ζ ^ b := by
    intro a b h
    rw [← Nat.mod_add_div a p, ← Nat.mod_add_div b p, pow_add, pow_add, pow_mul, pow_mul, hζ,
      one_pow, one_pow, (h : a % p = b % p)]
  have hζint : IsIntegral ℤ ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hp) (hζ ▸ isIntegral_one)
  let z : 𝓞 L := ⟨ζ, hζint⟩
  have hz : z ^ p = 1 := by
    exact NumberField.RingOfIntegers.ext hζ
  have hfrob : ∀ (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)), ¬ v.asIdeal ∣ 𝔮 →
      _root_.GlobalTheory.NT.IsFrob L v σ → σ ζ = ζ ^ Ideal.absNorm v.asIdeal := by
    intro σ v hv hF
    obtain ⟨P, hP, hlies, hx⟩ := hF
    have hpP : ((p : ℕ) : 𝓞 L) ∉ P := by
      intro hmem
      apply hv
      rw [Ideal.dvd_iff_le]
      refine hq.trans ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, Ideal.over_def P v.asIdeal, Ideal.under,
        SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact hmem
    have h1 : (σ • z) ^ p = 1 := by rw [← smul_pow', hz, smul_one]
    have := eq_of_pow_eq_one_of_sub_mem_prime P p hpP h1 (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (hx z)
    exact congrArg (fun w : 𝓞 L => (w : L)) this
  let Q : (L ≃ₐ[K] L) → Prop := fun σ => ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧
    (∀ χ : (M ≃ₐ[K] M) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal M χ I =
      (χ (AlgEquiv.restrictNormalHom M σ) : ℂ)) ∧ σ ζ = ζ ^ Ideal.absNorm I
  have hmul : ∀ σ τ, Q σ → Q τ → Q (σ * τ) := by
    rintro σ τ ⟨I, hI0, hIq, hIχ, hIζ⟩ ⟨J, hJ0, hJq, hJχ, hJζ⟩
    refine ⟨I * J, fun h => (Ideal.mul_eq_bot.mp h).elim hI0 hJ0, hIq.mul_left hJq, fun χ => ?_, ?_⟩
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_mul M χ hI0 hJ0, hIχ, hJχ, map_mul, map_mul, Units.val_mul]
    · rw [AlgEquiv.mul_apply, hJζ, map_pow, hIζ, ← pow_mul, map_mul]
  have hone : Q 1 := by
    refine ⟨1, by rw [Ideal.one_eq_top]; exact top_ne_bot, isCoprime_one_left, fun χ => ?_, ?_⟩
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_top, map_one, map_one, Units.val_one]
    · rw [map_one, pow_one, AlgEquiv.one_apply]
  have hgenQ : ∀ σ ∈ {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ}, Q σ := by
    rintro σ ⟨v, hv, hF⟩
    refine ⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_, hfrob σ v hv hF⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      apply hv
      rw [Ideal.dvd_iff_le]
      have := v.isMaximal.eq_of_le hne le_sup_left
      rw [this]
      exact le_sup_right
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_prime,
        _root_.GlobalTheory.NT.heckeVal_of_unramIn M χ (hunr v hv)
          (_root_.GlobalTheory.RayMaximal.isFrob_restrictNormal (L := M) hF)]
      rfl
  have hall : ∀ σ, Q σ := by
    intro σ
    have hσ : σ ∈ Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ} := hgen ▸ Subgroup.mem_top σ
    induction hσ using Subgroup.closure_induction with
    | mem σ hσ => exact hgenQ σ hσ
    | one => exact hone
    | mul σ τ _ _ hσ hτ => exact hmul σ τ hσ hτ
    | inv σ _ hσ =>
      have hpowQ : ∀ n : ℕ, Q (σ ^ n) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hσ
      have : σ⁻¹ = σ ^ (orderOf σ - 1) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos σ), pow_orderOf_eq_one]
      rw [this]
      exact hpowQ _
  haveI := IsGalois.tower_top_of_isGalois K M L
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro τ
  obtain ⟨I, hI0, hIq, hIχ, hIζ⟩ := hall (τ.restrictScalars K)
  have hres : AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1 := by
    ext m
    apply (algebraMap M L).injective
    show algebraMap M L ((τ.restrictScalars K).restrictNormal M m) = _
    rw [AlgEquiv.restrictNormal_commutes]
    simp
  obtain ⟨α, β, hαβ, hI⟩ := (hray I hI0 hIq).mp fun χ => by
    rw [hIχ, hres, map_one, Units.val_one]
  have := hpow _ _ (hnorm I α β hαβ hI)
  rw [pow_one] at this
  exact hIζ.trans this

end GlobalTheory.Mem.RayZeta

end
