import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals

noncomputable section

namespace GlobalTheory.RayFieldCompare

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Establish `hn : Nat.card G = (Nat.card G - 1) + 1` using `(Nat.sub_add_cancel Nat.card_pos).symm`. Establish `key : ∀ J : H, ∃ m ∈ M, φ m = φ J ∧ J⁻¹ * m ∈ P`. Introduce `J`. Establish `hJ : J ∈ Subgroup.closure (M : Set H)` using `hM ▸ Subgroup.mem_top J`. Proceed by induction on `hJ using Subgroup.closure_induction with`.

Consider the case `mem x hx => exact ⟨x, hx, rfl, by simp⟩`. Consider the case `one => exact ⟨1, M.one_mem, rfl, by simp⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha, ha1, ha2⟩` from `hx`. Take `⟨b, hb, hb1, hb2⟩` from `hy`.

Use `⟨a * b, M.mul_mem ha hb, by rw [map_mul, map_mul, ha1, hb1], ?_⟩` and prove the remaining obligations. Use `P.mul_mem ha2 hb2` as an intermediate fact. Rewrite `this` using `[mul_mul_mul_comm, ← mul_inv]`. Then use the resulting hypothesis. Consider the case `inv x _ hx`. Take `⟨a, ha, ha1, ha2⟩` from `hx`.

Establish `h1 : φ (a ^ Nat.card G) = 1` using `by rw [map_pow, pow_card_eq_one']`. Establish `h2` using `(h _ (M.pow_mem ha _)).1 h1`. Use `⟨a ^ (Nat.card G - 1), M.pow_mem ha _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv, ← ha1]`. Rewrite `h1` using `[hn, pow_succ, map_mul]`.

Conclude with `eq_inv_of_mul_eq_one_left h1`. Use `P.mul_mem (P.inv_mem ha2) h2` as an intermediate fact. Rewrite `this` using `[hn, pow_succ]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_inv, inv_inv, mul_comm (a ^ _) a, mul_assoc, inv_mul_cancel_left]`.

Use extensionality with `J`. Take `⟨m, hm, h1, h2⟩` from `key J`. Rewrite using `[MonoidHom.mem_ker, ← h1, h m hm]`. Prove the components needed by the constructor for the conclusion. Introduce `hp`.

Use `P.mul_mem (P.inv_mem h2) hp` as an intermediate fact. Simplify using `using this`. Introduce `hp`. Simplify using `using P.mul_mem hp h2`.
-/
theorem ker_eq_of_submonoid {H G : Type*} [CommGroup H] [Group G] [Finite G] (M : Submonoid H)
    (hM : Subgroup.closure (M : Set H) = ⊤) (P : Subgroup H) (φ : H →* G)
    (h : ∀ m ∈ M, φ m = 1 ↔ m ∈ P) : φ.ker = P := by
  have hn : Nat.card G = (Nat.card G - 1) + 1 := (Nat.sub_add_cancel Nat.card_pos).symm
  have key : ∀ J : H, ∃ m ∈ M, φ m = φ J ∧ J⁻¹ * m ∈ P := by
    intro J
    have hJ : J ∈ Subgroup.closure (M : Set H) := hM ▸ Subgroup.mem_top J
    induction hJ using Subgroup.closure_induction with
    | mem x hx => exact ⟨x, hx, rfl, by simp⟩
    | one => exact ⟨1, M.one_mem, rfl, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, ha1, ha2⟩ := hx
      obtain ⟨b, hb, hb1, hb2⟩ := hy
      refine ⟨a * b, M.mul_mem ha hb, by rw [map_mul, map_mul, ha1, hb1], ?_⟩
      have := P.mul_mem ha2 hb2
      rwa [mul_mul_mul_comm, ← mul_inv] at this
    | inv x _ hx =>
      obtain ⟨a, ha, ha1, ha2⟩ := hx
      have h1 : φ (a ^ Nat.card G) = 1 := by rw [map_pow, pow_card_eq_one']
      have h2 := (h _ (M.pow_mem ha _)).1 h1
      refine ⟨a ^ (Nat.card G - 1), M.pow_mem ha _, ?_, ?_⟩
      · rw [map_inv, ← ha1]
        rw [hn, pow_succ, map_mul] at h1
        exact eq_inv_of_mul_eq_one_left h1
      · have := P.mul_mem (P.inv_mem ha2) h2
        rw [hn, pow_succ] at this
        convert this using 1
        rw [mul_inv, inv_inv, mul_comm (a ^ _) a, mul_assoc, inv_mul_cancel_left]
  ext J
  obtain ⟨m, hm, h1, h2⟩ := key J
  rw [MonoidHom.mem_ker, ← h1, h m hm]
  constructor
  · intro hp
    have := P.mul_mem (P.inv_mem h2) hp
    simpa using this
  · intro hp
    simpa using P.mul_mem hp h2

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Use `(FractionalIdeal.finite_factors J).subset ?_` and prove the remaining obligations. Introduce `𝔭 h h0`. Conclude with `h (by simp only [Set.mem_ofPred_eq] at h0; simp [h0])`.
-/
theorem finite_support_zpow {A : Type*} [CommGroup A] (f : HeightOneSpectrum (𝓞 K) → A)
    (J : FractionalIdeal (𝓞 K)⁰ K) :
    Function.HasFiniteMulSupport fun 𝔭 => f 𝔭 ^ FractionalIdeal.count K 𝔭 J := by
  refine (FractionalIdeal.finite_factors J).subset ?_
  intro 𝔭 h h0
  exact h (by simp only [Set.mem_ofPred_eq] at h0; simp [h0])

def extend {A : Type*} [CommGroup A] (𝔪 : Ideal (𝓞 K)) (f : HeightOneSpectrum (𝓞 K) → A) :
    idealsPrimeTo 𝔪 →* A :=
  MonoidHom.mk' (fun J => ∏ᶠ 𝔭, f 𝔭 ^ FractionalIdeal.count K 𝔭 (J.1 : FractionalIdeal (𝓞 K)⁰ K)) (by
    intro a b
    rw [← finprod_mul_distrib (finite_support_zpow f _) (finite_support_zpow f _)]
    refine finprod_congr fun 𝔭 => ?_
    rw [Subgroup.coe_mul, Units.val_mul, FractionalIdeal.count_mul K 𝔭 a.1.ne_zero b.1.ne_zero, zpow_add])

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∏ᶠ 𝔮, f 𝔮 ^ FractionalIdeal.count K 𝔮 (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = _`. Rewrite using `[finprod_eq_single _ 𝔭, FractionalIdeal.count_self, zpow_one]`. Introduce `𝔮 hq`. Rewrite using `[FractionalIdeal.count_maximal_coprime K 𝔮 hq.symm, zpow_zero]`.
-/
theorem extend_primeElt {A : Type*} [CommGroup A] (𝔪 : Ideal (𝓞 K)) (f : HeightOneSpectrum (𝓞 K) → A)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪) : extend 𝔪 f (primeElt 𝔪 𝔭 h) = f 𝔭 := by
  change ∏ᶠ 𝔮, f 𝔮 ^ FractionalIdeal.count K 𝔮 (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [finprod_eq_single _ 𝔭, FractionalIdeal.count_self, zpow_one]
  intro 𝔮 hq
  rw [FractionalIdeal.count_maximal_coprime K 𝔮 hq.symm, zpow_zero]

open Classical in

def gen (𝔪 : Ideal (𝓞 K)) (𝔭 : HeightOneSpectrum (𝓞 K)) : idealsPrimeTo 𝔪 :=
  if h : ¬ 𝔭.asIdeal ∣ 𝔪 then primeElt 𝔪 𝔭 h else 1

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `MonoidHom.map_finprod ((Units.coeHom _).comp (idealsPrimeTo 𝔪).subtype) (finite_support_zpow (gen 𝔪) (J.1 : FractionalIdeal (𝓞 K)⁰ K))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.1.ne_zero]`.

Use `finprod_congr fun 𝔭 => ?_` and prove the remaining obligations. Distinguish the cases in `h : 𝔭.asIdeal ∣ 𝔪`. Rewrite using `[J.2 𝔭 h]`. Simplify using the standard rewrite rules. Simplify using `[gen, h, primeElt]`.
-/
theorem finprod_gen (𝔪 : Ideal (𝓞 K)) (J : idealsPrimeTo 𝔪) :
    ∏ᶠ 𝔭, gen 𝔪 𝔭 ^ FractionalIdeal.count K 𝔭 (J.1 : FractionalIdeal (𝓞 K)⁰ K) = J := by
  apply Subtype.ext
  apply Units.ext
  have := MonoidHom.map_finprod ((Units.coeHom _).comp (idealsPrimeTo 𝔪).subtype)
    (finite_support_zpow (gen 𝔪) (J.1 : FractionalIdeal (𝓞 K)⁰ K))
  refine this.trans ?_
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.1.ne_zero]
  refine finprod_congr fun 𝔭 => ?_
  by_cases h : 𝔭.asIdeal ∣ 𝔪
  · rw [J.2 𝔭 h]; simp
  · simp [gen, h, primeElt]

/- English proof (translation)
Use `eq_top_iff.2 fun J _ => ?_` and prove the remaining obligations. Rewrite using `[← finprod_gen 𝔪 J]`. Use `finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) fun 𝔭 => S.zpow_mem ?_ _` and prove the remaining obligations. Distinguish the cases in `h : 𝔭.asIdeal ∣ 𝔪`. Simplify using `[gen, h]`.

Simplify `hS 𝔭 h` using `[gen, h]`.
-/
theorem mem_of_primeElt (𝔪 : Ideal (𝓞 K)) (S : Subgroup (idealsPrimeTo 𝔪))
    (hS : ∀ 𝔭 h, primeElt 𝔪 𝔭 h ∈ S) : S = ⊤ := by
  refine eq_top_iff.2 fun J _ => ?_
  rw [← finprod_gen 𝔪 J]
  refine finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) fun 𝔭 => S.zpow_mem ?_ _
  by_cases h : 𝔭.asIdeal ∣ 𝔪
  · simp [gen, h]
  · simpa [gen, h] using hS 𝔭 h

def integral (𝔪 : Ideal (𝓞 K)) : Submonoid (idealsPrimeTo 𝔪) where
  carrier := {J | ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔪 ∧ (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I}
  one_mem' := ⟨1, one_ne_zero, isCoprime_one_left, by simp⟩
  mul_mem' := by
    rintro a b ⟨I, hI, hI', ha⟩ ⟨J, hJ, hJ', hb⟩
    exact ⟨I * J, mul_ne_zero hI hJ, hI'.mul_left hJ', by
      rw [Subgroup.coe_mul, Units.val_mul, ha, hb, FractionalIdeal.coeIdeal_mul]⟩

/- English proof (translation)
The claim follows from `mem_of_primeElt 𝔪 _ fun 𝔭 h => Subgroup.subset_closure ⟨𝔭.asIdeal, 𝔭.ne_bot, by rw [Ideal.isCoprime_iff_sup_eq] by_contra hne have := 𝔭.isMaximal.eq_of_le hne le_sup_left exact h (Ideal.dvd_iff_le.2 (this ▸ le_sup_right)), rfl⟩`.
-/
theorem closure_integral (𝔪 : Ideal (𝓞 K)) :
    Subgroup.closure (integral 𝔪 : Set (idealsPrimeTo 𝔪)) = ⊤ :=
  mem_of_primeElt 𝔪 _ fun 𝔭 h => Subgroup.subset_closure
    ⟨𝔭.asIdeal, 𝔭.ne_bot, by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have := 𝔭.isMaximal.eq_of_le hne le_sup_left
      exact h (Ideal.dvd_iff_le.2 (this ▸ le_sup_right)), rfl⟩

/- English proof (translation)
Use `⟨⟨Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI), fun 𝔭 hp => ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, FractionalIdeal.count_coe K 𝔭 hI]`. Use `norm_cast`. Assume the negation of the conclusion as `hne`. Establish `hd : 𝔭.asIdeal ∣ I` using `(Associates.count_ne_zero_iff_dvd hI 𝔭.irreducible).1 hne`.

Conclude with `𝔭.prime.not_isUnit (hc.isUnit_of_dvd' hd hp)`.
-/
theorem exists_integral (𝔪 I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hc : IsCoprime I 𝔪) :
    ∃ J : idealsPrimeTo 𝔪, (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I := by
  refine ⟨⟨Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI), fun 𝔭 hp => ?_⟩, rfl⟩
  rw [Units.val_mk0, FractionalIdeal.count_coe K 𝔭 hI]
  norm_cast
  by_contra hne
  have hd : 𝔭.asIdeal ∣ I := (Associates.count_ne_zero_iff_dvd hI 𝔭.irreducible).1 hne
  exact 𝔭.prime.not_isUnit (hc.isUnit_of_dvd' hd hp)

/- English proof (translation)
Rewrite using `[Subgroup.mem_subgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, ⟨a, b, hab, hx⟩, hxJ⟩`. Use `⟨a, b, hab, ?_⟩` and prove the remaining obligations. Apply `FractionalIdeal.coeIdeal_injective (K := K)` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[FractionalIdeal.coeIdeal_mul, ← hJ, ← hxJ, coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]`. Conclude with `congrArg _ hx`. Introduce and unpack `⟨a, b, hab, h⟩`. Establish `ha : (a : K) ≠ 0` using `by exact_mod_cast hab.1`.

Establish `hb : (b : K) ≠ 0` using `by exact_mod_cast hab.2.1`. Use `⟨Units.mk0 ((a : K) / b) (div_ne_zero ha hb), ⟨a, b, hab, by simp [hb]⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Establish `h'` using `congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) h`. Simplify using `only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at h'`.

Establish `hb' : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b) ≠ 0`. Simplify `hb` using `[FractionalIdeal.spanSingleton_eq_zero_iff]`. Apply `mul_right_cancel₀ hb'` to reduce the goal to its premises. Rewrite using `[hJ, h', coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_mul_spanSingleton]`. Use `congr 1`.

Conclude with `div_mul_cancel₀ _ hb`.
-/
theorem mem_rayPrincipal_iff (𝔪 I : Ideal (𝓞 K)) (J : idealsPrimeTo 𝔪)
    (hJ : (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I) :
    J ∈ (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪) ↔
      ∃ α β : 𝓞 K, RayPair 𝔪 α β ∧ I * Ideal.span {β} = Ideal.span {α} := by
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, ⟨a, b, hab, hx⟩, hxJ⟩
    refine ⟨a, b, hab, ?_⟩
    apply FractionalIdeal.coeIdeal_injective (K := K)
    simp only
    rw [FractionalIdeal.coeIdeal_mul, ← hJ, ← hxJ, coe_toPrincipalIdeal,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    exact congrArg _ hx
  · rintro ⟨a, b, hab, h⟩
    have ha : (a : K) ≠ 0 := by exact_mod_cast hab.1
    have hb : (b : K) ≠ 0 := by exact_mod_cast hab.2.1
    refine ⟨Units.mk0 ((a : K) / b) (div_ne_zero ha hb), ⟨a, b, hab, by simp [hb]⟩, ?_⟩
    apply Units.ext
    have h' := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) h
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at h'
    have hb' : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b) ≠ 0 := by
      simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hb
    apply mul_right_cancel₀ hb'
    rw [hJ, h', coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    exact div_mul_cancel₀ _ hb

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Use `haveI := 𝔭.isPrime`. Take `⟨⟨P, hP, hl⟩⟩` from `Ideal.nonempty_primesOver (S := 𝓞 L) 𝔭.asIdeal`. Establish `hP0 : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P`. Use `haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0`. Take `⟨σ, hσ⟩` from `IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P`.

Use `⟨σ, P, hP, hl, fun x => ?_⟩` and prove the remaining obligations. Use `hσ x` as an intermediate fact. Rewrite `this` using `[← hl.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]`. Then use the resulting hypothesis.
-/
theorem exists_isFrob [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) : ∃ σ, IsFrob L 𝔭 σ := by
  haveI := 𝔭.isPrime
  obtain ⟨⟨P, hP, hl⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) 𝔭.asIdeal
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P
  refine ⟨σ, P, hP, hl, fun x => ?_⟩
  have := hσ x
  rwa [← hl.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at this

/- English proof (translation)
Take `⟨P, hP, hPl, hs⟩` from `hσ`. Take `⟨Q, hQ, hQl, ht⟩` from `hτ`. Take `⟨g, rfl⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal P Q (L ≃ₐ[K] L)`. Establish `ht' : ∀ x : 𝓞 L, τ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P`. Introduce `x`.

Use `ht (g • x)` as an intermediate fact. Rewrite `this` using `[smul_smul, mul_comm' τ g, mul_smul, ← smul_pow', ← smul_sub, Ideal.smul_mem_pointwise_smul_iff]`. Then use the resulting hypothesis. Establish `: σ * τ⁻¹ = 1`. Use `hu _ ⟨P, hP, hPl, fun x => ?_⟩` and prove the remaining obligations. Use `P.sub_mem (hs (τ⁻¹ • x)) (ht' (τ⁻¹ • x))` as an intermediate fact.

Simplify `this` using `[mul_smul]`. Conclude with `mul_inv_eq_one.1 this`.
-/
theorem isFrob_unique [IsAbelianGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭)
    {σ τ : L ≃ₐ[K] L} (hσ : IsFrob L 𝔭 σ) (hτ : IsFrob L 𝔭 τ) : σ = τ := by
  obtain ⟨P, hP, hPl, hs⟩ := hσ
  obtain ⟨Q, hQ, hQl, ht⟩ := hτ
  obtain ⟨g, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal P Q (L ≃ₐ[K] L)
  have ht' : ∀ x : 𝓞 L, τ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P := by
    intro x
    have := ht (g • x)
    rwa [smul_smul, mul_comm' τ g, mul_smul, ← smul_pow', ← smul_sub, Ideal.smul_mem_pointwise_smul_iff] at this
  have : σ * τ⁻¹ = 1 := by
    refine hu _ ⟨P, hP, hPl, fun x => ?_⟩
    have := P.sub_mem (hs (τ⁻¹ • x)) (ht' (τ⁻¹ • x))
    simpa [mul_smul] using this
  exact mul_inv_eq_one.1 this

/- English proof (translation)
Establish `h : (∀ σ, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ` using `⟨fun τ hτ => by rw [hu τ hτ, map_one], σ, hσ⟩`. Rewrite using `[heckeVal, dif_pos h, isFrob_unique L hu h.2.choose_spec hσ]`.
-/
theorem heckeVal_eq [IsAbelianGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭)
    {σ : L ≃ₐ[K] L} (hσ : IsFrob L 𝔭 σ) (χ : (L ≃ₐ[K] L) →* ℂˣ) : heckeVal L χ 𝔭 = χ σ := by
  have h : (∀ σ, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ :=
    ⟨fun τ hτ => by rw [hu τ hτ, map_one], σ, hσ⟩
  rw [heckeVal, dif_pos h, isFrob_unique L hu h.2.choose_spec hσ]

/- English proof (translation)
Use `MonoidHom.map_finprod ((Units.coeHom ℂ).comp (χ.comp ψ)) (finite_support_zpow (gen 𝔪) (J.1 : FractionalIdeal (𝓞 K)⁰ K))` as an intermediate fact. Rewrite `this` using `[finprod_gen]`. Use `Eq.trans ?_ this.symm` and prove the remaining obligations. Use `finprod_congr fun 𝔭 => ?_` and prove the remaining obligations. Establish `hc` using `FractionalIdeal.count_coe K 𝔭 hI`.

Rewrite `hc` using `[← hJ]`. Distinguish the cases in `h : 𝔭.asIdeal ∣ 𝔪`. Establish `h0` using `J.2 𝔭 h`. Rewrite using `[h0]`. Rewrite `hc` using `[h0, eq_comm, Nat.cast_eq_zero]`.

Rewrite using `[zpow_zero, map_one]`. Use `pow_zero _ using 2` and compare the differences between its conclusion and the goal. Rewrite using `[hc, zpow_natCast, map_pow, heckeVal_eq L (hψ 𝔭 h).1 (hψ 𝔭 h).2]`. Simplify using `[gen, h]`.
-/
theorem heckeIdeal_eq [IsAbelianGalois K L] (𝔪 : Ideal (𝓞 K)) (ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L))
    (hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h))) (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (J : idealsPrimeTo 𝔪) (hJ : (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I) :
    heckeIdeal L χ I = χ (ψ J) := by
  have := MonoidHom.map_finprod ((Units.coeHom ℂ).comp (χ.comp ψ))
    (finite_support_zpow (gen 𝔪) (J.1 : FractionalIdeal (𝓞 K)⁰ K))
  rw [finprod_gen] at this
  refine Eq.trans ?_ this.symm
  refine finprod_congr fun 𝔭 => ?_
  have hc := FractionalIdeal.count_coe K 𝔭 hI
  rw [← hJ] at hc
  by_cases h : 𝔭.asIdeal ∣ 𝔪
  · have h0 := J.2 𝔭 h
    rw [h0]
    rw [h0, eq_comm, Nat.cast_eq_zero] at hc
    rw [zpow_zero, map_one]
    convert pow_zero _ using 2
  · rw [hc, zpow_natCast, map_pow, heckeVal_eq L (hψ 𝔭 h).1 (hψ 𝔭 h).2]
    simp [gen, h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hne`. Use `letI : CommGroup (L ≃ₐ[K] L) := { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := mul_comm' }`. Take `⟨χ, hχ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ hne`.

Use `h χ` as an intermediate fact. Rewrite `this` using `[heckeIdeal_eq L 𝔪 ψ hψ χ I hI J hJ]`. Conclude with `hχ (Units.ext this)`. Introduce `h χ`. Rewrite using `[heckeIdeal_eq L 𝔪 ψ hψ χ I hI J hJ, h, map_one, Units.val_one]`.
-/
theorem forall_heckeIdeal_iff [IsAbelianGalois K L] (𝔪 : Ideal (𝓞 K)) (ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L))
    (hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h)))
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (J : idealsPrimeTo 𝔪) (hJ : (J.1 : FractionalIdeal (𝓞 K)⁰ K) = I) :
    (∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔ ψ J = 1 := by
  constructor
  · intro h
    by_contra hne
    letI : CommGroup (L ≃ₐ[K] L) := { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := mul_comm' }
    obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ hne
    have := h χ
    rw [heckeIdeal_eq L 𝔪 ψ hψ χ I hI J hJ] at this
    exact hχ (Units.ext this)
  · intro h χ
    rw [heckeIdeal_eq L 𝔪 ψ hψ χ I hI J hJ, h, map_one, Units.val_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hu, hg, hk⟩`. Use `letI : CommGroup (L ≃ₐ[K] L) := { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := mul_comm' }`. Use `choose fr hfr using exists_isFrob (K := K) L`. Set `ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L)` to `extend 𝔪 fr`.

Establish `hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h))` using `fun 𝔭 h => ⟨hu 𝔭 h, by rw [extend_primeElt]; exact hfr 𝔭⟩`. Establish `hker : ψ.ker = (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪)`. Use `ker_eq_of_submonoid (integral 𝔪) (closure_integral 𝔪) _ ψ ?_` and prove the remaining obligations. Introduce and unpack `J ⟨I, hI, hc, hJ⟩`. Rewrite using `[← forall_heckeIdeal_iff L 𝔪 ψ hψ I hI J hJ, hk I hI hc, mem_rayPrincipal_iff 𝔪 I J hJ]`.

Establish `hsurj : Function.Surjective ψ`. Rewrite using `[← MonoidHom.range_eq_top, eq_top_iff, ← hg, Subgroup.closure_le]`. Introduce and unpack `σ ⟨𝔭, h, hσ⟩`. Conclude with `⟨primeElt 𝔪 𝔭 h, isFrob_unique L (hu 𝔭 h) (hψ 𝔭 h).2 hσ⟩`. Conclude with `⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), hψ⟩`.

Introduce and unpack `⟨Art, h⟩`. Set `ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L)` to `Art.toMonoidHom.comp (QuotientGroup.mk' _)`. Establish `hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h))` using `h`. Use `⟨fun 𝔭 hp => (h 𝔭 hp).1, ?_, fun I hI hc => ?_⟩` and prove the remaining obligations. Use `mem_of_primeElt 𝔪 ((Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob L 𝔭 σ}).comap ψ) fun 𝔭 hp => Subgroup.subset_closure ⟨𝔭, hp, (hψ 𝔭 hp).2⟩` as an intermediate fact.

Use `eq_top_iff.2 fun σ _ => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Art.surjective σ`. Take `⟨J, rfl⟩` from `QuotientGroup.mk_surjective c`. Conclude with `(this ▸ Subgroup.mem_top J : J ∈ Subgroup.comap ψ _)`. Take `⟨J, hJ⟩` from `exists_integral 𝔪 I hI hc`.

Rewrite using `[forall_heckeIdeal_iff L 𝔪 ψ hψ I hI J hJ, ← mem_rayPrincipal_iff 𝔪 I J hJ, ← QuotientGroup.eq_one_iff]`. Conclude with `Art.map_eq_one_iff`.
-/
theorem clauses_iff [IsAbelianGalois K L] (𝔪 : Ideal (𝓞 K)) :
    ((∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 → UnramIn L 𝔭) ∧
      Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔪 →
        ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
          ∃ α β : 𝓞 K, RayPair 𝔪 α β ∧ I * Ideal.span {β} = Ideal.span {α})) ↔
    ∃ Art : RayClassGroup 𝔪 ≃* (L ≃ₐ[K] L),
      ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪),
        UnramIn L 𝔭 ∧ IsFrob L 𝔭 (Art (primeClass 𝔪 𝔭 h)) := by
  constructor
  · rintro ⟨hu, hg, hk⟩
    letI : CommGroup (L ≃ₐ[K] L) := { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := mul_comm' }
    choose fr hfr using exists_isFrob (K := K) L
    let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := extend 𝔪 fr
    have hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h)) := fun 𝔭 h =>
      ⟨hu 𝔭 h, by rw [extend_primeElt]; exact hfr 𝔭⟩
    have hker : ψ.ker = (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪) := by
      refine ker_eq_of_submonoid (integral 𝔪) (closure_integral 𝔪) _ ψ ?_
      rintro J ⟨I, hI, hc, hJ⟩
      rw [← forall_heckeIdeal_iff L 𝔪 ψ hψ I hI J hJ, hk I hI hc, mem_rayPrincipal_iff 𝔪 I J hJ]
    have hsurj : Function.Surjective ψ := by
      rw [← MonoidHom.range_eq_top, eq_top_iff, ← hg, Subgroup.closure_le]
      rintro σ ⟨𝔭, h, hσ⟩
      exact ⟨primeElt 𝔪 𝔭 h, isFrob_unique L (hu 𝔭 h) (hψ 𝔭 h).2 hσ⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), hψ⟩
  · rintro ⟨Art, h⟩
    let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := Art.toMonoidHom.comp (QuotientGroup.mk' _)
    have hψ : ∀ 𝔭 h, UnramIn L 𝔭 ∧ IsFrob L 𝔭 (ψ (primeElt 𝔪 𝔭 h)) := h
    refine ⟨fun 𝔭 hp => (h 𝔭 hp).1, ?_, fun I hI hc => ?_⟩
    · have := mem_of_primeElt 𝔪 ((Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
        ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob L 𝔭 σ}).comap ψ) fun 𝔭 hp => Subgroup.subset_closure ⟨𝔭, hp, (hψ 𝔭 hp).2⟩
      refine eq_top_iff.2 fun σ _ => ?_
      obtain ⟨c, rfl⟩ := Art.surjective σ
      obtain ⟨J, rfl⟩ := QuotientGroup.mk_surjective c
      exact (this ▸ Subgroup.mem_top J : J ∈ Subgroup.comap ψ _)
    · obtain ⟨J, hJ⟩ := exists_integral 𝔪 I hI hc
      rw [forall_heckeIdeal_iff L 𝔪 ψ hψ I hI J hJ, ← mem_rayPrincipal_iff 𝔪 I J hJ,
        ← QuotientGroup.eq_one_iff]
      exact Art.map_eq_one_iff

/- English proof (translation)
Use `forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun 𝔪 => forall_congr' fun _ => exists_congr fun L => exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => ?_` and prove the remaining obligations. Conclude with `⟨fun ⟨i, h⟩ => ⟨i, (clauses_iff L 𝔪).1 h⟩, fun ⟨i, h⟩ => ⟨i, (clauses_iff L 𝔪).2 h⟩⟩`.
-/
theorem rayField_iff : GlobalTheory.NT.RayField ↔ GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayField := by
  refine forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun 𝔪 =>
    forall_congr' fun _ => exists_congr fun L => exists_congr fun _ => exists_congr fun _ =>
    exists_congr fun _ => ?_
  exact ⟨fun ⟨i, h⟩ => ⟨i, (clauses_iff L 𝔪).1 h⟩, fun ⟨i, h⟩ => ⟨i, (clauses_iff L 𝔪).2 h⟩⟩

end GlobalTheory.RayFieldCompare

end
