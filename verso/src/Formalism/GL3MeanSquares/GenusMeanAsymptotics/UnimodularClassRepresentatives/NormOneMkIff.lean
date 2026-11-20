import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SmulGenMemIff

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.NormOneGroup

open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals Formalism.HermitianLattices.Ext.L3.EndomorphismScalars

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V} {h : V →ₗ⋆[K] V →ₗ[K] K}

/- English proof (translation)
Establish `e3 : ∀ c : 𝓞 K, algebraMap (𝓞 K) K (conjO K c) = star (algebraMap (𝓞 K) K c)` using `fun _ => rfl`. Establish `eφ : ∀ a : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F)` using `fun _ => rfl`. Establish `hψ : ∀ a c : 𝓞 F, algebraMap F K ((a * c : 𝓞 F) : F) = algebraMap F K (a : F) * algebraMap F K (c : F)` using `fun a c => by`. Rewrite using `[show ((a * c : 𝓞 F) : F) = (a : F) * (c : F) from rfl, map_mul]`. Establish `hfix : ∀ a : 𝓞 F, star (algebraMap F K (a : F)) = algebraMap F K (a : F)` using `fun a => (hF _).mpr ⟨_, rfl⟩`.

Establish `hsmul1 : ∀ (c : 𝓞 K) (u w : V), h (c • u) w = star (algebraMap (𝓞 K) K c) * h u w` using `fun c u w => by rw [← algebraMap_smul K c u, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]`. Establish `hsmul2 : ∀ (c : 𝓞 K) (u w : V), h u (c • w) = algebraMap (𝓞 K) K c * h u w` using `fun c u w => by rw [← algebraMap_smul K c w, map_smul, smul_eq_mul]`. Establish `hA : ∀ w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L), ∀ u : ↥L, (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (w : V) (u : V)) ∧ (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V))`. Introduce `w hw u`. Use `Submodule.smul_induction_on hw ?_ ?_` and prove the remaining obligations.

Introduce `c hc m _`. Take `⟨r1, hr1⟩` from `Submodule.mem_one.mp (hLi m m.2 u u.2)`. Take `⟨r2, hr2⟩` from `Submodule.mem_one.mp (hLi u u.2 m m.2)`. Use `⟨⟨conjO K c * r1, Ideal.mul_mem_right _ _ (conjO_mem_extP hF 𝔭 k hc), ?_⟩, ⟨c * r2, Ideal.mul_mem_right _ _ hc, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_mul, e3, hr1, Submodule.coe_smul, hsmul1]`.

Rewrite using `[map_mul, hr2, Submodule.coe_smul, hsmul2]`. Introduce `w1 w2 h1 h2`. Take `⟨⟨z1, hz1, ez1⟩, ⟨z1', hz1', ez1'⟩⟩` from `h1`. Take `⟨⟨z2, hz2, ez2⟩, ⟨z2', hz2', ez2'⟩⟩` from `h2`. Use `⟨⟨z1 + z2, add_mem hz1 hz2, ?_⟩, ⟨z1' + z2', add_mem hz1' hz2', ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[map_add, ez1, ez2, Submodule.coe_add, map_add, LinearMap.add_apply]`. Rewrite using `[map_add, ez1', ez2', Submodule.coe_add, map_add]`. Establish `hB : ∀ u w : ↥L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ r ∈ extP K 𝔭 ^ v, algebraMap (𝓞 K) K r = algebraMap F K (t : F) * h (u : V) (w : V)`. Introduce `u w`. Take `⟨t1, ht1, a1, ha1⟩` from `he.2.2 u u.2`.

Take `⟨t2, ht2, a2, ha2⟩` from `he.2.2 w w.2`. Use `⟨t1 * t2, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht1 ht2, conjO K a1 * a2 * algebraMap (𝓞 F) (𝓞 K) n, Ideal.mul_mem_left _ _ (map_mem_extP hv), ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg₂ (fun p q => h p q) ha1 ha2`. Simplify using `only [hsmul1, hsmul2, hn, eφ, hfix] at h1`. Rewrite using `[map_mul, map_mul, e3, eφ, hψ]`.

Take the linear combination `-h1`. Take `⟨⟨z1, hz1, ez1⟩, -⟩` from `hA (x' - b • x) hx y'`. Take `⟨-, ⟨z2, hz2, ez2⟩⟩` from `hA (y' - b • y) hy (b • x)`. Take `⟨t, ht, r, hr, er⟩` from `hB x y`. Use `⟨t, ht, algebraMap (𝓞 F) (𝓞 K) t * (z1 + z2) + (conjO K b * b - 1) * r, ?_, ?_⟩` and prove the remaining obligations.

Use `add_mem (Ideal.mul_mem_left _ _ (add_mem hz1 hz2)) ?_` and prove the remaining obligations. Establish `hpow : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - v) * extP K 𝔭 ^ v`. Rewrite using `[← pow_add, Nat.sub_add_cancel hvk]`. Rewrite using `[hpow]`. Conclude with `Ideal.mul_mem_mul hc hr`.

Rewrite using `[map_add, map_mul, map_mul, map_add, ez1, ez2, er, map_sub, map_mul, map_one, e3, eφ]`. Simplify using `only [Submodule.coe_sub, Submodule.coe_smul, map_sub, LinearMap.sub_apply, hsmul1, hsmul2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cond_of_mem (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hvk : v ≤ k) {b : 𝓞 K}
    (hc : conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v)) (x y x' y' : ↥L)
    (hx : x' - b • x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (hy : y' - b • y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  have e3 : ∀ c : 𝓞 K, algebraMap (𝓞 K) K (conjO K c) = star (algebraMap (𝓞 K) K c) :=
    fun _ => rfl
  have eφ : ∀ a : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F) :=
    fun _ => rfl
  have hψ : ∀ a c : 𝓞 F, algebraMap F K ((a * c : 𝓞 F) : F) =
      algebraMap F K (a : F) * algebraMap F K (c : F) := fun a c => by
    rw [show ((a * c : 𝓞 F) : F) = (a : F) * (c : F) from rfl, map_mul]
  have hfix : ∀ a : 𝓞 F, star (algebraMap F K (a : F)) = algebraMap F K (a : F) :=
    fun a => (hF _).mpr ⟨_, rfl⟩
  have hsmul1 : ∀ (c : 𝓞 K) (u w : V), h (c • u) w = star (algebraMap (𝓞 K) K c) * h u w :=
    fun c u w => by rw [← algebraMap_smul K c u, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  have hsmul2 : ∀ (c : 𝓞 K) (u w : V), h u (c • w) = algebraMap (𝓞 K) K c * h u w :=
    fun c u w => by rw [← algebraMap_smul K c w, map_smul, smul_eq_mul]
  have hA : ∀ w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L), ∀ u : ↥L,
      (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (w : V) (u : V)) ∧
      (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V)) := by
    intro w hw u
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro c hc m _
      obtain ⟨r1, hr1⟩ := Submodule.mem_one.mp (hLi m m.2 u u.2)
      obtain ⟨r2, hr2⟩ := Submodule.mem_one.mp (hLi u u.2 m m.2)
      refine ⟨⟨conjO K c * r1, Ideal.mul_mem_right _ _ (conjO_mem_extP hF 𝔭 k hc), ?_⟩,
        ⟨c * r2, Ideal.mul_mem_right _ _ hc, ?_⟩⟩
      · rw [map_mul, e3, hr1, Submodule.coe_smul, hsmul1]
      · rw [map_mul, hr2, Submodule.coe_smul, hsmul2]
    · intro w1 w2 h1 h2
      obtain ⟨⟨z1, hz1, ez1⟩, ⟨z1', hz1', ez1'⟩⟩ := h1
      obtain ⟨⟨z2, hz2, ez2⟩, ⟨z2', hz2', ez2'⟩⟩ := h2
      refine ⟨⟨z1 + z2, add_mem hz1 hz2, ?_⟩, ⟨z1' + z2', add_mem hz1' hz2', ?_⟩⟩
      · rw [map_add, ez1, ez2, Submodule.coe_add, map_add, LinearMap.add_apply]
      · rw [map_add, ez1', ez2', Submodule.coe_add, map_add]
  have hB : ∀ u w : ↥L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ r ∈ extP K 𝔭 ^ v,
      algebraMap (𝓞 K) K r = algebraMap F K (t : F) * h (u : V) (w : V) := by
    intro u w
    obtain ⟨t1, ht1, a1, ha1⟩ := he.2.2 u u.2
    obtain ⟨t2, ht2, a2, ha2⟩ := he.2.2 w w.2
    refine ⟨t1 * t2, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht1 ht2,
      conjO K a1 * a2 * algebraMap (𝓞 F) (𝓞 K) n, Ideal.mul_mem_left _ _ (map_mem_extP hv), ?_⟩
    have h1 := congrArg₂ (fun p q => h p q) ha1 ha2
    simp only [hsmul1, hsmul2, hn, eφ, hfix] at h1
    rw [map_mul, map_mul, e3, eφ, hψ]
    linear_combination -h1
  obtain ⟨⟨z1, hz1, ez1⟩, -⟩ := hA (x' - b • x) hx y'
  obtain ⟨-, ⟨z2, hz2, ez2⟩⟩ := hA (y' - b • y) hy (b • x)
  obtain ⟨t, ht, r, hr, er⟩ := hB x y
  refine ⟨t, ht, algebraMap (𝓞 F) (𝓞 K) t * (z1 + z2) + (conjO K b * b - 1) * r, ?_, ?_⟩
  · refine add_mem (Ideal.mul_mem_left _ _ (add_mem hz1 hz2)) ?_
    have hpow : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - v) * extP K 𝔭 ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hvk]
    rw [hpow]
    exact Ideal.mul_mem_mul hc hr
  · rw [map_add, map_mul, map_mul, map_add, ez1, ez2, er, map_sub, map_mul, map_one, e3, eφ]
    simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, LinearMap.sub_apply, hsmul1, hsmul2]
    ring

/- English proof (translation)
Take `⟨t, ht, z, hz, hzeq⟩` from `H`. Establish `e1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F)` using `rfl`. Establish `e2 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F)` using `rfl`. Establish `e3 : algebraMap (𝓞 K) K (conjO K b) = star (algebraMap (𝓞 K) K b)` using `rfl`. Establish `hbe : h (b • e) (b • e) = star (algebraMap (𝓞 K) K b) * algebraMap (𝓞 K) K b * h e e`.

Rewrite using `[← algebraMap_smul K b e, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply, mul_assoc]`. Establish `hz' : z = algebraMap (𝓞 F) (𝓞 K) t * algebraMap (𝓞 F) (𝓞 K) n * (conjO K b * b - 1)`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[hzeq, hbe, hn, map_mul, map_mul, map_sub, map_mul, map_one, e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree.

Break down `le_or_gt k v with hkv | hvk` into its components or cases. Rewrite using `[Nat.sub_eq_zero_of_le hkv, pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`. Establish `hne : 𝔭 ≠ ⊥` using `ne_bot_of_isMaximal h𝔭`. Establish `hcop : ∀ I : Ideal (𝓞 F), ¬ I ≤ 𝔭 → 𝔭 ⊔ I = ⊤` using `fun I hI => by`.

Assume the negation of the conclusion as `hne'`. Conclude with `hI (le_sup_right.trans (h𝔭.eq_of_le hne' le_sup_left).ge)`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)`. Establish `hJp : ¬ J ≤ 𝔭`. Introduce `hle`.

Apply `hv'` to reduce the goal to its premises. Rewrite using `[← Ideal.span_singleton_le_iff_mem, hJ, pow_succ]`. Conclude with `Ideal.mul_mono_right hle`. Establish `htp : ¬ Ideal.span {t} ≤ 𝔭` using `fun hle => ht ((Ideal.span_singleton_le_iff_mem _).mp hle)`. Establish `hcopF : IsCoprime 𝔭 (Ideal.span {t} * J)` using `(Ideal.isCoprime_iff_sup_eq.mpr (hcop _ htp)).mul_right (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ hJp))`.

Establish `hX : IsCoprime (extP K 𝔭) ((Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)))`. Rewrite `hcopF`, the goal using `[Ideal.isCoprime_iff_sup_eq]`. Rewrite using `[extP, ← Ideal.map_sup, hcopF, Ideal.map_top]`. Establish `hspan : Ideal.span {z} = extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} * (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K))`. Establish `hn' : Ideal.span {algebraMap (𝓞 F) (𝓞 K) n} = Ideal.map (algebraMap (𝓞 F) (𝓞 K)) (𝔭 ^ v) * Ideal.map (algebraMap (𝓞 F) (𝓞 K)) J`.

Rewrite using `[← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton]`. Rewrite using `[hz', ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, Ideal.map_mul, extP, ← Ideal.map_pow, hn', Ideal.map_span, Set.image_singleton]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdvd : extP K 𝔭 ^ k ∣ extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} * (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K))`. Rewrite using `[← hspan]`.

Conclude with `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hz)`. Establish `hdvd2` using `(hX.pow_left (m := k)).dvd_of_dvd_mul_right hdvd`. Establish `hP0 : extP K 𝔭 ^ v ≠ 0`. Apply `pow_ne_zero` to reduce the goal to its premises. Rewrite using `[extP, Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]`.

Conclude with `hne`. Rewrite `hdvd2` using `[show k = v + (k - v) by omega, pow_add]`. Establish `h3` using `(mul_dvd_mul_iff_left hP0).mp hdvd2`. Conclude with `(Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp h3)`.
-/
theorem mem_of_cond (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : h e e = algebraMap F K (n : F)) {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hv' : n ∉ 𝔭 ^ (v + 1))
    {b : 𝓞 K} (H : CongrP 𝔭 k (h (b • e) (b • e)) (h e e)) :
    conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v) := by
  obtain ⟨t, ht, z, hz, hzeq⟩ := H
  have e1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
  have e2 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := rfl
  have e3 : algebraMap (𝓞 K) K (conjO K b) = star (algebraMap (𝓞 K) K b) := rfl
  have hbe : h (b • e) (b • e) = star (algebraMap (𝓞 K) K b) * algebraMap (𝓞 K) K b * h e e := by
    rw [← algebraMap_smul K b e, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_assoc]
  have hz' : z = algebraMap (𝓞 F) (𝓞 K) t * algebraMap (𝓞 F) (𝓞 K) n * (conjO K b * b - 1) := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hzeq, hbe, hn, map_mul, map_mul, map_sub, map_mul, map_one, e1, e2, e3]
    ring
  rcases le_or_gt k v with hkv | hvk
  · rw [Nat.sub_eq_zero_of_le hkv, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hne : 𝔭 ≠ ⊥ := ne_bot_of_isMaximal h𝔭
  have hcop : ∀ I : Ideal (𝓞 F), ¬ I ≤ 𝔭 → 𝔭 ⊔ I = ⊤ := fun I hI => by
    by_contra hne'
    exact hI (le_sup_right.trans (h𝔭.eq_of_le hne' le_sup_left).ge)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have hJp : ¬ J ≤ 𝔭 := by
    intro hle
    apply hv'
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_succ]
    exact Ideal.mul_mono_right hle
  have htp : ¬ Ideal.span {t} ≤ 𝔭 := fun hle => ht ((Ideal.span_singleton_le_iff_mem _).mp hle)
  have hcopF : IsCoprime 𝔭 (Ideal.span {t} * J) :=
    (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ htp)).mul_right (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ hJp))
  have hX : IsCoprime (extP K 𝔭) ((Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K))) := by
    rw [Ideal.isCoprime_iff_sup_eq] at hcopF ⊢
    rw [extP, ← Ideal.map_sup, hcopF, Ideal.map_top]
  have hspan : Ideal.span {z} = extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} *
      (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)) := by
    have hn' : Ideal.span {algebraMap (𝓞 F) (𝓞 K) n} =
        Ideal.map (algebraMap (𝓞 F) (𝓞 K)) (𝔭 ^ v) * Ideal.map (algebraMap (𝓞 F) (𝓞 K)) J := by
      rw [← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton]
    rw [hz', ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.map_mul, extP, ← Ideal.map_pow, hn', Ideal.map_span, Set.image_singleton]
    ring
  have hdvd : extP K 𝔭 ^ k ∣ extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} *
      (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [← hspan]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hz)
  have hdvd2 := (hX.pow_left (m := k)).dvd_of_dvd_mul_right hdvd
  have hP0 : extP K 𝔭 ^ v ≠ 0 := by
    apply pow_ne_zero
    rw [extP, Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact hne
  rw [show k = v + (k - v) by omega, pow_add] at hdvd2
  have h3 := (mul_dvd_mul_iff_left hP0).mp hdvd2
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp h3)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H`. Apply `mem_of_cond hF h𝔭 hn hv hv'` to reduce the goal to its premises. Establish `h1 : (Submodule.Quotient.mk (b • (⟨e, he.1⟩ : ↥L)) : Qk L 𝔭 k) = algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk ⟨e, he.1⟩)`. Rewrite using `[Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]`.

Conclude with `H _ _ _ _ h1 h1`. Introduce `hc x y x' y' hx hy`. Rewrite `hx`, `hy` using `[Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`. Conclude with `cond_of_mem hF hs hLi h𝔭 he hn hv hvk hc x y x' y' hx hy`.
-/
theorem cond_iff (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hv' : n ∉ 𝔭 ^ (v + 1)) (hvk : v ≤ k) (b : 𝓞 K) :
    (∀ x y x' y' : ↥L,
      (Submodule.Quotient.mk x' : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk x) →
      (Submodule.Quotient.mk y' : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) ↔
      conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v) := by
  constructor
  · intro H
    apply mem_of_cond hF h𝔭 hn hv hv'
    have h1 : (Submodule.Quotient.mk (b • (⟨e, he.1⟩ : ↥L)) : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk ⟨e, he.1⟩) := by
      rw [Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
    exact H _ _ _ _ h1 h1
  · intro hc x y x' y' hx hy
    rw [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hx hy
    exact cond_of_mem hF hs hLi h𝔭 he hn hv hvk hc x y x' y' hx hy

def NormOne (Q : Ideal (𝓞 K)) (z : 𝓞 K ⧸ Q) : Prop :=
  ∃ y : 𝓞 K, Ideal.Quotient.mk Q y = z ∧
    Ideal.Quotient.mk Q (conjO K y * y) = Ideal.Quotient.mk Q 1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h1⟩`. Rewrite `hy`, `h1` using `[Ideal.Quotient.eq]`. Establish `hyb : conjO K (y - b) ∈ extP K 𝔭 ^ j` using `conjO_mem_extP hF 𝔭 j hy`. Establish `e : conjO K b * b - 1 = (conjO K y * y - 1) - (conjO K y * (y - b) + conjO K (y - b) * b)`.

Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `sub_mem h1 (add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hyb))`. Introduce `h`.

Conclude with `⟨b, rfl, Ideal.Quotient.eq.mpr h⟩`.
-/
theorem normOne_mk_iff (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (j : ℕ) (b : 𝓞 K) :
    NormOne (extP K 𝔭 ^ j) (Ideal.Quotient.mk _ b) ↔ conjO K b * b - 1 ∈ extP K 𝔭 ^ j := by
  constructor
  · rintro ⟨y, hy, h1⟩
    rw [Ideal.Quotient.eq] at hy h1
    have hyb : conjO K (y - b) ∈ extP K 𝔭 ^ j := conjO_mem_extP hF 𝔭 j hy
    have e : conjO K b * b - 1 =
        (conjO K y * y - 1) - (conjO K y * (y - b) + conjO K (y - b) * b) := by
      rw [map_sub]
      ring
    rw [e]
    exact sub_mem h1 (add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hyb))
  · intro h
    exact ⟨b, rfl, Ideal.Quotient.eq.mpr h⟩

/- English proof (translation)
Unfold `normRepCount`. Use `Nat.card_congr ((Equiv.funUnique (Fin 1) (𝓞 K ⧸ Q)).symm.subtypeEquiv ?_)` and prove the remaining obligations. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, h1, h2⟩`.

Conclude with `⟨fun _ => y, fun i => by simpa using h1, by simpa using h2⟩`. Introduce and unpack `⟨y, h1, h2⟩`. Conclude with `⟨y 0, by simpa using h1 0, by simpa using h2⟩`.
-/
theorem card_normOne (Q : Ideal (𝓞 K)) :
    Nat.card {z : 𝓞 K ⧸ Q // NormOne Q z} = normRepCount K Q 1 1 := by
  unfold normRepCount
  refine Nat.card_congr ((Equiv.funUnique (Fin 1) (𝓞 K ⧸ Q)).symm.subtypeEquiv ?_)
  intro z
  constructor
  · rintro ⟨y, h1, h2⟩
    exact ⟨fun _ => y, fun i => by simpa using h1, by simpa using h2⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y 0, by simpa using h1 0, by simpa using h2⟩

end Formalism.HermitianLattices.Ext.L3.NormOneGroup
