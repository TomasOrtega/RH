import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmul

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Unfold `pK`. Rewrite using `[LocalSpans.mem_locF]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, z, hz, e⟩`.

Use `⟨t, ht, z, hz, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[Algebra.linearMap_apply]`. Rewrite using `[e, Algebra.smul_def, MeanB.algebraMap_comp]`. Introduce and unpack `⟨t, ht, z, hz, e⟩`. Conclude with `⟨t, ht, z, hz, by rw [Algebra.linearMap_apply, e, Algebra.smul_def, MeanB.algebraMap_comp]⟩`.
-/
theorem mem_pK {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {a : K} :
    a ∈ pK K 𝔭 k ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k,
      algebraMap (𝓞 K) K z = algebraMap F K (t : F) * a := by
  have := h𝔭.isPrime
  unfold pK
  rw [LocalSpans.mem_locF]
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    refine ⟨t, ht, z, hz, ?_⟩
    rw [Algebra.linearMap_apply] at e
    rw [e, Algebra.smul_def, MeanB.algebraMap_comp]
  · rintro ⟨t, ht, z, hz, e⟩
    exact ⟨t, ht, z, hz, by rw [Algebra.linearMap_apply, e, Algebra.smul_def, MeanB.algebraMap_comp]⟩

/- English proof (translation)
Conclude with `(mem_pK h𝔭).symm`.
-/
theorem congrP_algebraMap_iff_sub_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {a b : K} :
    CongrP 𝔭 k a b ↔ a - b ∈ pK K 𝔭 k := by
  exact (mem_pK h𝔭).symm

/- English proof (translation)
Unfold `pK`. Rewrite using `[pow_zero, Ideal.one_eq_top, Submodule.map_top, ← Submodule.one_eq_range]`.
-/
theorem locF_one_eq (𝔭 : Ideal (𝓞 F)) : locF 𝔭 (1 : Submodule (𝓞 K) K) = pK K 𝔭 0 := by
  unfold pK
  rw [pow_zero, Ideal.one_eq_top, Submodule.map_top, ← Submodule.one_eq_range]

/- English proof (translation)
The claim follows from `LocF.le_locF 𝔭 _ ⟨z, hz, rfl⟩`.
-/
theorem algebraMap_mem_pK' (𝔭 : Ideal (𝓞 F)) {k : ℕ} {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    algebraMap (𝓞 K) K z ∈ pK K 𝔭 k :=
  LocF.le_locF 𝔭 _ ⟨z, hz, rfl⟩

/- English proof (translation)
The claim follows from `algebraMap_mem_pK' 𝔭 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)`.
-/
theorem algebraMap_mem_pK (𝔭 : Ideal (𝓞 F)) (z : 𝓞 K) : algebraMap (𝓞 K) K z ∈ pK K 𝔭 0 :=
  algebraMap_mem_pK' 𝔭 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)

/- English proof (translation)
The claim follows from `LocF.locF_mono 𝔭 (Submodule.map_mono (Ideal.pow_le_pow_right hij))`.
-/
theorem pK_anti (𝔭 : Ideal (𝓞 F)) {i j : ℕ} (hij : i ≤ j) : pK K 𝔭 j ≤ pK K 𝔭 i :=
  LocF.locF_mono 𝔭 (Submodule.map_mono (Ideal.pow_le_pow_right hij))

/- English proof (translation)
Take `⟨t, ht, z, hz, e⟩` from `(mem_pK h𝔭).1 ha`. Take `⟨t', ht', z', hz', e'⟩` from `(mem_pK h𝔭).1 hb`. Use `(mem_pK h𝔭).2 ⟨t * t', fun h => (h𝔭.isPrime.mem_or_mem h).elim ht ht', z * z', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_mul hz hz'`.

Rewrite using `[map_mul, e, e', show ((t * t' : 𝓞 F) : F) = (t : F) * (t' : F) from rfl, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_pK {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {i j : ℕ} {a b : K} (ha : a ∈ pK K 𝔭 i)
    (hb : b ∈ pK K 𝔭 j) : a * b ∈ pK K 𝔭 (i + j) := by
  obtain ⟨t, ht, z, hz, e⟩ := (mem_pK h𝔭).1 ha
  obtain ⟨t', ht', z', hz', e'⟩ := (mem_pK h𝔭).1 hb
  refine (mem_pK h𝔭).2 ⟨t * t', fun h => (h𝔭.isPrime.mem_or_mem h).elim ht ht', z * z', ?_, ?_⟩
  · rw [pow_add]; exact Ideal.mul_mem_mul hz hz'
  · rw [map_mul, e, e', show ((t * t' : 𝓞 F) : F) = (t : F) * (t' : F) from rfl, map_mul]; ring

/- English proof (translation)
Take `⟨t, ht, z, hz, e⟩` from `(mem_pK h𝔭).1 ha`. Use `(mem_pK h𝔭).2 ⟨t, ht, conjO K z, idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k z hz, ?_⟩` and prove the remaining obligations. Establish `: algebraMap (𝓞 K) K (conjO K z) = star (algebraMap (𝓞 K) K z)` using `rfl`. Rewrite using `[this, e, star_mul', MeanB.star_algebraMap hF]`.
-/
theorem star_mem_pK (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {a : K}
    (ha : a ∈ pK K 𝔭 k) : star a ∈ pK K 𝔭 k := by
  obtain ⟨t, ht, z, hz, e⟩ := (mem_pK h𝔭).1 ha
  refine (mem_pK h𝔭).2 ⟨t, ht, conjO K z, idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k z hz, ?_⟩
  have : algebraMap (𝓞 K) K (conjO K z) = star (algebraMap (𝓞 K) K z) := rfl
  rw [this, e, star_mul', MeanB.star_algebraMap hF]

/- English proof (translation)
Establish `hbot : 𝔭 ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr h𝔭)`. Establish `hlt : 𝔭 ^ 2 < 𝔭` using `Ideal.pow_lt_self 𝔭 hbot h𝔭.ne_top 2 le_rfl`. Take `⟨π, hπ, hπ'⟩` from `SetLike.exists_of_lt hlt`.

Conclude with `⟨π, hπ, hπ'⟩`.
-/
theorem exists_unif {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ π : 𝓞 F, π ∈ 𝔭 ∧ π ∉ 𝔭 ^ 2 := by
  have hbot : 𝔭 ≠ ⊥ := by
    rintro rfl
    exact RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr h𝔭)
  have hlt : 𝔭 ^ 2 < 𝔭 := Ideal.pow_lt_self 𝔭 hbot h𝔭.ne_top 2 le_rfl
  obtain ⟨π, hπ, hπ'⟩ := SetLike.exists_of_lt hlt
  exact ⟨π, hπ, hπ'⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨𝔟, hb⟩ : 𝔭 ∣ Ideal.span {π} := by`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hπ`. Establish `hnb : ¬ 𝔟 ≤ 𝔭`. Introduce `hle`.

Apply `hπ'` to reduce the goal to its premises. Establish `: Ideal.span {π} ≤ 𝔭 ^ 2`. Rewrite using `[hb, sq]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `this (Ideal.mem_span_singleton_self π)`.

Take `⟨s, hs, hs'⟩` from `SetLike.not_le_iff_exists.mp hnb`. Use `⟨s ^ k, fun h => hs' (h𝔭.isPrime.mem_of_pow_mem k h), fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, hb, mul_pow, mul_comm (s ^ k)]`. Conclude with `Ideal.mul_mem_mul hx (Ideal.pow_mem_pow hs k)`.
-/
theorem exists_mul_dvd_unif {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (k : ℕ) : ∃ s : 𝓞 F, s ∉ 𝔭 ∧ ∀ x ∈ 𝔭 ^ k, π ^ k ∣ s * x := by
  obtain ⟨𝔟, hb⟩ : 𝔭 ∣ Ideal.span {π} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hπ
  have hnb : ¬ 𝔟 ≤ 𝔭 := by
    intro hle
    apply hπ'
    have : Ideal.span {π} ≤ 𝔭 ^ 2 := by
      rw [hb, sq]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp hnb
  refine ⟨s ^ k, fun h => hs' (h𝔭.isPrime.mem_of_pow_mem k h), fun x hx => ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, hb, mul_pow, mul_comm (s ^ k)]
  exact Ideal.mul_mem_mul hx (Ideal.pow_mem_pow hs k)

/- English proof (translation)
Establish `hc' : Ideal.span {c} ≠ (0 : Ideal (𝓞 F))` using `by simpa using hc`. Establish `hu : ¬ IsUnit 𝔭`. Rewrite using `[Ideal.isUnit_iff]`. Conclude with `h𝔭.ne_top`. Take `⟨𝔟, hb, hnd⟩` from `(FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd`.

Rewrite `hnd` using `[Ideal.dvd_iff_le]`. Take `⟨t, htb, htp⟩` from `SetLike.not_le_iff_exists.mp hnd`. Use `⟨multiplicity 𝔭 (Ideal.span {c}), t, htp, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.mem_span_singleton, hb, mul_comm t]`. Conclude with `Ideal.mul_mem_mul hx htb`.
-/
theorem exists_mul_dvd {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) :
    ∃ (r : ℕ) (u : 𝓞 F), u ∉ 𝔭 ∧ ∀ x ∈ 𝔭 ^ r, c ∣ u * x := by
  have hc' : Ideal.span {c} ≠ (0 : Ideal (𝓞 F)) := by simpa using hc
  have hu : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]; exact h𝔭.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.mp hnd
  refine ⟨multiplicity 𝔭 (Ideal.span {c}), t, htp, fun x hx => ?_⟩
  rw [← Ideal.mem_span_singleton, hb, mul_comm t]
  exact Ideal.mul_mem_mul hx htb

/- English proof (translation)
Establish `h0 : π ≠ 0` using `fun h => hπ' (h ▸ Submodule.zero_mem _)`. Rewrite using `[map_ne_zero]`. Conclude with `h0` after adjusting the coercions.
-/
theorem unif_ne_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ' : π ∉ 𝔭 ^ 2) :
    algebraMap F K (π : F) ≠ 0 := by
  have h0 : π ≠ 0 := fun h => hπ' (h ▸ Submodule.zero_mem _)
  rw [map_ne_zero]
  exact_mod_cast h0

/- English proof (translation)
Establish `h0 : t ≠ 0` using `fun h => ht (h ▸ Submodule.zero_mem _)`. Rewrite using `[map_ne_zero]`. Conclude with `h0` after adjusting the coercions.
-/
theorem notMem_ne_zero {𝔭 : Ideal (𝓞 F)} {t : 𝓞 F} (ht : t ∉ 𝔭) : algebraMap F K (t : F) ≠ 0 := by
  have h0 : t ≠ 0 := fun h => ht (h ▸ Submodule.zero_mem _)
  rw [map_ne_zero]
  exact_mod_cast h0

/- English proof (translation)
Establish `h1 : (ι π) ^ k ∈ extP K 𝔭 ^ k` using `Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hπ) k`. Establish `h2` using `algebraMap_mem_pK' (K := K) 𝔭 h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_pow]`. Use `congr 1`.
-/
theorem unif_pow_mem_pK {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ : π ∈ 𝔭) (k : ℕ) :
    algebraMap F K (π : F) ^ k ∈ pK K 𝔭 k := by
  have h1 : (ι π) ^ k ∈ extP K 𝔭 ^ k := Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hπ) k
  have h2 := algebraMap_mem_pK' (K := K) 𝔭 h1
  convert h2 using 1
  rw [map_pow]
  congr 1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Take `⟨t, ht, z, hz, e⟩` from `(mem_pK h𝔭).1 ha`. Take `⟨s, hs, hdvd⟩` from `exists_mul_dvd_unif h𝔭 hπ hπ' k`. Establish `h1 : Ideal.span {ι s} * extP K 𝔭 ^ k ≤ Ideal.span {ι (π ^ k)}`.

Establish `h2 : Ideal.span {s} * 𝔭 ^ k ≤ Ideal.span {π ^ k}`. Rewrite using `[Ideal.span_singleton_mul_le_iff]`. Introduce `x hx`. Conclude with `Ideal.mem_span_singleton.2 (hdvd x hx)`. Use `Ideal.map_mono (f := ι) h2` as an intermediate fact.

Rewrite `this` using `[Ideal.map_mul, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton, Ideal.map_pow]`. Then use the resulting hypothesis. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton.1 (h1 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz))`. Establish `hπ0` using `unif_ne_zero (K := K) hπ'`. Use `⟨a / algebraMap F K (π : F) ^ k, ?_, by field_simp⟩` and prove the remaining obligations. Use `(mem_pK h𝔭).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, w, by simp, ?_⟩` and prove the remaining obligations.

Establish `e2` using `congrArg (algebraMap (𝓞 K) K) hw`. Rewrite `e2` using `[map_mul, map_mul, e, MeanB.algebraMap_comp, MeanB.algebraMap_comp, show ((π ^ k : 𝓞 F) : F) = (π : F) ^ k from rfl, map_pow]`. Rewrite using `[show ((s * t : 𝓞 F) : F) = (s : F) * (t : F) from rfl, map_mul]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-e2`.

Introduce and unpack `⟨b, hb, rfl⟩`. Use `mul_mem_pK h𝔭 (unif_pow_mem_pK (K := K) hπ k) hb` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_pK_iff_unif {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (hπ' : π ∉ 𝔭 ^ 2)
    {k : ℕ} {a : K} :
    a ∈ pK K 𝔭 k ↔ ∃ b ∈ pK K 𝔭 0, a = algebraMap F K (π : F) ^ k * b := by
  constructor
  · intro ha
    obtain ⟨t, ht, z, hz, e⟩ := (mem_pK h𝔭).1 ha
    obtain ⟨s, hs, hdvd⟩ := exists_mul_dvd_unif h𝔭 hπ hπ' k
    have h1 : Ideal.span {ι s} * extP K 𝔭 ^ k ≤ Ideal.span {ι (π ^ k)} := by
      have h2 : Ideal.span {s} * 𝔭 ^ k ≤ Ideal.span {π ^ k} := by
        rw [Ideal.span_singleton_mul_le_iff]
        intro x hx
        exact Ideal.mem_span_singleton.2 (hdvd x hx)
      have := Ideal.map_mono (f := ι) h2
      rwa [Ideal.map_mul, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
        Ideal.map_pow] at this
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1
      (h1 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz))
    have hπ0 := unif_ne_zero (K := K) hπ'
    refine ⟨a / algebraMap F K (π : F) ^ k, ?_, by field_simp⟩
    refine (mem_pK h𝔭).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, w, by simp, ?_⟩
    have e2 := congrArg (algebraMap (𝓞 K) K) hw
    rw [map_mul, map_mul, e, MeanB.algebraMap_comp, MeanB.algebraMap_comp,
      show ((π ^ k : 𝓞 F) : F) = (π : F) ^ k from rfl, map_pow] at e2
    rw [show ((s * t : 𝓞 F) : F) = (s : F) * (t : F) from rfl, map_mul]
    field_simp
    linear_combination -e2
  · rintro ⟨b, hb, rfl⟩
    have := mul_mem_pK h𝔭 (unif_pow_mem_pK (K := K) hπ k) hb
    simpa using this

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Rewrite using `[← LocF.locF_idem 𝔭 A₀]`. Use `(LocalSpans.mem_locF 𝔭 _ _).2 ⟨t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K (ι t), MeanB.algebraMap_comp, smul_smul, mul_inv_cancel₀ (notMem_ne_zero ht), one_smul]`. Conclude with `hy`.
-/
theorem inv_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V) {t : 𝓞 F}
    (ht : t ∉ 𝔭) {y : V} (hy : y ∈ locF 𝔭 A₀) : (algebraMap F K (t : F))⁻¹ • y ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  rw [← LocF.locF_idem 𝔭 A₀]
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t, ht, ?_⟩
  rw [← algebraMap_smul K (ι t), MeanB.algebraMap_comp, smul_smul,
    mul_inv_cancel₀ (notMem_ne_zero ht), one_smul]
  exact hy

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.smul_induction_on' with`. Consider the case `smul z hz y hy`. Take `⟨b, hb, e⟩` from `(mem_pK_iff_unif h𝔭 hπ hπ').1 (algebraMap_mem_pK' (K := K) 𝔭 hz)`.

Take `⟨t, ht, w, -, e'⟩` from `(mem_pK h𝔭).1 hb`. Use `⟨(algebraMap F K (t : F))⁻¹ • (w • y), inv_smul_mem h𝔭 A₀ ht ((locF 𝔭 A₀).smul_mem w hy), ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K z, ← algebraMap_smul K w, e, e', smul_smul, smul_smul]`. Use `congr 1`. Use `notMem_ne_zero (K := K) ht` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Consider the case `add x _ y _ hx hy`. Take `⟨x', hx', rfl⟩` from `hx`. Take `⟨y', hy', rfl⟩` from `hy`. Conclude with `⟨x' + y', (locF 𝔭 A₀).add_mem hx' hy', (smul_add _ _ _).symm⟩`.

Introduce and unpack `⟨y, hy, rfl⟩`. Use `Submodule.smul_mem_smul (localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_mem_pow hπ k)) hy` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul K (ι (π ^ k)), MeanB.algebraMap_comp, show ((π ^ k : 𝓞 F) : F) = (π : F) ^ k from rfl, map_pow]`. Then use the resulting hypothesis.
-/
theorem mem_smul_iff_unif {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (A₀ : Submodule (𝓞 K) V) {k : ℕ} {x : V} :
    x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀ ↔ ∃ y ∈ locF 𝔭 A₀, x = algebraMap F K (π : F) ^ k • y := by
  constructor
  · intro hx
    induction hx using Submodule.smul_induction_on' with
    | smul z hz y hy =>
      obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 (algebraMap_mem_pK' (K := K) 𝔭 hz)
      obtain ⟨t, ht, w, -, e'⟩ := (mem_pK h𝔭).1 hb
      refine ⟨(algebraMap F K (t : F))⁻¹ • (w • y), inv_smul_mem h𝔭 A₀ ht ((locF 𝔭 A₀).smul_mem w hy), ?_⟩
      rw [← algebraMap_smul K z, ← algebraMap_smul K w, e, e', smul_smul, smul_smul]
      congr 1
      have := notMem_ne_zero (K := K) ht
      field_simp
    | add x _ y _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', (locF 𝔭 A₀).add_mem hx' hy', (smul_add _ _ _).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have := Submodule.smul_mem_smul (localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_mem_pow hπ k)) hy
    rwa [← algebraMap_smul K (ι (π ^ k)), MeanB.algebraMap_comp,
      show ((π ^ k : 𝓞 F) : F) = (π : F) ^ k from rfl, map_pow] at this

/- English proof (translation)
Rewrite using `[pow_zero, Ideal.one_eq_top, Submodule.top_smul]`.
-/
theorem pow_zero_smul (𝔭 : Ideal (𝓞 F)) (A : Submodule (𝓞 K) V) : extP K 𝔭 ^ 0 • A = A := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

/- English proof (translation)
The claim follows from `Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)`.
-/
theorem smul_anti (𝔭 : Ideal (𝓞 F)) (A : Submodule (𝓞 K) V) {i j : ℕ} (hij : i ≤ j) :
    extP K 𝔭 ^ j • A ≤ extP K 𝔭 ^ i • A :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)

/- English proof (translation)
Take `⟨t, ht, w, -, e'⟩` from `(mem_pK h𝔭).1 ha`. Use `inv_smul_mem h𝔭 A₀ ht ((locF 𝔭 A₀).smul_mem w hx)` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul K w, e', smul_smul, ← mul_assoc, inv_mul_cancel₀ (notMem_ne_zero ht), one_mul]`. Conclude with `this`.
-/
theorem smul_mem_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V)
    {a : K} {x : V} (ha : a ∈ pK K 𝔭 0) (hx : x ∈ locF 𝔭 A₀) : a • x ∈ locF 𝔭 A₀ := by
  obtain ⟨t, ht, w, -, e'⟩ := (mem_pK h𝔭).1 ha
  have := inv_smul_mem h𝔭 A₀ ht ((locF 𝔭 A₀).smul_mem w hx)
  rw [← algebraMap_smul K w, e', smul_smul, ← mul_assoc, inv_mul_cancel₀ (notMem_ne_zero ht),
    one_mul] at this
  exact this

/- English proof (translation)
Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`. Take `⟨b, hb, rfl⟩` from `(mem_pK_iff_unif h𝔭 hπ hπ').1 ha`. Take `⟨y, hy, rfl⟩` from `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx`. Use `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨b • y, smul_mem_locF h𝔭 A₀ hb hy, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, pow_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_mem_smul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V) {i j : ℕ}
    {a : K} {x : V} (ha : a ∈ pK K 𝔭 i) (hx : x ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    a • x ∈ extP K 𝔭 ^ (i + j) • locF 𝔭 A₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨b, hb, rfl⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 ha
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨b • y, smul_mem_locF h𝔭 A₀ hb hy, ?_⟩
  rw [smul_smul, smul_smul, pow_add]
  congr 1; ring

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`. Take `⟨x', hx', rfl⟩` from `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx`. Take `⟨y', hy', rfl⟩` from `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hy`. Take `⟨t, ht, hx''⟩` from `(LocalSpans.mem_locF 𝔭 A₀ x').1 hx'`.

Take `⟨s, hs, hy''⟩` from `(LocalSpans.mem_locF 𝔭 A₀ y').1 hy'`. Establish `h0 : h x' y' ∈ pK K 𝔭 0`. Take `⟨w, hw⟩` from `hA₀i _ hx'' _ hy''`. Use `(mem_pK h𝔭).2 ⟨t * s, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht hs, w, by simp, ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[localizedQuotients.form_smul hF, MeanB.algebraMap_comp]`.

Rewrite using `[← hw]`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Rewrite using `[map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply, star_pow, MeanB.star_algebraMap hF, ← mul_assoc, ← pow_add, add_comm j i]`. Conclude with `(mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨_, h0, rfl⟩`.
-/
theorem form_mem_pK (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {i j : ℕ} {x y : V}
    (hx : x ∈ extP K 𝔭 ^ i • locF 𝔭 A₀) (hy : y ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    h x y ∈ pK K 𝔭 (i + j) := by
  have := h𝔭.isPrime
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨x', hx', rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  obtain ⟨y', hy', rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hy
  obtain ⟨t, ht, hx''⟩ := (LocalSpans.mem_locF 𝔭 A₀ x').1 hx'
  obtain ⟨s, hs, hy''⟩ := (LocalSpans.mem_locF 𝔭 A₀ y').1 hy'
  have h0 : h x' y' ∈ pK K 𝔭 0 := by
    obtain ⟨w, hw⟩ := hA₀i _ hx'' _ hy''
    refine (mem_pK h𝔭).2 ⟨t * s, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht hs, w, by simp, ?_⟩
    rw [localizedQuotients.form_smul hF, MeanB.algebraMap_comp] at hw
    rw [← hw]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
    star_pow, MeanB.star_algebraMap hF, ← mul_assoc, ← pow_add, add_comm j i]
  exact (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨_, h0, rfl⟩

end Formalism.HermitianLattices.Ext.L3.D2
