import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdelePoisson

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Establish `hint : ∀ r : 𝓞 K, algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K r) ∈ integralFiniteAdeles (𝓞 K) K` using `fun r v ↦ coe_algebraMap_mem_adicCompletionIntegers v r`. Set `U : {d : 𝓞 K // d ≠ 0} → Set 𝔸ᶠ[K]` to `fun d ↦ {s | algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1) * s ∈ integralFiniteAdeles (𝓞 K) K}`. Establish `hUo : ∀ d, IsOpen (U d)` using `fun d ↦ isOpen_integralFiniteAdeles.preimage (continuous_const_mul _)`. Establish `hsU : S ⊆ ⋃ d, U d`. Introduce `s _`.

Take `⟨k, hk⟩` from `exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) s`. Take `⟨n, m, hm, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) k`. Establish `hm0 : m ≠ 0` using `nonZeroDivisors.ne_zero hm`. Establish `hmK : algebraMap (𝓞 K) K m ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hm0`. Use `Set.mem_iUnion.mpr ⟨⟨m, hm0⟩, ?_⟩` and prove the remaining obligations.

Establish `h : algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s = algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n) + algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * (s - algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m))`. Rewrite using `[mul_sub, ← map_mul, mul_div_cancel₀ _ hmK]`. Expand and normalize the polynomial expressions, which then agree. Use `show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s ∈ integralFiniteAdeles (𝓞 K) K`. Rewrite using `[h]`.

Conclude with `add_mem (hint n) (mul_mem (hint m) hk)`. Establish `hdU : Directed (· ⊆ ·) U`. Introduce `d e`. Use `⟨⟨d.1 * e.1, mul_ne_zero d.2 e.2⟩, fun s hs ↦ ?_, fun s hs ↦ ?_⟩` and prove the remaining obligations. Use `mul_mem (hint e.1) hs show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K` as an intermediate fact.

Rewrite using `[map_mul, map_mul, mul_comm (algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1)), mul_assoc]` and apply the resulting hypothesis. Use `mul_mem (hint d.1) hs show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K` as an intermediate fact. Rewrite using `[map_mul, map_mul, mul_assoc]` and apply the resulting hypothesis. Establish `: Nonempty {d : 𝓞 K // d ≠ 0}` using `⟨⟨1, one_ne_zero⟩⟩`. Take `⟨d, hd⟩` from `hS.elim_directed_cover U hUo hsU hdU`.

Conclude with `⟨d.1, d.2, fun s hs ↦ hd hs⟩`.
-/
theorem exists_mul_mem_integralFiniteAdeles_of_isCompact {S : Set 𝔸ᶠ[K]} (hS : IsCompact S) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ s ∈ S,
      algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d) * s ∈ integralFiniteAdeles (𝓞 K) K := by
  have hint : ∀ r : 𝓞 K,
      algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K r) ∈ integralFiniteAdeles (𝓞 K) K :=
    fun r v ↦ coe_algebraMap_mem_adicCompletionIntegers v r
  let U : {d : 𝓞 K // d ≠ 0} → Set 𝔸ᶠ[K] := fun d ↦
    {s | algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1) * s ∈ integralFiniteAdeles (𝓞 K) K}
  have hUo : ∀ d, IsOpen (U d) := fun d ↦
    isOpen_integralFiniteAdeles.preimage (continuous_const_mul _)
  have hsU : S ⊆ ⋃ d, U d := by
    intro s _
    obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) s
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hmK : algebraMap (𝓞 K) K m ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hm0
    refine Set.mem_iUnion.mpr ⟨⟨m, hm0⟩, ?_⟩
    have h : algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s =
        algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n) + algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) *
          (s - algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m)) := by
      rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hmK]
      ring
    show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s ∈ integralFiniteAdeles (𝓞 K) K
    rw [h]
    exact add_mem (hint n) (mul_mem (hint m) hk)
  have hdU : Directed (· ⊆ ·) U := by
    intro d e
    refine ⟨⟨d.1 * e.1, mul_ne_zero d.2 e.2⟩, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · have := mul_mem (hint e.1) hs
      show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K
      rwa [map_mul, map_mul, mul_comm (algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1)), mul_assoc]
    · have := mul_mem (hint d.1) hs
      show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K
      rwa [map_mul, map_mul, mul_assoc]
  have : Nonempty {d : 𝓞 K // d ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨d, hd⟩ := hS.elim_directed_cover U hUo hsU hdU
  exact ⟨d.1, d.2, fun s hs ↦ hd hs⟩

/- English proof (translation)
Use `set e := idealLatticeEquiv J`. Set `g : idealLattice K J → K` to `fun α ↦ ((e.symm α : _) : K)`. Establish `hinj : Function.Injective g` using `fun α β hαβ ↦ e.symm.injective (Subtype.ext hαβ)`. Establish `hsupp : ∀ ξ ∉ Set.range g, (if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0) = 0`. Introduce `ξ hξ`.

Rewrite using `[if_neg]`. Introduce `hm`. Conclude with `hξ ⟨e ⟨ξ, hm⟩, by simp [g]⟩`. Rewrite using `[← hinj.summable_iff hsupp]`. Use `hh using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `α`. Simplify using `only [Function.comp_apply, g]`. Rewrite using `[if_pos (show ((e.symm α : _) : K) ∈ (J : FractionalIdeal (𝓞 K)⁰ K) from (e.symm α).2)]`. Establish `he` using `coe_idealLatticeEquiv J (e.symm α)`. Rewrite `he` using `[Equiv.apply_symm_apply]`.

Rewrite using `[he]`.
-/
theorem summable_ite_mem_of_summable_idealLattice (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {h : mixedSpace K → ℝ} (hh : Summable fun α : idealLattice K J ↦ h α) :
    Summable fun ξ : K ↦
      if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0 := by
  set e := idealLatticeEquiv J
  let g : idealLattice K J → K := fun α ↦ ((e.symm α : _) : K)
  have hinj : Function.Injective g := fun α β hαβ ↦ e.symm.injective (Subtype.ext hαβ)
  have hsupp : ∀ ξ ∉ Set.range g,
      (if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0) = 0 := by
    intro ξ hξ
    rw [if_neg]
    intro hm
    exact hξ ⟨e ⟨ξ, hm⟩, by simp [g]⟩
  rw [← hinj.summable_iff hsupp]
  convert hh using 1
  funext α
  simp only [Function.comp_apply, g]
  rw [if_pos (show ((e.symm α : _) : K) ∈ (J : FractionalIdeal (𝓞 K)⁰ K) from (e.symm α).2)]
  have he := coe_idealLatticeEquiv J (e.symm α)
  rw [Equiv.apply_symm_apply] at he
  rw [he]

/- English proof (translation)
Establish `hs` using `ZLattice.summable_norm_pow_inv (L := idealLattice K J) (Module.finrank ℤ (idealLattice K J) + 1) (by omega)`. Use `Summable.of_norm_bounded_eventually hs ?_` and prove the remaining obligations. Use `filter_upwards [(Set.finite_singleton (0 : idealLattice K J)).compl_mem_cofinite] with ℓ hℓ`. Establish `hpos : 0 < ‖ℓ‖` using `norm_pos_iff.mpr hℓ`. Rewrite using `[Real.norm_of_nonneg (by positivity), inv_pow]`.

Use `gcongr`. Express the relevant statement in the definitionally equal form `‖ℓ‖ ≤ 1 + ‖ℓ‖`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem summable_inv_one_add_norm_pow_idealLattice (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun α : idealLattice K J ↦
      ((1 + ‖(α : mixedSpace K)‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹ := by
  have hs := ZLattice.summable_norm_pow_inv (L := idealLattice K J)
    (Module.finrank ℤ (idealLattice K J) + 1) (by omega)
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : idealLattice K J)).compl_mem_cofinite] with ℓ hℓ
  have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  rw [Real.norm_of_nonneg (by positivity), inv_pow]
  gcongr
  change ‖ℓ‖ ≤ 1 + ‖ℓ‖
  linarith

/- English proof (translation)
Use `set S : Set 𝔸ᶠ[K] := (fun p : IdeleGroup K × 𝔸ᶠ[K] ↦ ((IdeleGroup.toFinite K p.1⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * p.2) '' (C ×ˢ (b +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])))`. Establish `hS : IsCompact S` using `(hC.prod ((isCompact_idealFiniteAdeles I).vadd b)).image ((Units.continuous_val.comp ((IdeleGroup.continuous_toFinite (K := K)).comp (continuous_inv.comp continuous_fst))).mul continuous_snd)`. Take `⟨d, hd0, hd⟩` from `exists_mul_mem_integralFiniteAdeles_of_isCompact hS`. Use `set dK := algebraMap (𝓞 K) K d`. Establish `hdK : dK ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0`.

Use `set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹) ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK))`. Establish `hJ : ∀ a ∈ C, ∀ ξ : K, ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈ idealFiniteAdeles I → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K)`. Introduce `a ha ξ hξ`. Establish `hmem : algebraMap K 𝔸ᶠ[K] ξ ∈ S`. Use `⟨(a, ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ), ⟨ha, mem_vadd_idealFiniteAdeles.mpr hξ⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_inv, Units.inv_mul_cancel_left]`. Establish `h1` using `hd _ hmem`. Rewrite `h1` using `[← map_mul]`. Establish `h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)`. Rewrite using `[← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]`.

Conclude with `h1`. Rewrite `h2` using `[Units.val_one]`. Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).mp h2`. Use `(FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]`.

Use `set k := Module.finrank ℤ (idealLattice K J) + 1`. Take `⟨A, hA, hφ⟩` from `exists_norm_le_inv_one_add_pow φ k`. Establish `hcont : Continuous fun a : IdeleGroup K ↦ ‖homeomorphMixedSpace K ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖` using `continuous_norm.comp ((homeomorphMixedSpace K).continuous.comp (Units.continuous_val.comp ((IdeleGroup.continuous_toInfinite (K := K)).comp continuous_inv)))`. Take `⟨B, hB⟩` from `hC.exists_bound_of_continuousOn hcont.continuousOn`. Use `set B' := max B 1`.

Establish `hB'1 : 1 ≤ B'` using `le_max_right _ _`. Establish `hB'0 : 0 < B'` using `zero_lt_one.trans_le hB'1`. Use `⟨fun ξ ↦ if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then A * B' ^ k * ((1 + ‖mixedEmbedding K ξ‖) ^ k)⁻¹ else 0, ?_, ?_⟩` and prove the remaining obligations. Conclude with `summable_ite_mem_of_summable_idealLattice J (h := fun x ↦ A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹) ((summable_inv_one_add_norm_pow_idealLattice J).mul_left (A * B' ^ k))`. Introduce `a ha ξ`.

Use `set c := homeomorphMixedSpace K ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)`. Use `set c' := homeomorphMixedSpace K ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)`. Establish `hcc : c' * c = 1`. Rewrite using `[← homeomorphMixedSpace_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, homeomorphMixedSpace_apply, map_one]`. Establish `hval : schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ) = φ (c * mixedEmbedding K ξ) * cosetIndicator I b (((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ)`.

Establish `h1 : (a • algebraMap K 𝔸[K] ξ).1 = ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * algebraMap K (InfiniteAdeleRing K) ξ` using `rfl`. Establish `h2 : (a • algebraMap K 𝔸[K] ξ).2 = ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ` using `rfl`. Simplify using `only [schwartzBruhatTensor]`. Rewrite using `[h1, h2, homeomorphMixedSpace_mul, homeomorphMixedSpace_algebraMap]`. Rewrite using `[hval, cosetIndicator_apply]`.

Use `beta_reduce`. Use `split_ifs with hm hJm hJm`. Rewrite using `[mul_one] set x := mixedEmbedding K ξ`. Establish `hx : ‖x‖ ≤ B' * ‖c * x‖`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `((norm_norm _).symm.trans_le (hB a ha)).trans (le_max_left _ _)`. Establish `key : 1 + ‖x‖ ≤ B' * (1 + ‖c * x‖)` using `by nlinarith [norm_nonneg (c * x)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, mul_inv, ← mul_assoc (B' ^ k), mul_inv_cancel₀ (by positivity), one_mul]`. Use `_ ≤ A * (B' ^ k * ((1 + ‖x‖) ^ k)⁻¹) := by gcongr`.

Use `_ = A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹ := by ring`. Conclude with `absurd (hJ a ha ξ hm) hJm`. Rewrite using `[mul_zero, norm_zero]`. Check the signs of the components of the expression. Rewrite using `[mul_zero, norm_zero]`.
-/
theorem exists_summable_bound_tensor_cosetIndicator (φ : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]) {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K,
      ‖schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by

  set S : Set 𝔸ᶠ[K] := (fun p : IdeleGroup K × 𝔸ᶠ[K] ↦
      ((IdeleGroup.toFinite K p.1⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * p.2) ''
    (C ×ˢ (b +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])))
  have hS : IsCompact S := (hC.prod ((isCompact_idealFiniteAdeles I).vadd b)).image
    ((Units.continuous_val.comp ((IdeleGroup.continuous_toFinite (K := K)).comp
      (continuous_inv.comp continuous_fst))).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK))
  have hJ : ∀ a ∈ C, ∀ ξ : K,
      ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈
        idealFiniteAdeles I → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a ha ξ hξ
    have hmem : algebraMap K 𝔸ᶠ[K] ξ ∈ S := by
      refine ⟨(a, ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ),
        ⟨ha, mem_vadd_idealFiniteAdeles.mpr hξ⟩, ?_⟩
      simp only [map_inv, Units.inv_mul_cancel_left]
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

  set k := Module.finrank ℤ (idealLattice K J) + 1
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ k
  have hcont : Continuous fun a : IdeleGroup K ↦ ‖homeomorphMixedSpace K
      ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ :=
    continuous_norm.comp ((homeomorphMixedSpace K).continuous.comp (Units.continuous_val.comp
      ((IdeleGroup.continuous_toInfinite (K := K)).comp continuous_inv)))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  refine ⟨fun ξ ↦ if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then
      A * B' ^ k * ((1 + ‖mixedEmbedding K ξ‖) ^ k)⁻¹ else 0, ?_, ?_⟩
  · exact summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹)
      ((summable_inv_one_add_norm_pow_idealLattice J).mul_left (A * B' ^ k))
  intro a ha ξ
  set c := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  set c' := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  have hcc : c' * c = 1 := by
    rw [← homeomorphMixedSpace_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, homeomorphMixedSpace_apply, map_one]
  have hval : schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ) =
      φ (c * mixedEmbedding K ξ) * cosetIndicator I b
        (((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ) := by
    have h1 : (a • algebraMap K 𝔸[K] ξ).1 = ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) * algebraMap K (InfiniteAdeleRing K) ξ := rfl
    have h2 : (a • algebraMap K 𝔸[K] ξ).2 =
        ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ := rfl
    simp only [schwartzBruhatTensor]
    rw [h1, h2, homeomorphMixedSpace_mul, homeomorphMixedSpace_algebraMap]
  rw [hval, cosetIndicator_apply]
  beta_reduce
  split_ifs with hm hJm hJm
  · rw [mul_one]
    set x := mixedEmbedding K ξ
    have hx : ‖x‖ ≤ B' * ‖c * x‖ := by
      calc ‖x‖ = ‖c' * (c * x)‖ := by rw [← mul_assoc, hcc, one_mul]
        _ ≤ ‖c'‖ * ‖c * x‖ := norm_mul_le _ _
        _ ≤ B' * ‖c * x‖ := by
          gcongr
          exact ((norm_norm _).symm.trans_le (hB a ha)).trans (le_max_left _ _)
    have key : 1 + ‖x‖ ≤ B' * (1 + ‖c * x‖) := by nlinarith [norm_nonneg (c * x)]
    calc ‖φ (c * x)‖ ≤ A * ((1 + ‖c * x‖) ^ k)⁻¹ := hφ _
      _ = A * (B' ^ k * ((B' * (1 + ‖c * x‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc (B' ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ A * (B' ^ k * ((1 + ‖x‖) ^ k)⁻¹) := by gcongr
      _ = A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹ := by ring
  · exact absurd (hJ a ha ξ hm) hJm
  · rw [mul_zero, norm_zero]
    positivity
  · rw [mul_zero, norm_zero]

/- English proof (translation)
Establish `hF'` using `schwartzBruhat_le_span_cosetIndicator hF`. Use `clear hF`. Proceed by induction on `hF' using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨φ, I, b, rfl⟩` from `hG`.

Conclude with `exists_summable_bound_tensor_cosetIndicator φ I b hC`. Consider the case `zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩`. Consider the case `add G H _ _ hG hH`. Take `⟨u, hu, hGu⟩` from `hG`. Take `⟨w, hw, hHw⟩` from `hH`.

Conclude with `⟨u + w, hu.add hw, fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩`. Consider the case `smul r G _ hG`. Take `⟨u, hu, hGu⟩` from `hG`. Use `⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)`.
-/
theorem exists_summable_bound_smul_algebraMap {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K, ‖F (a • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by
  have hF' := schwartzBruhat_le_span_cosetIndicator hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_summable_bound_tensor_cosetIndicator φ I b hC
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨w, hw, hHw⟩ := hH
    exact ⟨u + w, hu.add hw, fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩
  | smul r G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)

/- English proof (translation)
Take `⟨u, hu, hFu⟩` from `exists_summable_bound_smul_algebraMap hF hC`. Conclude with `tendstoUniformlyOn_tsum hu fun ξ a ha ↦ hFu a ha ξ`.
-/
theorem tendstoUniformlyOn_tsum_smul_algebraMap {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun (s : Finset K) (a : IdeleGroup K) ↦ ∑ ξ ∈ s, F (a • algebraMap K 𝔸[K] ξ))
      (fun a ↦ ∑' ξ : K, F (a • algebraMap K 𝔸[K] ξ)) atTop C := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_smul_algebraMap hF hC
  exact tendstoUniformlyOn_tsum hu fun ξ a ha ↦ hFu a ha ξ

/- English proof (translation)
Take `⟨u, hu, hFu⟩` from `exists_summable_bound_smul_algebraMap (adelicFourier_mem_schwartzBruhat hF) hC.inv`. Conclude with `⟨u, hu, fun a ha ξ ↦ hFu a⁻¹ (Set.inv_mem_inv.mpr ha) ξ⟩`.
-/
theorem exists_summable_bound_adelicFourier_inv_smul_algebraMap {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K,
      ‖adelicFourier K F (a⁻¹ • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_smul_algebraMap
    (adelicFourier_mem_schwartzBruhat hF) hC.inv
  exact ⟨u, hu, fun a ha ξ ↦ hFu a⁻¹ (Set.inv_mem_inv.mpr ha) ξ⟩

/- English proof (translation)
Take `⟨u, hu, hFu⟩` from `exists_summable_bound_adelicFourier_inv_smul_algebraMap hF hC`. Conclude with `tendstoUniformlyOn_tsum hu fun ξ a ha ↦ hFu a ha ξ`.
-/
theorem tendstoUniformlyOn_tsum_adelicFourier_inv_smul_algebraMap {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun (s : Finset K) (a : IdeleGroup K) ↦
        ∑ ξ ∈ s, adelicFourier K F (a⁻¹ • algebraMap K 𝔸[K] ξ))
      (fun a ↦ ∑' ξ : K, adelicFourier K F (a⁻¹ • algebraMap K 𝔸[K] ξ)) atTop C := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_adelicFourier_inv_smul_algebraMap hF hC
  exact tendstoUniformlyOn_tsum hu fun ξ a ha ↦ hFu a ha ξ

end

end GroundTheory.Global
