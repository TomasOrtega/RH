import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := C) k`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hint : IsIntegral T b` using `Algebra.IsIntegral.isIntegral b`. Establish `h` using `Ideal.comap_ne_bot_of_integral_mem (R := T) (I := Ideal.span {b}) hb0 (Ideal.mem_span_singleton_self b) hint`. Take `⟨t, ht, ht0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`.

Rewrite `ht` using `[Ideal.mem_comap, Ideal.mem_span_singleton]`. Take `⟨d, hd⟩` from `ht`. Use `⟨t, ht0, d * a, ?_⟩` and prove the remaining obligations. Establish `hbK : algebraMap C K b ≠ 0`. Simplify using `using hb0`.

Rewrite using `[IsScalarTower.algebraMap_apply T C K, hd, map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_base_denominator_of_finite {T C K : Type} [CommRing T] [IsDomain T] [CommRing C]
    [IsDomain C] [Field K] [Algebra T C] [Algebra C K] [IsFractionRing C K] [Algebra T K]
    [IsScalarTower T C K] [Module.Finite T C] (k : K) :
    ∃ t : T, t ≠ 0 ∧ ∃ c : C, algebraMap T K t * k = algebraMap C K c := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hint : IsIntegral T b := Algebra.IsIntegral.isIntegral b
  have h := Ideal.comap_ne_bot_of_integral_mem (R := T) (I := Ideal.span {b}) hb0
    (Ideal.mem_span_singleton_self b) hint
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at ht
  obtain ⟨d, hd⟩ := ht
  refine ⟨t, ht0, d * a, ?_⟩
  have hbK : algebraMap C K b ≠ 0 := by
    simpa using hb0
  rw [IsScalarTower.algebraMap_apply T C K, hd, map_mul, map_mul]
  field_simp

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := T) (M := C)`. Use `⟨⟨s.image (algebraMap C K), ?_⟩⟩` and prove the remaining obligations. Establish `key : ∀ c : C, algebraMap C K c ∈ Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K)`. Introduce `c`. Establish `hc : c ∈ Submodule.span T (s : Set C)` using `hs ▸ Submodule.mem_top`.

Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx)))`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[eq_top_iff]`. Introduce `k _`.

Take `⟨t, ht, c, hc⟩` from `exists_base_denominator_of_finite (T := T) (C := C) k`. Establish `htF : algebraMap T F t ≠ 0` using `by simpa using ht`. Establish `: k = (algebraMap T F t)⁻¹ • algebraMap C K c`. Rewrite using `[← hc, IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def, inv_smul_smul₀ htF]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (key c)`.
-/
theorem finite_fractionRing_of_finite (T C F K : Type) [CommRing T] [IsDomain T] [CommRing C]
    [IsDomain C] [Field F] [Field K] [Algebra T C] [Algebra T F] [IsFractionRing T F]
    [Algebra C K] [IsFractionRing C K] [Algebra T K] [Algebra F K]
    [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C] : Module.Finite F K := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T) (M := C)
  refine ⟨⟨s.image (algebraMap C K), ?_⟩⟩
  have key : ∀ c : C, algebraMap C K c ∈
      Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) := by
    intro c
    have hc : c ∈ Submodule.span T (s : Set C) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx)))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro k _
  obtain ⟨t, ht, c, hc⟩ := exists_base_denominator_of_finite (T := T) (C := C) k
  have htF : algebraMap T F t ≠ 0 := by simpa using ht
  have : k = (algebraMap T F t)⁻¹ • algebraMap C K c := by
    rw [← hc, IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def, inv_smul_smul₀ htF]
  rw [this]
  exact Submodule.smul_mem _ _ (key c)

/- English proof (translation)
Establish `hTU : ∀ t : T, t ≠ 0 → algebraMap T U t ≠ 0`. Introduce `t ht h0`. Establish `h1 : algebraMap T L t = 0`. Rewrite using `[IsScalarTower.algebraMap_apply T U L, h0, map_zero]`. Rewrite `h1` using `[IsScalarTower.algebraMap_apply T F L]`.

Apply `ht` to reduce the goal to its premises. Simplify using `using h1`. Establish `den : ∀ ω : L ⊗[F] K, ∃ u : U, u ≠ 0 ∧ ∃ s', φ (u ⊗ₜ 1) * ω = φ s'`. Introduce `ω`. Proceed by induction on `ω using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨1, one_ne_zero, 0, by simp⟩`. Consider the case `tmul l k`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := U) l`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbL : algebraMap U L b ≠ 0` using `by simpa using hb0`.

Take `⟨t, ht, c, hc⟩` from `exists_base_denominator_of_finite (T := T) (C := C) k`. Use `⟨algebraMap T U t * b, mul_ne_zero (hTU t ht) hb0, a ⊗ₜ c, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, hφ, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hc, IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def (algebraMap T F t) k, ← TensorProduct.smul_tmul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply T F L, map_mul, ← IsScalarTower.algebraMap_apply T U …`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Consider the case `add x y hx hy`. Take `⟨u, hu, s₁, h₁⟩` from `hx`. Take `⟨v, hv, s₂, h₂⟩` from `hy`. Use `⟨u * v, mul_ne_zero hu hv, (v ⊗ₜ 1) * s₁ + (u ⊗ₜ 1) * s₂, ?_⟩` and prove the remaining obligations. Establish `: ((u * v) ⊗ₜ[T] (1 : C)) = (u ⊗ₜ 1) * (v ⊗ₜ 1)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[this, map_add, map_mul, map_mul, map_mul, ← h₁, ← h₂]`. Expand and normalize the polynomial expressions, which then agree. Establish `: Module.Finite F K` using `finite_fractionRing_of_finite T C F K`. Establish `: IsArtinianRing (L ⊗[F] K)` using `IsArtinianRing.of_finite L (L ⊗[F] K)`.

Introduce `s hs`. Apply `IsArtinianRing.isUnit_of_mem_nonZeroDivisors` to reduce the goal to its premises. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `ω hω`. Take `⟨u, hu, s', h⟩` from `den ω`.

Establish `h0 : s' * s = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, ← h, mul_assoc, hω, mul_zero, map_zero]`. Establish `hs' : s' = 0` using `(mem_nonZeroDivisors_iff_right.1 hs) s' h0`. Establish `huL : algebraMap U L u ≠ 0` using `by simpa using hu`.

Establish `hunit : IsUnit (φ (u ⊗ₜ 1))`. Rewrite using `[hφ, map_one]`. Conclude with `(IsUnit.mk0 _ huL).map (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := L) (B := K))`. Rewrite `h` using `[hs', map_zero]`. Conclude with `(hunit.mul_right_eq_zero).1 h`.
-/
theorem isUnit_map_of_mem_nonZeroDivisors_tensor (T U C F K L : Type) [CommRing T] [IsDomain T]
    [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L]
    [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K]
    [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K]
    [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L]
    [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C]
    (φ : U ⊗[T] C →+* L ⊗[F] K) (hinj : Function.Injective φ)
    (hφ : ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) :
    ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by
  have hTU : ∀ t : T, t ≠ 0 → algebraMap T U t ≠ 0 := by
    intro t ht h0
    have h1 : algebraMap T L t = 0 := by
      rw [IsScalarTower.algebraMap_apply T U L, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply T F L] at h1
    apply ht
    simpa using h1
  have den : ∀ ω : L ⊗[F] K, ∃ u : U, u ≠ 0 ∧ ∃ s', φ (u ⊗ₜ 1) * ω = φ s' := by
    intro ω
    induction ω using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul l k =>
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := U) l
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbL : algebraMap U L b ≠ 0 := by simpa using hb0
      obtain ⟨t, ht, c, hc⟩ := exists_base_denominator_of_finite (T := T) (C := C) k
      refine ⟨algebraMap T U t * b, mul_ne_zero (hTU t ht) hb0, a ⊗ₜ c, ?_⟩
      rw [hφ, hφ, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hc,
        IsScalarTower.algebraMap_apply T F K, ← Algebra.smul_def (algebraMap T F t) k,
        ← TensorProduct.smul_tmul,
        Algebra.smul_def, ← IsScalarTower.algebraMap_apply T F L, map_mul,
        ← IsScalarTower.algebraMap_apply T U L]
      congr 1
      field_simp
    | add x y hx hy =>
      obtain ⟨u, hu, s₁, h₁⟩ := hx
      obtain ⟨v, hv, s₂, h₂⟩ := hy
      refine ⟨u * v, mul_ne_zero hu hv, (v ⊗ₜ 1) * s₁ + (u ⊗ₜ 1) * s₂, ?_⟩
      have : ((u * v) ⊗ₜ[T] (1 : C)) = (u ⊗ₜ 1) * (v ⊗ₜ 1) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this, map_add, map_mul, map_mul, map_mul, ← h₁, ← h₂]
      ring
  have : Module.Finite F K := finite_fractionRing_of_finite T C F K
  have : IsArtinianRing (L ⊗[F] K) := IsArtinianRing.of_finite L (L ⊗[F] K)
  intro s hs
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro ω hω
  obtain ⟨u, hu, s', h⟩ := den ω
  have h0 : s' * s = 0 := by
    apply hinj
    rw [map_mul, ← h, mul_assoc, hω, mul_zero, map_zero]
  have hs' : s' = 0 := (mem_nonZeroDivisors_iff_right.1 hs) s' h0
  have huL : algebraMap U L u ≠ 0 := by simpa using hu
  have hunit : IsUnit (φ (u ⊗ₜ 1)) := by
    rw [hφ, map_one]
    exact (IsUnit.mk0 _ huL).map (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := L) (B := K))
  rw [hs', map_zero] at h
  exact (hunit.mul_right_eq_zero).1 h

end GlobalTheory
