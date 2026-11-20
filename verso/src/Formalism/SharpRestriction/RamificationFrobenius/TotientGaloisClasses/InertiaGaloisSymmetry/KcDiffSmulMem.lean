import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcBase

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

/- English proof (translation)
Establish `h : σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ` using `H.gal.injective (by rw [map_mul, map_mul, mul_comm])`. Use `congrArg (fun f : H.E ≃ₐ[ℚ] H.E => f x) h` as an intermediate fact. Simplify `this` using `only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]`.
-/
theorem kc_comm_of (σ : H.E ≃ₐ[ℚ] H.E) (τ : H.E ≃ₐ[H.K] H.E) (x : H.E) : σ (τ x) = τ (σ x) := by
  have h : σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ :=
    H.gal.injective (by rw [map_mul, map_mul, mul_comm])
  have := congrArg (fun f : H.E ≃ₐ[ℚ] H.E => f x) h
  simpa only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply] using this

/- English proof (translation)
Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.apply_symm_apply, hc, AlgEquiv.apply_symm_apply]`.
-/
theorem kc_comm_symm (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x))
    (τ : H.E ≃ₐ[H.K] H.E) (x : H.E) : σ.symm (τ x) = τ (σ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, hc, AlgEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun τ _ => hc τ w`.
-/
theorem kc_sum_comm (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (w : H.E) :
    σ (∑ τ : H.E ≃ₐ[H.K] H.E, τ w) = ∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ w) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun τ _ => hc τ w

/- English proof (translation)
The claim follows from `one_ne_zero`.
-/
theorem kc_one_ne : (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := one_ne_zero

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe y`. Introduce `h`.

Conclude with `⟨⟨t, h⟩, rfl⟩`.
-/
private theorem mem_one_fractionalIdeal_iff_isIntegral (t : H.E) : t ∈ (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

/- English proof (translation)
The claim follows from `isIntegral_algEquiv (σ.restrictScalars ℤ)`.
-/
private theorem isIntegral_algEquiv_apply_iff (σ : H.E ≃ₐ[ℚ] H.E) (t : H.E) : IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

/- English proof (translation)
Use `haveI := H.galois`. Rewrite using `[FractionalIdeal.mem_dual (kc_one_ne H)]`. Establish `key : ∀ w : H.E, Algebra.trace H.K H.E w ∈ (algebraMap (𝓞 H.K) H.K).range ↔ IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ w)`. Introduce `w`. Rewrite using `[← trace_eq_sum_automorphisms, isIntegral_algebraMap_iff (algebraMap H.K H.E).injective]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Rewrite using `[← ha]`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe a`. Introduce `h`.

Conclude with `⟨⟨_, h⟩, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Rewrite using `[← key]`. Use `h _ ((mem_one_fractionalIdeal_iff_isIntegral H _).mpr (NumberField.RingOfIntegers.isIntegral_coe x))` as an intermediate fact.

Rewrite `this` using `[Algebra.traceForm_apply]`. Then use the resulting hypothesis. Introduce `h a ha`. Rewrite `ha` using `[mem_one_fractionalIdeal_iff_isIntegral]`. Rewrite using `[Algebra.traceForm_apply, key]`. Conclude with `h ⟨a, ha⟩`.
-/
theorem kc_mem_dual_iff (y : H.E) :
    y ∈ FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x)) := by
  haveI := H.galois
  rw [FractionalIdeal.mem_dual (kc_one_ne H)]
  have key : ∀ w : H.E, Algebra.trace H.K H.E w ∈ (algebraMap (𝓞 H.K) H.K).range ↔
      IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ w) := by
    intro w
    rw [← trace_eq_sum_automorphisms, isIntegral_algebraMap_iff (algebraMap H.K H.E).injective]
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]
      exact NumberField.RingOfIntegers.isIntegral_coe a
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  constructor
  · intro h x
    rw [← key]
    have := h _ ((mem_one_fractionalIdeal_iff_isIntegral H _).mpr (NumberField.RingOfIntegers.isIntegral_coe x))
    rwa [Algebra.traceForm_apply] at this
  · intro h a ha
    rw [mem_one_fractionalIdeal_iff_isIntegral] at ha
    rw [Algebra.traceForm_apply, key]
    exact h ⟨a, ha⟩

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/- English proof (translation)
Establish `hd : FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0`. Simplify `kc_one_ne H` using `[FractionalIdeal.dual_eq_zero_iff]`. Establish `e1 : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔ (z : H.E) ∈ ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)`. Rewrite using `[FractionalIdeal.mem_coeIdeal]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨z, h, rfl⟩`. Introduce and unpack `⟨w, hw, e⟩`. Establish `: w = z` using `NumberField.RingOfIntegers.ext e`. Rewrite using `[← this]` and apply the resulting hypothesis.

Rewrite using `[e1, coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E), FractionalIdeal.mem_inv_iff hd]`. Simplify using `only [kc_mem_dual_iff, mem_one_fractionalIdeal_iff_isIntegral]`.
-/
theorem kc_mem_diff_iff (z : 𝓞 H.E) :
    z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      ∀ y : H.E, (∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) →
        IsIntegral ℤ ((z : H.E) * y) := by
  have hd : FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
    simpa [FractionalIdeal.dual_eq_zero_iff] using kc_one_ne H
  have e1 : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      (z : H.E) ∈ ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    · intro h
      exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, e⟩
      have : w = z := NumberField.RingOfIntegers.ext e
      rwa [← this]
  rw [e1, coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E), FractionalIdeal.mem_inv_iff hd]
  simp only [kc_mem_dual_iff, mem_one_fractionalIdeal_iff_isIntegral]

/- English proof (translation)
Introduce `x`. Establish `hx` using `hy (σ⁻¹ • x)`. Establish `hx' : σ ((σ⁻¹ • x : 𝓞 H.E) : H.E) = (x : H.E)` using `by show σ (σ⁻¹ (x : H.E)) = x`. Rewrite using `[AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]`. Establish `e : ∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x) = σ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * ((σ⁻¹ • x : 𝓞 H.E) : H.E)))`.

Rewrite using `[kc_sum_comm H σ hc]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul σ, hx']`. Rewrite using `[e, isIntegral_algEquiv_apply_iff]`. Conclude with `hx`.
-/
theorem kc_dual_smul (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (y : H.E)
    (hy : ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) :
    ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x)) := by
  intro x
  have hx := hy (σ⁻¹ • x)
  have hx' : σ ((σ⁻¹ • x : 𝓞 H.E) : H.E) = (x : H.E) := by
    show σ (σ⁻¹ (x : H.E)) = x
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have e : ∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x) =
      σ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * ((σ⁻¹ • x : 𝓞 H.E) : H.E))) := by
    rw [kc_sum_comm H σ hc]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul σ, hx']
  rw [e, isIntegral_algEquiv_apply_iff]
  exact hx

/- English proof (translation)
Rewrite `hz`, the goal using `[kc_mem_diff_iff]`. Introduce `y hy`. Establish `hy'` using `kc_dual_smul H σ.symm (kc_comm_symm H σ hc) y hy`. Establish `h1` using `hz (σ.symm y) hy'`. Rewrite `h1` using `[← isIntegral_algEquiv_apply_iff H σ, map_mul, AlgEquiv.apply_symm_apply]`.

Establish `e : ((σ • z : 𝓞 H.E) : H.E) = σ (z : H.E)` using `rfl`. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem kc_diff_smul_mem (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (z : 𝓞 H.E)
    (hz : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E)) : σ • z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  rw [kc_mem_diff_iff] at hz ⊢
  intro y hy
  have hy' := kc_dual_smul H σ.symm (kc_comm_symm H σ hc) y hy
  have h1 := hz (σ.symm y) hy'
  rw [← isIntegral_algEquiv_apply_iff H σ, map_mul, AlgEquiv.apply_symm_apply] at h1
  have e : ((σ • z : 𝓞 H.E) : H.E) = σ (z : H.E) := rfl
  rw [e]
  exact h1

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Use `kc_diff_smul_mem H σ hc _ hx` as an intermediate fact. Rewrite `this` using `[smul_inv_smul]`. Then use the resulting hypothesis.
-/
theorem kc_diff_smul_le (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) ≤ differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
  have := kc_diff_smul_mem H σ hc _ hx
  rwa [smul_inv_smul] at this

/- English proof (translation)
Apply `le_antisymm (kc_diff_smul_le H σ (kc_comm_of H σ))` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Conclude with `kc_diff_smul_mem H σ⁻¹ (kc_comm_of H σ⁻¹) x hx`.
-/
theorem kc_diff_smul_eq (σ : H.E ≃ₐ[ℚ] H.E) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  apply le_antisymm (kc_diff_smul_le H σ (kc_comm_of H σ))
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  exact kc_diff_smul_mem H σ⁻¹ (kc_comm_of H σ⁻¹) x hx

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe y`. Introduce `h`.

Conclude with `⟨⟨t, h⟩, rfl⟩`.
-/
theorem kc_mem_one_iff (t : H.E) :
    t ∈ (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

/- English proof (translation)
The claim follows from `isIntegral_algEquiv (σ.restrictScalars ℤ)`.
-/
theorem kc_integ_iff (σ : H.E ≃ₐ[ℚ] H.E) (t : H.E) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

/- English proof (translation)
Introduce `h`. Apply `hB` to reduce the goal to its premises. Rewrite using `[← inv_smul_smul σ B, h]`. Use extensionality with `x`. Simplify using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`.
-/
theorem kc_smul_ne_bot (σ : H.E ≃ₐ[ℚ] H.E) (B : Ideal (𝓞 H.E))
    (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  rw [← inv_smul_smul σ B, h]
  ext x
  simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]

/- English proof (translation)
Establish `hB' : (B : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hB`. Establish `hσB : ((σ • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H σ B hB)`. Rewrite using `[FractionalIdeal.mem_inv_iff hσB, FractionalIdeal.mem_inv_iff hB']`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`.

Rewrite `hw` using `[FractionalIdeal.mem_coeIdeal]`. Take `⟨b, hb, rfl⟩` from `hw`. Establish `hb' : σ • b ∈ σ • B`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]`. Conclude with `hb`.

Use `h (algebraMap (𝓞 H.E) H.E (σ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ • b, hb', rfl⟩)` as an intermediate fact. Rewrite `this`, the goal using `[kc_mem_one_iff]`. Rewrite `this` using `[show algebraMap (𝓞 H.E) H.E (σ • b) = σ (algebraMap (𝓞 H.E) H.E b) from rfl, ← map_mul, kc_integ_iff]`. Conclude with `this`. Introduce `h w hw`.

Rewrite `hw` using `[FractionalIdeal.mem_coeIdeal]`. Take `⟨b, hb, rfl⟩` from `hw`. Rewrite `hb` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Use `h (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ⁻¹ • b, hb, rfl⟩)` as an intermediate fact. Rewrite `this`, the goal using `[kc_mem_one_iff]`.

Establish `e : σ (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) = algebraMap (𝓞 H.E) H.E b` using `by show σ (σ⁻¹ (b : H.E)) = b`. Rewrite using `[AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]`. Rewrite `this` using `[← kc_integ_iff H σ, map_mul, e]`. Conclude with `this`.
-/
theorem kc_mem_inv_smul (σ : H.E ≃ₐ[ℚ] H.E) (B : Ideal (𝓞 H.E))
    (hB : B ≠ ⊥) (y : H.E) :
    σ y ∈ ((σ • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by
  have hB' : (B : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB
  have hσB : ((σ • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H σ B hB)
  rw [FractionalIdeal.mem_inv_iff hσB, FractionalIdeal.mem_inv_iff hB']
  constructor
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    have hb' : σ • b ∈ σ • B := by
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
      exact hb
    have := h (algebraMap (𝓞 H.E) H.E (σ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ • b, hb', rfl⟩)
    rw [kc_mem_one_iff] at this ⊢
    rw [show algebraMap (𝓞 H.E) H.E (σ • b) = σ (algebraMap (𝓞 H.E) H.E b) from rfl, ← map_mul,
      kc_integ_iff] at this
    exact this
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have := h (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ⁻¹ • b, hb, rfl⟩)
    rw [kc_mem_one_iff] at this ⊢
    have e : σ (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) = algebraMap (𝓞 H.E) H.E b := by
      show σ (σ⁻¹ (b : H.E)) = b
      rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rw [← kc_integ_iff H σ, map_mul, e] at this
    exact this

/- English proof (translation)
Introduce `B hdiff x`. Establish `hD0` using `differentIdeal_ne_bot (A := 𝓞 H.K) (B := 𝓞 H.E)`. Establish `hB : B ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hdiff` using `[← Ideal.zero_eq_bot, zero_mul]`.

Conclude with `hD0 hdiff`. Establish `hJ : ((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H H.conj B hB)`. Establish `hdual : FractionalIdeal.dual (𝓞 H.K) H.K (((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) = ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹`. Rewrite using `[FractionalIdeal.dual_eq_mul_inv, inv_inv, ← inv_inv (FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E)), ← coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E), hdiff, FractionalIdeal.coeIdeal_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hJ, mul_one]`. Establish `hx : x ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ ↔ x ∈ FractionalIdeal.dual (𝓞 H.K) H.K (((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹)`.

Rewrite using `[hdual]`. Rewrite using `[hx, FractionalIdeal.mem_dual (inv_ne_zero hJ)]`. Prove the components needed by the constructor for the conclusion. Introduce `hh y hy`. Use `hh (H.conj y) ((kc_mem_inv_smul H H.conj B hB y).mpr hy)` as an intermediate fact.

Rewrite `this` using `[Algebra.traceForm_apply]`. Then use the resulting hypothesis. Introduce `hh z hz`. Rewrite using `[Algebra.traceForm_apply]`. Establish `hz' : H.conj (H.conj.symm z) = z` using `H.conj.apply_symm_apply z`. Rewrite `hz`, the goal using `[← hz']`.

Conclude with `hh _ ((kc_mem_inv_smul H H.conj B hB _).mp hz)`.
-/
theorem unimodular : ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → ∀ x : H.E,
    x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
      ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
        Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range := by
  intro B hdiff x
  have hD0 := differentIdeal_ne_bot (A := 𝓞 H.K) (B := 𝓞 H.E)
  have hB : B ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_mul] at hdiff
    exact hD0 hdiff
  have hJ : ((H.conj • B : Ideal (𝓞 H.E)) :
      FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H H.conj B hB)
  have hdual : FractionalIdeal.dual (𝓞 H.K) H.K
      (((H.conj • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) =
      ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by
    rw [FractionalIdeal.dual_eq_mul_inv, inv_inv,
      ← inv_inv (FractionalIdeal.dual (𝓞 H.K) H.K
        (1 : FractionalIdeal (𝓞 H.E)⁰ H.E)),
      ← coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E),
      hdiff, FractionalIdeal.coeIdeal_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hJ, mul_one]
  have hx : x ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ ↔
      x ∈ FractionalIdeal.dual (𝓞 H.K) H.K
        (((H.conj • B : Ideal (𝓞 H.E)) :
          FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) := by
    rw [hdual]
  rw [hx, FractionalIdeal.mem_dual (inv_ne_zero hJ)]
  constructor
  · intro hh y hy
    have := hh (H.conj y) ((kc_mem_inv_smul H H.conj B hB y).mpr hy)
    rwa [Algebra.traceForm_apply] at this
  · intro hh z hz
    rw [Algebra.traceForm_apply]
    have hz' : H.conj (H.conj.symm z) = z := H.conj.apply_symm_apply z
    rw [← hz'] at hz ⊢
    exact hh _ ((kc_mem_inv_smul H H.conj B hB _).mp hz)

end Formalism.HC.Der

end
