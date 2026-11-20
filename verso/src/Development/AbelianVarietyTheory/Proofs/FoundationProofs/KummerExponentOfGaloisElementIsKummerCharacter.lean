import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle

noncomputable section

open Polynomial IntermediateField

namespace GlobalTheory.NeedB.KumLemma

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/- English proof (translation)
Rewrite using `[ZMod.val_add, ← pow_add]`. Use `conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N]`. Rewrite using `[pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`.
-/
theorem pow_val_add {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

/- English proof (translation)
Take `⟨c, hc⟩` from `hN`. Establish `hg : (g θ) ^ N = θ ^ N` using `by rw [← map_pow, ← hc, AlgEquiv.commutes]`. Establish `h1 : (g θ / θ) ^ N = 1`. Rewrite using `[div_pow, hg, div_self (pow_ne_zero _ hθ)]`. Take `⟨i, hi, hi'⟩` from `hζ.eq_pow_of_pow_eq_one h1`.

Use `⟨(i : ZMod N), ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.val_cast_of_lt hi, hi', div_mul_cancel₀ _ hθ]`.
-/
theorem exists_pow {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    ∃ i : ZMod N, g θ = ζ ^ i.val * θ := by
  obtain ⟨c, hc⟩ := hN
  have hg : (g θ) ^ N = θ ^ N := by rw [← map_pow, ← hc, AlgEquiv.commutes]
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, hg, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_cast_of_lt hi, hi', div_mul_cancel₀ _ hθ]

/- English proof (translation)
Establish `h' : ζ ^ a.val = ζ ^ b.val` using `mul_right_cancel₀ hθ h`. Conclude with `ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')`.
-/
theorem unique_pow {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    {a b : ZMod N} (h : ζ ^ a.val * θ = ζ ^ b.val * θ) : a = b := by
  have h' : ζ ^ a.val = ζ ^ b.val := mul_right_cancel₀ hθ h
  exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')

/- English proof (translation)
Establish `h` using `exists_pow hζ hθ hN g`. Unfold `kum`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem kum_spec {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    g θ = ζ ^ (kum (N := N) ζ θ g).val * θ := by
  have h := exists_pow hζ hθ hN g
  unfold kum
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
The claim follows from `unique_pow hζ hθ ((kum_spec hζ hθ hN g).symm.trans hi)`.
-/
theorem kum_eq {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) {i : ZMod N}
    (hi : g θ = ζ ^ i.val * θ) : kum (N := N) ζ θ g = i :=
  unique_pow hζ hθ ((kum_spec hζ hθ hN g).symm.trans hi)

/- English proof (translation)
Apply `kum_eq hζ hθ hN` to reduce the goal to its premises. Rewrite using `[AlgEquiv.mul_apply, kum_spec hζ hθ hN h, map_mul, map_pow, hfix, kum_spec hζ hθ hN g, add_comm, pow_val_add hζ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kum_mul {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ)
    (hθ : θ ≠ 0) (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g h : Ω ≃ₐ[K] Ω) :
    kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h := by
  apply kum_eq hζ hθ hN
  rw [AlgEquiv.mul_apply, kum_spec hζ hθ hN h, map_mul, map_pow, hfix, kum_spec hζ hθ hN g,
    add_comm, pow_val_add hζ]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `kum_spec hζ hθ hN g` as an intermediate fact. Rewrite `this` using `[h, ZMod.val_zero, pow_zero, one_mul]`. Then use the resulting hypothesis. Introduce `h`.

Apply `kum_eq hζ hθ hN` to reduce the goal to its premises. Rewrite using `[h, ZMod.val_zero, pow_zero, one_mul]`.
-/
theorem kum_eq_zero_iff {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    kum (N := N) ζ θ g = 0 ↔ g θ = θ := by
  constructor
  · intro h
    have := kum_spec hζ hθ hN g
    rwa [h, ZMod.val_zero, pow_zero, one_mul] at this
  · intro h
    apply kum_eq hζ hθ hN
    rw [h, ZMod.val_zero, pow_zero, one_mul]

/- English proof (translation)
Use `haveI : NeZero N := ⟨by omega⟩`. Use `⟨?_, kum_spec hζ hθ hN, kum_mul hζ hfix hθ hN, kum_eq_zero_iff hζ hθ hN⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `g`. Use `haveI : FiniteDimensional K K⟮θ⟯ := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral θ)`.

Establish `hopen : IsOpen ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω))` using `IntermediateField.fixingSubgroup_isOpen _`. Use `⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)), hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]`. Conclude with `Subgroup.one_mem _`. Introduce `g' hg'`.

Establish `hfθ : (g⁻¹ * g') θ = θ`. Use `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' θ (IntermediateField.mem_adjoin_simple_self K θ)` as an intermediate fact. Conclude with `this`. Establish `h0` using `(kum_eq_zero_iff hζ hθ hN _).2 hfθ`. Establish `: g' = g * (g⁻¹ * g')` using `by group`.

Rewrite using `[this, kum_mul hζ hfix hθ hN, h0, add_zero]`.
-/
theorem kummer_character [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω) (hN0 : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) :
    IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
    (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧
    (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) := by
  haveI : NeZero N := ⟨by omega⟩
  refine ⟨?_, kum_spec hζ hθ hN, kum_mul hζ hfix hθ hN, kum_eq_zero_iff hζ hθ hN⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮θ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral θ)
  have hopen : IsOpen ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfθ : (g⁻¹ * g') θ = θ := by
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' θ
        (IntermediateField.mem_adjoin_simple_self K θ)
      exact this
    have h0 := (kum_eq_zero_iff hζ hθ hN _).2 hfθ
    have : g' = g * (g⁻¹ * g') := by group
    rw [this, kum_mul hζ hfix hθ hN, h0, add_zero]

end GlobalTheory.NeedB.KumLemma

open GlobalTheory.NeedB in

/- English proof (translation)
Introduce `K Ω _ _ _ _ N ζ θ h0 hζ hf hθ hN` and use `GlobalTheory.NeedB.KumLemma.kummer_character N ζ θ h0 hζ hf hθ hN`.
-/
theorem GlobalTheory.NeedB.KumLemma.kummer_character_main : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → θ ≠ 0 → θ ^ N ∈ Set.range (algebraMap K Ω) →
  IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
  (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧ (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) :=
  fun K Ω _ _ _ _ N ζ θ h0 hζ hf hθ hN => GlobalTheory.NeedB.KumLemma.kummer_character N ζ θ h0 hζ hf hθ hN
