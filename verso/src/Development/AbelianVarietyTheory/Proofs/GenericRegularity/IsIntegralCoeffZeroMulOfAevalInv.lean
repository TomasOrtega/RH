import Mathlib

namespace GlobalTheory

open Polynomial

open Polynomial in

/- English proof (translation)
Introduce `O O' _ _ _ _ _ _ _ _ _ _ _ hpts A Ω _ _ _ _ _ _ _ hOA e he f hf`. Distinguish the cases in `hf0 : f = 0`. Conclude with `⟨1, by simp, by simp [hf0, isIntegral_zero]⟩`. Take `⟨d, c, hc, hdc⟩` from `IsFractionRing.div_surjective (A := A) f`. Establish `hc0 : c ≠ 0` using `nonZeroDivisors.ne_zero hc`.

Establish `hinj : Function.Injective (algebraMap A Ω)` using `IsFractionRing.injective A Ω`. Establish `hcΩ : algebraMap A Ω c ≠ 0` using `(map_ne_zero_iff _ hinj).2 hc0`. Establish `hfc : f * algebraMap A Ω c = algebraMap A Ω d` using `by rw [← hdc, div_mul_cancel₀ _ hcΩ]`. Use `set g : Ω := f⁻¹ with hg`. Establish `hgf : g * f = 1` using `inv_mul_cancel₀ hf0`.

Establish `hgd : g * algebraMap A Ω d = algebraMap A Ω c`. Rewrite using `[← hfc, ← mul_assoc, hgf, one_mul]`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hπm : π ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit`. Set `B` to `Algebra.adjoin A ({g} : Set Ω)`.

Use `letI : Algebra O B := ((algebraMap A B).comp (algebraMap O A)).toAlgebra`. Use `haveI : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : Algebra.FiniteType A B := ⟨(Subalgebra.fg_top B).2 (by simpa using Subalgebra.fg_adjoin_finset (R := A) {g})⟩`. Use `haveI : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance`. Establish `hOB : Function.Injective (algebraMap O B)`.

Introduce `x y hxy`. Conclude with `hOA (hinj (congrArg Subtype.val hxy))`. Set `gB : B` to `⟨g, Algebra.self_mem_adjoin_singleton A g⟩`. Set `I : Ideal B` to `Ideal.span ({gB, algebraMap O B π} : Set B)`. Establish `hI : I = ⊤`.

Assume the negation of the conclusion as `hI`. Establish `hmI : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I`. Rewrite using `[hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.subset_span (by simp)`. Establish `hec : algebraMap A B (e * c) ≠ 0`.

Introduce `h`. Conclude with `mul_ne_zero he hc0 (hinj (by simpa using congrArg Subtype.val h))`. Take `⟨V, _, _, _, _, _, φ, hφ, hφe, hφI⟩` from `hpts B hOB I hI hmI _ hec`. Set `ψ : A →+* V` to `φ.comp (algebraMap A B)`. Establish `hψ : ψ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O')` using `hφ`.

Establish `hψec : ψ e * ψ c ≠ 0`. Simplify `hφe` using `[ψ, map_mul]`. Establish `hψc : ψ c ≠ 0` using `right_ne_zero_of_mul hψec`. Take `⟨t, ht⟩` from `hf V ψ hψ (left_ne_zero_of_mul hψec) d c hfc hψc`. Establish `hmem : φ gB ∈ IsLocalRing.maximalIdeal V` using `hφI gB (Ideal.subset_span (by simp))`.

Establish `h1 : φ gB * ψ d = ψ c`. Simplify using `only [ψ, RingHom.comp_apply, ← map_mul]`. Use `congr 1`. Conclude with `Subtype.ext hgd`. Establish `hu : IsUnit (φ gB)`.

Use `IsUnit.of_mul_eq_one t ?_` and prove the remaining obligations. Establish `h2 : ψ c * (φ gB * t) = ψ c * 1` using `by linear_combination (-φ gB) * ht + h1`. Conclude with `mul_left_cancel₀ hψc h2`. Conclude with `((IsLocalRing.mem_maximalIdeal _).1 hmem) hu`. Establish `hone : (1 : B) ∈ I` using `hI ▸ Submodule.mem_top`.

Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.1 hone`. Establish `hpoly : ∀ x : B, ∃ p : A[X], aeval g p = (x : Ω)`. Introduce `x`. Establish `hx : (x : Ω) ∈ Algebra.adjoin A ({g} : Set Ω)` using `x.2`. Rewrite `hx` using `[Algebra.adjoin_singleton_eq_range_aeval]`.

Conclude with `(AlgHom.mem_range _).1 hx`. Take `⟨p, hp⟩` from `hpoly a`. Take `⟨r, hr⟩` from `hpoly b`. Establish `hΩ : (a : Ω) * g + (b : Ω) * algebraMap A Ω (algebraMap O A π) = 1` using `congrArg Subtype.val hab`. Set `H : A[X]` to `1 - X * p - C (algebraMap O A π) * r`.

Establish `hH : aeval g H = 0`. Simplify using `only [H, map_sub, map_one, map_mul, aeval_X, aeval_C, hp, hr]`. Take the linear combination `-hΩ`. Use `letI : Invertible g := invertibleOfNonzero (inv_ne_zero hf0)`. Establish `hrev : aeval f (reverse H) = 0`.

Establish `key` using `eval₂_reverse_mul_pow (algebraMap A Ω) g H`. Establish `hinv : ⅟g = f` using `by rw [invOf_eq_inv, hg, inv_inv]`. Rewrite `key` using `[hinv, ← aeval_def, ← aeval_def, hH]`. Conclude with `(mul_eq_zero.1 key).resolve_right (pow_ne_zero _ (inv_ne_zero hf0))`. Establish `hint` using `isIntegral_leadingCoeff_smul (reverse H) f hrev`.

Establish `hcoeff : H.coeff 0 = 1 - algebraMap O A π * r.coeff 0` using `by simp [H]`. Use `⟨H.coeff 0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcoeff, sub_sub_cancel_left]`. Conclude with `(Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπm))`. Distinguish the cases in `h0 : H.coeff 0 = 0`.

Rewrite using `[h0, map_zero, zero_mul]`. Conclude with `isIntegral_zero`. Establish `hlead : (reverse H).leadingCoeff = H.coeff 0`. Rewrite using `[reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (Or.inr h0)]`. Rewrite using `[← hlead, ← Algebra.smul_def]`.

Conclude with `hint`.
-/
theorem _root_.GlobalTheory.isIntegral_mul_of_bounded_at_points :
    ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → (∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω], Function.Injective (algebraMap O A) → ∀ (e : A), e ≠ 0 → ∀ f : Ω, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O' V] [Module.Finite O' V] (φ : A →+* V), φ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') → φ e ≠ 0 → ∀ a b : A, f * algebraMap A Ω b = algebraMap A Ω a → φ b ≠ 0 → φ b ∣ φ a) → ∃ s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧ IsIntegral A (algebraMap A Ω s * f) := by
  intro O O' _ _ _ _ _ _ _ _ _ _ _ hpts A Ω _ _ _ _ _ _ _ hOA e he f hf
  by_cases hf0 : f = 0
  · exact ⟨1, by simp, by simp [hf0, isIntegral_zero]⟩
  obtain ⟨d, c, hc, hdc⟩ := IsFractionRing.div_surjective (A := A) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hcΩ : algebraMap A Ω c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hfc : f * algebraMap A Ω c = algebraMap A Ω d := by rw [← hdc, div_mul_cancel₀ _ hcΩ]
  set g : Ω := f⁻¹ with hg
  have hgf : g * f = 1 := inv_mul_cancel₀ hf0
  have hgd : g * algebraMap A Ω d = algebraMap A Ω c := by
    rw [← hfc, ← mul_assoc, hgf, one_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : π ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  let B := Algebra.adjoin A ({g} : Set Ω)
  letI : Algebra O B := ((algebraMap A B).comp (algebraMap O A)).toAlgebra
  haveI : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A B :=
    ⟨(Subalgebra.fg_top B).2 (by simpa using Subalgebra.fg_adjoin_finset (R := A) {g})⟩
  haveI : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hOB : Function.Injective (algebraMap O B) := by
    intro x y hxy
    exact hOA (hinj (congrArg Subtype.val hxy))
  let gB : B := ⟨g, Algebra.self_mem_adjoin_singleton A g⟩
  let I : Ideal B := Ideal.span ({gB, algebraMap O B π} : Set B)
  have hI : I = ⊤ := by
    by_contra hI
    have hmI : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    have hec : algebraMap A B (e * c) ≠ 0 := by
      intro h
      exact mul_ne_zero he hc0 (hinj (by simpa using congrArg Subtype.val h))
    obtain ⟨V, _, _, _, _, _, φ, hφ, hφe, hφI⟩ := hpts B hOB I hI hmI _ hec
    let ψ : A →+* V := φ.comp (algebraMap A B)
    have hψ : ψ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') := hφ
    have hψec : ψ e * ψ c ≠ 0 := by
      simpa [ψ, map_mul] using hφe
    have hψc : ψ c ≠ 0 := right_ne_zero_of_mul hψec
    obtain ⟨t, ht⟩ := hf V ψ hψ (left_ne_zero_of_mul hψec) d c hfc hψc
    have hmem : φ gB ∈ IsLocalRing.maximalIdeal V := hφI gB (Ideal.subset_span (by simp))
    have h1 : φ gB * ψ d = ψ c := by
      simp only [ψ, RingHom.comp_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgd
    have hu : IsUnit (φ gB) := by
      refine IsUnit.of_mul_eq_one t ?_
      have h2 : ψ c * (φ gB * t) = ψ c * 1 := by linear_combination (-φ gB) * ht + h1
      exact mul_left_cancel₀ hψc h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmem) hu
  have hone : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hone
  have hpoly : ∀ x : B, ∃ p : A[X], aeval g p = (x : Ω) := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin A ({g} : Set Ω) := x.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact (AlgHom.mem_range _).1 hx
  obtain ⟨p, hp⟩ := hpoly a
  obtain ⟨r, hr⟩ := hpoly b
  have hΩ : (a : Ω) * g + (b : Ω) * algebraMap A Ω (algebraMap O A π) = 1 :=
    congrArg Subtype.val hab
  let H : A[X] := 1 - X * p - C (algebraMap O A π) * r
  have hH : aeval g H = 0 := by
    simp only [H, map_sub, map_one, map_mul, aeval_X, aeval_C, hp, hr]
    linear_combination -hΩ
  letI : Invertible g := invertibleOfNonzero (inv_ne_zero hf0)
  have hrev : aeval f (reverse H) = 0 := by
    have key := eval₂_reverse_mul_pow (algebraMap A Ω) g H
    have hinv : ⅟g = f := by rw [invOf_eq_inv, hg, inv_inv]
    rw [hinv, ← aeval_def, ← aeval_def, hH] at key
    exact (mul_eq_zero.1 key).resolve_right (pow_ne_zero _ (inv_ne_zero hf0))
  have hint := isIntegral_leadingCoeff_smul (reverse H) f hrev
  have hcoeff : H.coeff 0 = 1 - algebraMap O A π * r.coeff 0 := by simp [H]
  refine ⟨H.coeff 0, ?_, ?_⟩
  · rw [hcoeff, sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπm))
  · by_cases h0 : H.coeff 0 = 0
    · rw [h0, map_zero, zero_mul]
      exact isIntegral_zero
    · have hlead : (reverse H).leadingCoeff = H.coeff 0 := by
        rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (Or.inr h0)]
      rw [← hlead, ← Algebra.smul_def]
      exact hint

end GlobalTheory
