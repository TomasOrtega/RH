import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing TensorProduct

namespace GlobalTheory.CompletionFactor

/- English proof (translation)
Establish `hc : IsCoprime (Ideal.span {1 - e}) (Ideal.span {e} : Ideal S)`. Rewrite using `[Ideal.isCoprime_span_singleton_iff]`. Conclude with `⟨1, 1, by ring⟩`. Establish `hb : (⊥ : Ideal S) = Ideal.span {1 - e} ⊓ Ideal.span {e}`. Rewrite using `[Ideal.inf_eq_mul_of_isCoprime hc, Ideal.span_singleton_mul_span_singleton, sub_mul, one_mul, he.eq, sub_self, Ideal.span_singleton_zero]`.

Use `⟨(RingEquiv.quotientBot S).symm.trans ((Ideal.quotEquivOfEq hb).trans (Ideal.quotientInfEquivQuotientProd _ _ hc)), fun x => ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem exists_ringEquiv_prod_of_isIdempotentElem {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) :
    ∃ ε : S ≃+* (S ⧸ Ideal.span {1 - e}) × (S ⧸ Ideal.span {e}),
      ∀ x, (ε x).1 = Ideal.Quotient.mk _ x := by
  have hc : IsCoprime (Ideal.span {1 - e}) (Ideal.span {e} : Ideal S) := by
    rw [Ideal.isCoprime_span_singleton_iff]
    exact ⟨1, 1, by ring⟩
  have hb : (⊥ : Ideal S) = Ideal.span {1 - e} ⊓ Ideal.span {e} := by
    rw [Ideal.inf_eq_mul_of_isCoprime hc, Ideal.span_singleton_mul_span_singleton, sub_mul,
      one_mul, he.eq, sub_self, Ideal.span_singleton_zero]
  refine ⟨(RingEquiv.quotientBot S).symm.trans ((Ideal.quotEquivOfEq hb).trans
    (Ideal.quotientInfEquivQuotientProd _ _ hc)), fun x => ?_⟩
  rfl

/- English proof (translation)
Establish `hq : ((maximalIdeal D).comap φ).IsMaximal`. Apply `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B)` to reduce the goal to its premises. Rewrite using `[Ideal.comap_comap, ← (maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hφ]`. Use `infer_instance`. Take `⟨e, he, H⟩` from `exists_idempotent_notMem_iff_of_henselian B ((maximalIdeal D).comap φ)`.

Establish `hl` using `isLocalRing_quotient_one_sub he _ H`. Establish `h1 : φ e = 1`. Use `(IsIdempotentElem.iff_eq_one_of_isUnit ?_).1 (he.map φ)` and prove the remaining obligations. Use `(H _ hq).2 rfl` as an intermediate fact. Rewrite `this` using `[Ideal.mem_comap, notMem_maximalIdeal]`. Then use the resulting hypothesis.

Establish `h0 : ∀ a ∈ Ideal.span {1 - e}, φ a = 0`. Introduce `a ha`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Simplify using `[h1]`. Use `⟨e, he, hl, Ideal.Quotient.lift _ φ h0, ⟨fun r hr => ?_⟩, fun x => rfl⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Establish `hm` using `Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {1 - e})) Ideal.Quotient.mk_surjective (K := maximalIdeal _)`. Establish `h : (maximalIdeal _).comap (Ideal.Quotient.mk (Ideal.span {1 - e})) = (maximalIdeal D).comap φ`. Rewrite using `[← H _ hm, ← one_sub_mem_iff_notMem_of_isIdempotentElem he, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]`. Conclude with `zero_mem _`.

Rewrite using `[← notMem_maximalIdeal, ← Ideal.mem_comap, h, Ideal.mem_comap, notMem_maximalIdeal]`. Conclude with `hr`.
-/
theorem exists_local_factor {B S D : Type*} [CommRing B] [HenselianLocalRing B] [CommRing S]
    [Algebra B S] [Module.Finite B S] [CommRing D] [IsLocalRing D] (φ : S →+* D)
    (hφ : maximalIdeal B ≤ (maximalIdeal D).comap (φ.comp (algebraMap B S))) :
    ∃ e : S, IsIdempotentElem e ∧ IsLocalRing (S ⧸ Ideal.span {1 - e}) ∧
      ∃ ψ : (S ⧸ Ideal.span {1 - e}) →+* D, IsLocalHom ψ ∧
        ∀ x, ψ (Ideal.Quotient.mk _ x) = φ x := by
  have hq : ((maximalIdeal D).comap φ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B)
    rw [Ideal.comap_comap, ← (maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hφ]
    infer_instance
  obtain ⟨e, he, H⟩ := exists_idempotent_notMem_iff_of_henselian B ((maximalIdeal D).comap φ)
  have hl := isLocalRing_quotient_one_sub he _ H
  have h1 : φ e = 1 := by
    refine (IsIdempotentElem.iff_eq_one_of_isUnit ?_).1 (he.map φ)
    have := (H _ hq).2 rfl
    rwa [Ideal.mem_comap, notMem_maximalIdeal] at this
  have h0 : ∀ a ∈ Ideal.span {1 - e}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [h1]
  refine ⟨e, he, hl, Ideal.Quotient.lift _ φ h0, ⟨fun r hr => ?_⟩, fun x => rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hm := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {1 - e}))
    Ideal.Quotient.mk_surjective (K := maximalIdeal _)
  have h : (maximalIdeal _).comap (Ideal.Quotient.mk (Ideal.span {1 - e})) =
      (maximalIdeal D).comap φ := by
    rw [← H _ hm, ← one_sub_mem_iff_notMem_of_isIdempotentElem he, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    exact zero_mem _
  rw [← notMem_maximalIdeal, ← Ideal.mem_comap, h, Ideal.mem_comap, notMem_maximalIdeal]
  exact hr

/- English proof (translation)
Set `β₀ : C →+* R` to `π.comp (Algebra.TensorProduct.includeRight (R := T)).toRingHom`. Establish `hβ₀ : ∀ c, β₀ c = π (1 ⊗ₜ[T] c)` using `fun c => rfl`. Establish `hu : ∀ s : 𝔫.primeCompl, IsUnit (β₀ s)` using `fun s => by`. Use `IsUnit.of_map ψ _ ?_` and prove the remaining obligations. Rewrite using `[hβ₀, hψ]`.

Conclude with `(IsLocalization.map_units A s).map _`. Set `β : A →+* R` to `IsLocalization.lift hu`. Establish `hβ : ∀ c, β (algebraMap C A c) = π (1 ⊗ₜ[T] c)` using `fun c => IsLocalization.lift_eq hu c`. Establish `hψβ : ψ.comp β = algebraMap A (AdicCompletion (maximalIdeal A) A)`. Use `IsLocalization.ringHom_ext 𝔫.primeCompl (RingHom.ext fun c => ?_)` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, hβ, hψ]`. Establish `hβm : ∀ a ∈ maximalIdeal A, β a ∈ maximalIdeal R` using `fun a ha => by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[notMem_maximalIdeal]`. Establish `h2 : IsUnit ((ψ.comp β) a)` using `h.map ψ`.

Rewrite `h2` using `[hψβ]`. Conclude with `notMem_maximalIdeal.2 (IsUnit.of_map _ _ h2) ha`. Take `⟨χ, hχ, -⟩` from `exists_extend_adicCompletion β (maximalIdeal A) (maximalIdeal R) (k := 1) (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hβm)`. Establish `h₁ : ψ.comp χ = RingHom.id _`. Use `adicCompletion_ringHom_ext (maximalIdeal A).fg_of_isNoetherianRing (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (k := 1) ?_ ?_` and prove the remaining obligations.

Rewrite using `[pow_one, RingHom.comp_assoc, hχ, hψβ, AdicCompletion.maximalIdeal_eq_map]`. Rewrite using `[RingHom.comp_assoc, hχ, hψβ, RingHom.id_comp]`. Establish `hC : ∀ c : C, χ (ψ (π (1 ⊗ₜ[T] c))) = π (1 ⊗ₜ[T] c)` using `fun c => by`. Rewrite using `[hψ, ← RingHom.comp_apply, hχ, hβ]`. Establish `hT : ∀ t : T, (algebraMap T (AdicCompletion (maximalIdeal T) T) t) ⊗ₜ[T] (1 : C) = 1 ⊗ₜ[T] algebraMap T C t` using `fun t => by`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]`. Establish `hL : π.comp Algebra.TensorProduct.includeLeftRingHom = ((χ.comp ψ).comp π).comp Algebra.TensorProduct.includeLeftRingHom`. Use `adicCompletion_ringHom_ext (maximalIdeal T).fg_of_isNoetherianRing (maximalIdeal R) (k := 1) ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_one, Ideal.map_le_iff_le_comap]`. Introduce `t ht`.

Rewrite using `[Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, hT, ← hβ]`. Apply `hβm` to reduce the goal to its premises. Rewrite using `[IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]`. Conclude with `ht`. Use `RingHom.ext fun t => ?_` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, hT, hC]`. Establish `h₂ : ∀ x, χ (ψ (π x)) = π x`. Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a c`. Establish `e1 : a ⊗ₜ[T] c = (a ⊗ₜ[T] (1 : C)) * (1 ⊗ₜ[T] c)` using `by simp`. Establish `e2 : π (a ⊗ₜ[T] (1 : C)) = χ (ψ (π (a ⊗ₜ[T] (1 : C))))` using `congr($hL a)`. Rewrite using `[e1, map_mul, map_mul, map_mul, ← e2, hC]`.

Use `Function.bijective_iff_has_inverse.2 ⟨χ, fun r => ?_, fun y => congr($h₁ y)⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hπ r`. Conclude with `h₂ x`.
-/
theorem bijective_of_complete_quotient {T C A R : Type*} [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] [CommRing C] [Algebra T C] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (h𝔫 : 𝔫.comap (algebraMap T C) = maximalIdeal T)
    [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (π : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+* R) (hπ : Function.Surjective π)
    (ψ : R →+* AdicCompletion (maximalIdeal A) A) [IsLocalHom ψ]
    (hψ : ∀ c : C, ψ (π (1 ⊗ₜ[T] c)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c)) :
    Function.Bijective ψ := by
  let β₀ : C →+* R := π.comp (Algebra.TensorProduct.includeRight (R := T)).toRingHom
  have hβ₀ : ∀ c, β₀ c = π (1 ⊗ₜ[T] c) := fun c => rfl
  have hu : ∀ s : 𝔫.primeCompl, IsUnit (β₀ s) := fun s => by
    refine IsUnit.of_map ψ _ ?_
    rw [hβ₀, hψ]
    exact (IsLocalization.map_units A s).map _
  let β : A →+* R := IsLocalization.lift hu
  have hβ : ∀ c, β (algebraMap C A c) = π (1 ⊗ₜ[T] c) := fun c => IsLocalization.lift_eq hu c
  have hψβ : ψ.comp β = algebraMap A (AdicCompletion (maximalIdeal A) A) := by
    refine IsLocalization.ringHom_ext 𝔫.primeCompl (RingHom.ext fun c => ?_)
    simp only [RingHom.comp_apply, hβ, hψ]
  have hβm : ∀ a ∈ maximalIdeal A, β a ∈ maximalIdeal R := fun a ha => by
    by_contra h
    rw [notMem_maximalIdeal] at h
    have h2 : IsUnit ((ψ.comp β) a) := h.map ψ
    rw [hψβ] at h2
    exact notMem_maximalIdeal.2 (IsUnit.of_map _ _ h2) ha
  obtain ⟨χ, hχ, -⟩ := exists_extend_adicCompletion β (maximalIdeal A) (maximalIdeal R) (k := 1)
    (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hβm)
  have h₁ : ψ.comp χ = RingHom.id _ := by
    refine adicCompletion_ringHom_ext (maximalIdeal A).fg_of_isNoetherianRing
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (k := 1) ?_ ?_
    · rw [pow_one, RingHom.comp_assoc, hχ, hψβ, AdicCompletion.maximalIdeal_eq_map]
    · rw [RingHom.comp_assoc, hχ, hψβ, RingHom.id_comp]
  have hC : ∀ c : C, χ (ψ (π (1 ⊗ₜ[T] c))) = π (1 ⊗ₜ[T] c) := fun c => by
    rw [hψ, ← RingHom.comp_apply, hχ, hβ]
  have hT : ∀ t : T, (algebraMap T (AdicCompletion (maximalIdeal T) T) t) ⊗ₜ[T] (1 : C) =
      1 ⊗ₜ[T] algebraMap T C t := fun t => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]
  have hL : π.comp Algebra.TensorProduct.includeLeftRingHom =
      ((χ.comp ψ).comp π).comp Algebra.TensorProduct.includeLeftRingHom := by
    refine adicCompletion_ringHom_ext (maximalIdeal T).fg_of_isNoetherianRing
      (maximalIdeal R) (k := 1) ?_ ?_
    · rw [pow_one, Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply, hT, ← hβ]
      apply hβm
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]
      exact ht
    · refine RingHom.ext fun t => ?_
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, hT, hC]
  have h₂ : ∀ x, χ (ψ (π x)) = π x := by
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a c =>
      have e1 : a ⊗ₜ[T] c = (a ⊗ₜ[T] (1 : C)) * (1 ⊗ₜ[T] c) := by simp
      have e2 : π (a ⊗ₜ[T] (1 : C)) = χ (ψ (π (a ⊗ₜ[T] (1 : C)))) := congr($hL a)
      rw [e1, map_mul, map_mul, map_mul, ← e2, hC]
  refine Function.bijective_iff_has_inverse.2 ⟨χ, fun r => ?_, fun y => congr($h₁ y)⟩
  obtain ⟨x, rfl⟩ := hπ r
  exact h₂ x

/- English proof (translation)
Introduce `T C A _ _ _ _ _ _ _ _ _ 𝔫 _ _ h𝔫`. Establish `hCn : IsNoetherianRing C` using `IsNoetherianRing.of_finite T C`. Establish `hAn : IsNoetherianRing A` using `IsLocalization.isNoetherianRing 𝔫.primeCompl A hCn`. Establish `hTn` using `AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)`. Set `g : C →+* AdicCompletion (maximalIdeal A) A` to `(algebraMap A _).comp (algebraMap C A)`.

Establish `hg : maximalIdeal T ≤ (maximalIdeal _).comap (g.comp (algebraMap T C))`. Introduce `t ht`. Rewrite using `[Ideal.mem_comap, AdicCompletion.maximalIdeal_eq_map]`. Use `Ideal.mem_map_of_mem _ (?_ : algebraMap C A (algebraMap T C t) ∈ maximalIdeal A)` and prove the remaining obligations. Rewrite using `[IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]`.

Conclude with `ht`. Take `⟨α, hα, -⟩` from `exists_extend_adicCompletion (g.comp (algebraMap T C)) (maximalIdeal T) (maximalIdeal _) (k := 1) (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hg)`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφa, hφc⟩ : ∃ φ : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+* AdicCompletion (maximalIdeal A) A, φ.comp (algebraMap (AdicCompletion (maximalIdeal T) T) _) = α ∧ ∀ c, φ (1 ⊗ₜ[T] c) = g c := by`. Use `letI : Algebra T (AdicCompletion (maximalIdeal A) A) := (g.comp (algebraMap T C)).toAlgebra`. Set `α' : AdicCompletion (maximalIdeal T) T →ₐ[T] AdicCompletion (maximalIdeal A) A` to `{ α with commutes' := fun t => congr($hα t) }`.

Set `g' : C →ₐ[T] AdicCompletion (maximalIdeal A) A` to `{ g with commutes' := fun t => rfl }`. Use `⟨(Algebra.TensorProduct.lift α' g' fun _ _ => .all _ _).toRingHom, RingHom.ext fun a => ?_, fun c => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (a ⊗ₜ[T] 1) = α' a`. Rewrite using `[Algebra.TensorProduct.lift_tmul, map_one, mul_one]`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (1 ⊗ₜ[T] c) = g' c`.

Rewrite using `[Algebra.TensorProduct.lift_tmul, map_one, one_mul]`. Establish `hH` using `henselianLocalRing_of_henselianRing (AdicCompletion (maximalIdeal T) T)`. Take `⟨e, he, hl, ψ, hψl, hψ⟩` from `exists_local_factor (B := AdicCompletion (maximalIdeal T) T) φ (by`. Rewrite using `[hφa, AdicCompletion.maximalIdeal_eq_map (R := T), Ideal.map_le_iff_le_comap, Ideal.comap_comap, hα]`. Conclude with `hg)`.

Establish `hc` using `CompleteFiniteExtension.isAdicComplete_of_finite_local (AdicCompletion (maximalIdeal T) T) ((AdicCompletion (maximalIdeal T) T ⊗[T] C) ⧸ Ideal.span {1 - e})`. Establish `hψc : ∀ c : C, ψ (Ideal.Quotient.mk _ (1 ⊗ₜ[T] c)) = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c)` using `fun c => by`. Rewrite using `[hψ, hφc]`. Both sides reduce to the same expression. Establish `hb` using `bijective_of_complete_quotient 𝔫 h𝔫 _ Ideal.Quotient.mk_surjective ψ hψc`.

Take `⟨ε, hε⟩` from `exists_ringEquiv_prod_of_isIdempotentElem he`. Use `⟨_, inferInstance, ε.trans ((RingEquiv.ofBijective ψ hb).prodCongr (RingEquiv.refl _)), fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[← hψc, ← hε]`. Both sides reduce to the same expression.
-/
theorem exists_ringEquiv_completion_prod : ∀ (T C A : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [CommRing C] [Algebra T C] [Module.Finite T C] [CommRing A] [IsLocalRing A] [Algebra C A] (𝔫 : Ideal C) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫], 𝔫.comap (algebraMap T C) = maximalIdeal T → ∃ (S' : Type) (_ : CommRing S') (e : (AdicCompletion (maximalIdeal T) T ⊗[T] C) ≃+* (AdicCompletion (maximalIdeal A) A × S')), ∀ c : C, (e ((1 : AdicCompletion (maximalIdeal T) T) ⊗ₜ[T] c)).1 = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := by
  intro T C A _ _ _ _ _ _ _ _ _ 𝔫 _ _ h𝔫
  have hCn : IsNoetherianRing C := IsNoetherianRing.of_finite T C
  have hAn : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔫.primeCompl A hCn
  have hTn := AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  let g : C →+* AdicCompletion (maximalIdeal A) A := (algebraMap A _).comp (algebraMap C A)
  have hg : maximalIdeal T ≤ (maximalIdeal _).comap (g.comp (algebraMap T C)) := by
    intro t ht
    rw [Ideal.mem_comap, AdicCompletion.maximalIdeal_eq_map]
    refine Ideal.mem_map_of_mem _ (?_ : algebraMap C A (algebraMap T C t) ∈ maximalIdeal A)
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔫, ← Ideal.mem_comap, h𝔫]
    exact ht
  obtain ⟨α, hα, -⟩ := exists_extend_adicCompletion (g.comp (algebraMap T C)) (maximalIdeal T)
    (maximalIdeal _) (k := 1) (by rw [pow_one, Ideal.map_le_iff_le_comap]; exact hg)
  obtain ⟨φ, hφa, hφc⟩ : ∃ φ : (AdicCompletion (maximalIdeal T) T ⊗[T] C) →+*
      AdicCompletion (maximalIdeal A) A,
      φ.comp (algebraMap (AdicCompletion (maximalIdeal T) T) _) = α ∧
        ∀ c, φ (1 ⊗ₜ[T] c) = g c := by
    letI : Algebra T (AdicCompletion (maximalIdeal A) A) := (g.comp (algebraMap T C)).toAlgebra
    let α' : AdicCompletion (maximalIdeal T) T →ₐ[T] AdicCompletion (maximalIdeal A) A :=
      { α with commutes' := fun t => congr($hα t) }
    let g' : C →ₐ[T] AdicCompletion (maximalIdeal A) A := { g with commutes' := fun t => rfl }
    refine ⟨(Algebra.TensorProduct.lift α' g' fun _ _ => .all _ _).toRingHom,
      RingHom.ext fun a => ?_, fun c => ?_⟩
    · change Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (a ⊗ₜ[T] 1) = α' a
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    · change Algebra.TensorProduct.lift α' g' (fun _ _ => .all _ _) (1 ⊗ₜ[T] c) = g' c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hH := henselianLocalRing_of_henselianRing (AdicCompletion (maximalIdeal T) T)
  obtain ⟨e, he, hl, ψ, hψl, hψ⟩ := exists_local_factor (B := AdicCompletion (maximalIdeal T) T) φ
    (by
      rw [hφa, AdicCompletion.maximalIdeal_eq_map (R := T), Ideal.map_le_iff_le_comap,
        Ideal.comap_comap, hα]
      exact hg)
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local
    (AdicCompletion (maximalIdeal T) T)
    ((AdicCompletion (maximalIdeal T) T ⊗[T] C) ⧸ Ideal.span {1 - e})
  have hψc : ∀ c : C, ψ (Ideal.Quotient.mk _ (1 ⊗ₜ[T] c)) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A c) := fun c => by
    rw [hψ, hφc]; rfl
  have hb := bijective_of_complete_quotient 𝔫 h𝔫 _ Ideal.Quotient.mk_surjective ψ hψc
  obtain ⟨ε, hε⟩ := exists_ringEquiv_prod_of_isIdempotentElem he
  refine ⟨_, inferInstance, ε.trans ((RingEquiv.ofBijective ψ hb).prodCongr (RingEquiv.refl _)),
    fun c => ?_⟩
  rw [← hψc, ← hε]
  rfl

end GlobalTheory.CompletionFactor
