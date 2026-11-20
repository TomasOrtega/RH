import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveAdicCompletionMapOfFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement

open IsLocalRing

namespace GlobalTheory.CompletionReduced

/- English proof (translation)
Rewrite using `[Ideal.jacobson, le_sInf_iff]`. Introduce and unpack `M ⟨-, hM⟩`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Conclude with `hI.trans (sInf_le ⟨bot_le, hf M hM⟩)`.
-/
theorem map_le_jacobson_of_comap_isMaximal {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : ∀ M : Ideal B, M.IsMaximal → (M.comap f).IsMaximal) (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) : I.map f ≤ Ideal.jacobson (⊥ : Ideal B) := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro M ⟨-, hM⟩
  rw [Ideal.map_le_iff_le_comap]
  exact hI.trans (sInf_le ⟨bot_le, hf M hM⟩)

/- English proof (translation)
Proceed by induction on `e using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h0 (by simp)`. Consider the case `coe k`. Proceed by induction on `k using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞)` using `h`. Rewrite `h'` using `[WithBot.coe_le_coe, top_add]`. Conclude with `absurd h' (by simp)`. Consider the case `coe k`.

Use `⟨k, ?_, le_rfl⟩` and prove the remaining obligations. Establish `: ((k + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)` using `by exact_mod_cast h`. Conclude with `this` after adjusting the coercions.
-/
theorem exists_lt_of_add_one_le (e : WithBot ℕ∞) (n : ℕ) (h0 : 0 ≤ e) (h : e + 1 ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, m < n ∧ e ≤ (m : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe, top_add] at h'
      exact absurd h' (by simp)
    | coe k =>
      refine ⟨k, ?_, le_rfl⟩
      have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      exact_mod_cast this

/- English proof (translation)
Use `haveI : IsNoetherianRing N := Algebra.EssFiniteType.isNoetherianRing ℤ N`. Distinguish the cases in `hbot : I = ⊥`. Substitute `hbot` using the available equality. Conclude with `isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.toRingEquiv.toRingHom (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.injective`. Take `⟨x, hxI, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`.

Set `R` to `AdicCompletion I N`. Use `haveI : IsNoetherianRing R := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian N I`. Use `haveI : Module.Flat N R := AdicCompletion.flat_of_isNoetherian I`. Establish `hxR : algebraMap N R x ∈ nonZeroDivisors R`. Establish `hxA : IsSMulRegular N x` using `IsSMulRegular.of_ne_zero hx0`.

Establish `h : IsSMulRegular R (algebraMap N R x)` using `hxA.of_flat`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `y hy`. Use `h ?_` and prove the remaining obligations. Simplify `hy` using `[smul_eq_mul, mul_comm]`.

Establish `hxjac : algebraMap N R x ∈ Ideal.jacobson (⊥ : Ideal R)`. Establish `h1 : IsAdicComplete I R` using `AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)`. Establish `h2 : IsAdicComplete (I.map (algebraMap N R)) R` using `(IsAdicComplete.map_algebraMap_iff _ _).2 h1`. Conclude with `IsAdicComplete.le_jacobson_bot (I.map (algebraMap N R)) (Ideal.mem_map_of_mem _ hxI)`. Establish `hredq : ∀ q : Ideal N, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap N R))`.

Introduce `q hq hxq`. Take `⟨e⟩` from `GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv N I q`. Use `haveI : IsDomain (N ⧸ q) := Ideal.Quotient.isDomain q`. Use `haveI : Algebra.EssFiniteType N (N ⧸ q) := inferInstance`. Use `haveI hess : @Algebra.EssFiniteType ℤ (N ⧸ q) _ _ (Ring.toIntAlgebra _) := by`.

Use `letI := Ring.toIntAlgebra (N ⧸ q)`. Use `haveI : IsScalarTower ℤ N (N ⧸ q) := .of_algebraMap_eq fun z => by simp`. Conclude with `Algebra.EssFiniteType.comp ℤ N (N ⧸ q)`. Establish `hj : I.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (N ⧸ q))` using `map_le_jacobson_of_comap_isMaximal _ (fun M hM => Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) I hIjac`. Establish `hd1 : ringKrullDim (N ⧸ q) + 1 ≤ (n : WithBot ℕ∞)`.

Establish `h1` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)`. Establish `h2 : ringKrullDim (N ⧸ q) ≤ ringKrullDim (N ⧸ Ideal.span {x})` using `ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective (by rwa [Ideal.span_singleton_le_iff_mem]))`. Conclude with `((add_le_add h2 le_rfl).trans h1).trans hdimN`. Take `⟨m, hmn, hm⟩` from `exists_lt_of_add_one_le _ n ringKrullDim_nonneg_of_nontrivial hd1`. Use `haveI := ih m hmn (N ⧸ q) hm _ hj`.

Conclude with `isReduced_of_injective e.toRingHom e.injective`. Use `GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes R (algebraMap N R x) hxR hxjac ?_` and prove the remaining obligations. Introduce `P _ hP`. Take `⟨h1, -⟩` from `GlobalTheory.T.associated_prime_localization_dvr N R x hx0 hredq P hP`. Conclude with `h1`.
-/
theorem isReduced_of_normal (n : ℕ)
    (ih : ∀ m < n, ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      ringKrullDim D ≤ (m : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
        IsReduced (AdicCompletion J D))
    (N : Type) [CommRing N] [IsDomain N] [IsIntegrallyClosed N] [Algebra.EssFiniteType ℤ N]
    (hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞)) (I : Ideal N)
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal N)) : IsReduced (AdicCompletion I N) := by
  haveI : IsNoetherianRing N := Algebra.EssFiniteType.isNoetherianRing ℤ N
  by_cases hbot : I = ⊥
  · subst hbot
    exact isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.toRingEquiv.toRingHom
      (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.injective
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let R := AdicCompletion I N
  haveI : IsNoetherianRing R := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian N I
  haveI : Module.Flat N R := AdicCompletion.flat_of_isNoetherian I
  have hxR : algebraMap N R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular N x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap N R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hxjac : algebraMap N R x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    have h1 : IsAdicComplete I R := AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)
    have h2 : IsAdicComplete (I.map (algebraMap N R)) R := (IsAdicComplete.map_algebraMap_iff _ _).2 h1
    exact IsAdicComplete.le_jacobson_bot (I.map (algebraMap N R)) (Ideal.mem_map_of_mem _ hxI)
  have hredq : ∀ q : Ideal N, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap N R)) := by
    intro q hq hxq
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv N I q
    haveI : IsDomain (N ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType N (N ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (N ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (N ⧸ q)
      haveI : IsScalarTower ℤ N (N ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ N (N ⧸ q)
    have hj : I.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (N ⧸ q)) :=
      map_le_jacobson_of_comap_isMaximal _
        (fun M hM => Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) I hIjac
    have hd1 : ringKrullDim (N ⧸ q) + 1 ≤ (n : WithBot ℕ∞) := by
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
      have h2 : ringKrullDim (N ⧸ q) ≤ ringKrullDim (N ⧸ Ideal.span {x}) :=
        ringKrullDim_le_of_surjective _
          (Ideal.Quotient.factor_surjective (by rwa [Ideal.span_singleton_le_iff_mem]))
      exact ((add_le_add h2 le_rfl).trans h1).trans hdimN
    obtain ⟨m, hmn, hm⟩ := exists_lt_of_add_one_le _ n ringKrullDim_nonneg_of_nontrivial hd1
    haveI := ih m hmn (N ⧸ q) hm _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  refine GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes R (algebraMap N R x) hxR hxjac ?_
  intro P _ hP
  obtain ⟨h1, -⟩ := GlobalTheory.T.associated_prime_localization_dvr N R x hx0 hredq P hP
  exact h1

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `D _ _ _ hdim J hJ`. Use `haveI : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D`.

Set `N` to `integralClosure D (FractionRing D)`. Use `haveI : Module.Finite D N := GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain D`. Use `haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing D)`. Establish `hinj : Function.Injective (algebraMap D N)`. Introduce `a b hab`.

Use `congrArg (fun y : N => (y : FractionRing D)) hab` as an intermediate fact. Conclude with `IsFractionRing.injective D (FractionRing D) this`. Establish `hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞)`. Rewrite using `[ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj]`. Conclude with `hdim`.

Use `haveI : Algebra.EssFiniteType D N := inferInstance`. Use `haveI hessN : @Algebra.EssFiniteType ℤ N _ _ (Ring.toIntAlgebra _) := by`. Use `letI := Ring.toIntAlgebra N`. Use `haveI : IsScalarTower ℤ D N := .of_algebraMap_eq fun z => by simp`. Conclude with `Algebra.EssFiniteType.comp ℤ D N`.

Establish `hIjac : J.map (algebraMap D N) ≤ Ideal.jacobson (⊥ : Ideal N)` using `map_le_jacobson_of_comap_isMaximal _ (fun M hM => Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M) J hJ`. Take `⟨f, hf⟩` from `GlobalTheory.T.exists_injective_adicCompletion_map_of_finite D N hinj J`. Use `haveI := isReduced_of_normal n ih N hdimN _ hIjac`. Conclude with `isReduced_of_injective f hf`.
-/
theorem isReduced_of_dim_le : ∀ (n : ℕ) (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
    ringKrullDim D ≤ (n : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
      IsReduced (AdicCompletion J D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ _ _ hdim J hJ
  haveI : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D

  let N := integralClosure D (FractionRing D)
  haveI : Module.Finite D N := GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain D
  haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing D)
  have hinj : Function.Injective (algebraMap D N) := by
    intro a b hab
    have := congrArg (fun y : N => (y : FractionRing D)) hab
    exact IsFractionRing.injective D (FractionRing D) this
  have hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞) := by
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj]; exact hdim
  haveI : Algebra.EssFiniteType D N := inferInstance
  haveI hessN : @Algebra.EssFiniteType ℤ N _ _ (Ring.toIntAlgebra _) := by
    letI := Ring.toIntAlgebra N
    haveI : IsScalarTower ℤ D N := .of_algebraMap_eq fun z => by simp
    exact Algebra.EssFiniteType.comp ℤ D N
  have hIjac : J.map (algebraMap D N) ≤ Ideal.jacobson (⊥ : Ideal N) :=
    map_le_jacobson_of_comap_isMaximal _
      (fun M hM => Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M) J hJ
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_injective_adicCompletion_map_of_finite D N hinj J
  haveI := isReduced_of_normal n ih N hdimN _ hIjac
  exact isReduced_of_injective f hf

/- English proof (translation)
Introduce `D _ _ _ J hJ`. Establish `hlt` using `GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int D`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim D ≤ (m : WithBot ℕ∞) := by`. Generalize the expression as in `ringKrullDim D = e at hlt ⊢`. Proceed by induction on `e using WithBot.recBotCoe with`.

Consider the case `bot => exact ⟨0, bot_le⟩`. Consider the case `coe k`. Proceed by induction on `k using ENat.recTopCoe with`. Consider the case `top => exact absurd hlt (by simp)`. Consider the case `coe k => exact ⟨k, le_rfl⟩`.

Conclude with `isReduced_of_dim_le m D hm J hJ`.
-/
theorem isReduced_adicCompletion : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D]
    (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  intro D _ _ _ J hJ
  have hlt := GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int D
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim D ≤ (m : WithBot ℕ∞) := by
    generalize ringKrullDim D = e at hlt ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe k =>
      induction k using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe k => exact ⟨k, le_rfl⟩
  exact isReduced_of_dim_le m D hm J hJ

end GlobalTheory.CompletionReduced
