import Mathlib

namespace GlobalTheory.ValuationExtensionExistence

/- English proof (translation)
Establish `: (RingHom.ker ev).IsPrime` using `RingHom.ker_isPrime ev`. Take `⟨Q, -, hQ, hQp⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := R) (RingHom.ker ev) ⊥ (by`. Rewrite using `[Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective V R)]`. Conclude with `bot_le)`. Use `hQ` as an intermediate fact.

Establish `: Q.LiesOver (RingHom.ker ev)` using `⟨hQp.symm⟩`. Set `: Algebra (V ⧸ RingHom.ker ev) K` to `(RingHom.kerLift ev).toAlgebra`. Establish `: Module.IsTorsionFree (V ⧸ RingHom.ker ev) K` using `Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective ev)`. Establish `: Module.IsTorsionFree (V ⧸ RingHom.ker ev) (R ⧸ Q)` using `Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)`. Establish `: Algebra.IsIntegral (V ⧸ RingHom.ker ev) (R ⧸ Q)` using `Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker ev)`.

Establish `: Algebra.IsAlgebraic (V ⧸ RingHom.ker ev) (R ⧸ Q)` using `Algebra.IsIntegral.isAlgebraic`. Set `f : R ⧸ Q →ₐ[V ⧸ RingHom.ker ev] K` to `IsAlgClosed.lift`. Use `⟨(f : R ⧸ Q →+* K).comp (Ideal.Quotient.mk Q), ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Establish `h` using `f.commutes (Ideal.Quotient.mk (RingHom.ker ev) v)`.

Rewrite `h` using `[Ideal.Quotient.algebraMap_mk_of_liesOver]`. Conclude with `h.trans (RingHom.kerLift_mk ev v)`.
-/
theorem exists_extension {V R K : Type} [CommRing V] [CommRing R] [IsDomain R] [Field K]
    [IsAlgClosed K] [Algebra V R] [Algebra.IsIntegral V R] [FaithfulSMul V R] (ev : V →+* K) :
    ∃ ev₁ : R →+* K, ev₁.comp (algebraMap V R) = ev := by
  classical

  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R) (RingHom.ker ev) ⊥ (by
    rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective V R)]
    exact bot_le)
  have := hQ
  have : Q.LiesOver (RingHom.ker ev) := ⟨hQp.symm⟩

  let : Algebra (V ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective ev)
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  have : Algebra.IsIntegral (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker ev)
  have : Algebra.IsAlgebraic (V ⧸ RingHom.ker ev) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : R ⧸ Q →ₐ[V ⧸ RingHom.ker ev] K := IsAlgClosed.lift
  refine ⟨(f : R ⧸ Q →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext v
  have h := f.commutes (Ideal.Quotient.mk (RingHom.ker ev) v)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h
  exact h.trans (RingHom.kerLift_mk ev v)

/- English proof (translation)
Introduce `V R K _ _ _ _ _ _ _ _ ρ hinj hfin`. Establish `hint : ρ.IsIntegral` using `hfin.to_isIntegral`. Use `⟨?_, fun ev => ?_⟩` and prove the remaining obligations. Use `((IsLocalRing.local_hom_TFAE ρ).out 4 0).mp ?_` and prove the remaining obligations. Conclude with `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ρ hint _)`.

Set `` to `ρ.toAlgebra`. Establish `: Algebra.IsIntegral V R` using `⟨hint⟩`. Establish `: FaithfulSMul V R` using `(faithfulSMul_iff_algebraMap_injective V R).2 hinj`. Conclude with `exists_extension ev`.
-/
theorem main : ∀ (V R K : Type) [inst : CommRing V] [IsDomain V] [IsLocalRing V]
    [inst_3 : CommRing R] [IsDomain R] [IsLocalRing R] [inst_6 : Field K] [IsAlgClosed K]
    (ρ : V →+* R), Function.Injective (⇑ρ : V → R) → RingHom.Finite ρ →
      IsLocalHom ρ ∧ ∀ (ev : V →+* K), ∃ (ev₁ : R →+* K), RingHom.comp ev₁ ρ = ev := by
  intro V R K _ _ _ _ _ _ _ _ ρ hinj hfin
  have hint : ρ.IsIntegral := hfin.to_isIntegral
  refine ⟨?_, fun ev => ?_⟩
  · refine ((IsLocalRing.local_hom_TFAE ρ).out 4 0).mp ?_
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ρ hint _)
  · let := ρ.toAlgebra
    have : Algebra.IsIntegral V R := ⟨hint⟩
    have : FaithfulSMul V R := (faithfulSMul_iff_algebraMap_injective V R).2 hinj
    exact exists_extension ev

end GlobalTheory.ValuationExtensionExistence
