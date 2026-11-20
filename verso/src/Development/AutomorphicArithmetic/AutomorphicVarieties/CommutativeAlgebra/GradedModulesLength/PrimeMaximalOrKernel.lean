import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

/- English proof (translation)
Use `haveI : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)`. Establish `hcomap : ∀ a : O, algebraMap O (B ⧸ P) a = 0 ↔ algebraMap O B a ∈ P`. Introduce `a`. Rewrite using `[IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`. Distinguish the cases in `hc : ∃ c : O, c ≠ 0 ∧ algebraMap O B c ∈ P`.

Take `⟨c, hc0, hcP⟩` from `hc left`. Apply `IsLocalRing.eq_maximalIdeal` to reduce the goal to its premises. Establish `hQ : (P.comap (algebraMap O B)).IsMaximal`. Apply `Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _)` to reduce the goal to its premises. Introduce `h`.

Establish `hmem : c ∈ P.comap (algebraMap O B)` using `hcP`. Rewrite `hmem` using `[h]`. Conclude with `hc0 ((Submodule.mem_bot O).1 hmem)`. Establish `hbot : (⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P)) = P.comap (algebraMap O B)`. Use extensionality with `a`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap, hcomap]`. Use `haveI : (⊥ : Ideal (B ⧸ P)).IsPrime := Ideal.bot_prime`. Establish `hmax` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) (⊥ : Ideal (B ⧸ P)) (hbot ▸ hQ)`. Rewrite using `[Ideal.Quotient.maximal_ideal_iff_isField_quotient]`. Conclude with `Ring.isField_iff_maximal_bot.2 hmax`.

Use `push_neg at hc right`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (algebraMap O (B ⧸ P))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Assume the negation of the conclusion as `h0`. Conclude with `hc a h0 ((hcomap a).1 ha)`. Use `haveI : Module.IsTorsionFree O (B ⧸ P) := NoZeroSMulDivisors.iff_algebraMap_injective.2 hinj`. Use `haveI : Module.IsTorsionFree O K := NoZeroSMulDivisors.iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective O K)`. Use `haveI : Algebra.IsAlgebraic O (B ⧸ P) := Algebra.IsIntegral.isAlgebraic`.

Set `τ : (B ⧸ P) →ₐ[O] K` to `IsAlgClosed.lift`. Use `⟨τ.comp (Ideal.Quotient.mkₐ O P), ?_⟩` and prove the remaining obligations. Establish `hτ : RingHom.ker (τ : (B ⧸ P) →+* K) = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := O)` to reduce the goal to its premises. Use extensionality with `a`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]`. Express the relevant statement in the definitionally equal form `τ (algebraMap O (B ⧸ P) a) = 0 ↔ a = 0`. Rewrite using `[AlgHom.commutes]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `FaithfulSMul.algebraMap_injective O K (h.trans (map_zero _).symm)`. Introduce `h`. Rewrite using `[h, map_zero]`. Establish `hτi : Function.Injective τ` using `(RingHom.injective_iff_ker_eq_bot (τ : (B ⧸ P) →+* K)).2 hτ`. Use extensionality with `b`.

Rewrite using `[RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `τ (Ideal.Quotient.mk P b) = 0 ↔ b ∈ P`. Rewrite using `[map_eq_zero_iff τ hτi, Ideal.Quotient.eq_zero_iff_mem]`.
-/
private theorem prime_maximal_or_kernel (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (P : Ideal B) [hP : P.IsPrime]
    [Module.Finite O (B ⧸ P)] :
    P = maximalIdeal B ∨ ((∀ c : O, c ≠ 0 → algebraMap O B c ∉ P) ∧ ∃ σ : B →ₐ[O] K, RingHom.ker σ = P) := by
  classical
  haveI : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  have hcomap : ∀ a : O, algebraMap O (B ⧸ P) a = 0 ↔ algebraMap O B a ∈ P := by
    intro a
    rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  by_cases hc : ∃ c : O, c ≠ 0 ∧ algebraMap O B c ∈ P
  · obtain ⟨c, hc0, hcP⟩ := hc
    left
    apply IsLocalRing.eq_maximalIdeal
    have hQ : (P.comap (algebraMap O B)).IsMaximal := by
      apply Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _)
      intro h
      have hmem : c ∈ P.comap (algebraMap O B) := hcP
      rw [h] at hmem
      exact hc0 ((Submodule.mem_bot O).1 hmem)
    have hbot : (⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P)) = P.comap (algebraMap O B) := by
      ext a
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap, hcomap]
    haveI : (⊥ : Ideal (B ⧸ P)).IsPrime := Ideal.bot_prime
    have hmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) (⊥ : Ideal (B ⧸ P)) (hbot ▸ hQ)
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact Ring.isField_iff_maximal_bot.2 hmax
  · push_neg at hc
    right
    refine ⟨hc, ?_⟩
    have hinj : Function.Injective (algebraMap O (B ⧸ P)) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact hc a h0 ((hcomap a).1 ha)
    haveI : Module.IsTorsionFree O (B ⧸ P) := NoZeroSMulDivisors.iff_algebraMap_injective.2 hinj
    haveI : Module.IsTorsionFree O K :=
      NoZeroSMulDivisors.iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective O K)
    haveI : Algebra.IsAlgebraic O (B ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let τ : (B ⧸ P) →ₐ[O] K := IsAlgClosed.lift
    refine ⟨τ.comp (Ideal.Quotient.mkₐ O P), ?_⟩
    have hτ : RingHom.ker (τ : (B ⧸ P) →+* K) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O)
      ext a
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      change τ (algebraMap O (B ⧸ P) a) = 0 ↔ a = 0
      rw [AlgHom.commutes]
      constructor
      · intro h
        exact FaithfulSMul.algebraMap_injective O K (h.trans (map_zero _).symm)
      · intro h
        rw [h, map_zero]
    have hτi : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot (τ : (B ⧸ P) →+* K)).2 hτ
    ext b
    rw [RingHom.mem_ker]
    change τ (Ideal.Quotient.mk P b) = 0 ↔ b ∈ P
    rw [map_eq_zero_iff τ hτi, Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Introduce `O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x I hM P hP hIP`. Set `φ : 𝒜 0 →ₗ[O] A ⧸ I` to `(Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ (𝒜 0).subtype`. Establish `hr : (LinearMap.range φ).FG`. Establish `: LinearMap.range φ = (𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`.

Rewrite using `[this]`. Conclude with `hM`. Use `haveI : Module.Finite O (LinearMap.range φ) := Module.Finite.iff_fg.2 hr`. Use `haveI : Module.Finite O (𝒜 0 ⧸ LinearMap.ker φ) := Module.Finite.equiv φ.quotKerEquivRange.symm`. Set `ψ : 𝒜 0 →ₗ[O] (𝒜 0 ⧸ P)` to `(Ideal.Quotient.mkₐ O P).toLinearMap`.

Establish `hk : LinearMap.ker φ ≤ LinearMap.ker ψ` using `fun b hb => Ideal.Quotient.eq_zero_iff_mem.2 (hIP b (Ideal.Quotient.eq_zero_iff_mem.1 hb))`. Use `haveI : Module.Finite O (𝒜 0 ⧸ P) := by`. Use `Module.Finite.of_surjective ((LinearMap.ker φ).liftQ ψ hk) fun y => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Submodule.Quotient.mk b, rfl⟩`.

Conclude with `prime_maximal_or_kernel O K (𝒜 0) P`.
-/
theorem UpperTheory.V.Alg.M.emb_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I →
    ∀ P : Ideal (𝒜 0), P.IsPrime → (∀ b : 𝒜 0, (b : A) ∈ I → b ∈ P) →
      (P = maximalIdeal (𝒜 0) ∨ ((∀ c : O, c ≠ 0 → algebraMap O (𝒜 0) c ∉ P) ∧ ∃ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = P)) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x I hM P hP hIP
  let φ : 𝒜 0 →ₗ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ (𝒜 0).subtype
  have hr : (LinearMap.range φ).FG := by
    have : LinearMap.range φ = (𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [this]; exact hM
  haveI : Module.Finite O (LinearMap.range φ) := Module.Finite.iff_fg.2 hr
  haveI : Module.Finite O (𝒜 0 ⧸ LinearMap.ker φ) := Module.Finite.equiv φ.quotKerEquivRange.symm
  let ψ : 𝒜 0 →ₗ[O] (𝒜 0 ⧸ P) := (Ideal.Quotient.mkₐ O P).toLinearMap
  have hk : LinearMap.ker φ ≤ LinearMap.ker ψ := fun b hb =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hIP b (Ideal.Quotient.eq_zero_iff_mem.1 hb))
  haveI : Module.Finite O (𝒜 0 ⧸ P) := by
    refine Module.Finite.of_surjective ((LinearMap.ker φ).liftQ ψ hk) fun y => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  exact prime_maximal_or_kernel O K (𝒜 0) P
