import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmConjugationOnPrimesProperties
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmExtensionAdelesStandardModelDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdeleIdemPrimeCriterion
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.PrimeIdemExists

/- English proof (translation)
Use `⟨(⟨fun w => if w = v then 1 else 0, ?_⟩ : RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite), ?_, ?_⟩` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun w => ?_ beta_reduce` and prove the remaining obligations. Distinguish the cases in `h : w = v`. Rewrite using `[if_pos h]`. Conclude with `one_mem (w.adicCompletionIntegers K)`.

Rewrite using `[if_neg h]`. Conclude with `zero_mem (w.adicCompletionIntegers K)`. Conclude with `if_pos rfl`. Introduce `w hw`. Conclude with `if_neg hw`.
-/
theorem exists_indicator (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ a : FiniteAdeleRing (𝓞 K) K, a v = 1 ∧ ∀ w, w ≠ v → a w = 0 := by
  refine ⟨(⟨fun w => if w = v then 1 else 0, ?_⟩ :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite), ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun w => ?_
    beta_reduce
    by_cases h : w = v
    · rw [if_pos h]; exact one_mem (w.adicCompletionIntegers K)
    · rw [if_neg h]; exact zero_mem (w.adicCompletionIntegers K)
  · exact if_pos rfl
  · intro w hw; exact if_neg hw

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (ε ⊗ₜ[F] (1 : E)) = ε ⊗ₜ[F] (1 : E)`. Simplify using the standard rewrite rules.
-/
theorem cA_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ε : AF F) :
    cA σ (algebraMap (AF F) (AE F E) ε) = algebraMap (AF F) (AE F E) ε := by
  change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (ε ⊗ₜ[F] (1 : E)) = ε ⊗ₜ[F] (1 : E)
  simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] (σ x)`. Simplify using the standard rewrite rules.
-/
theorem cA_incA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : E) :
    cA σ (incA F E x) = incA F E (σ x) := by
  change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] (σ x)
  simp

/- English proof (translation)
The claim follows from `Prod.ext h1 (DFunLike.ext _ _ h2)`.
-/
theorem prod_ext {K : Type} [Field K] [NumberField K] {M : Type} {a b : M × FiniteAdeleRing (𝓞 K) K}
    (h1 : a.1 = b.1) (h2 : ∀ P, a.2 P = b.2 P) : a = b :=
  Prod.ext h1 (DFunLike.ext _ _ h2)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ P`. Take `⟨c, hcc, -, hcmem, hcund, -, hcint, -⟩` from `GlobalTheory.cmConjugation_on_primes_adeles_idempotents F E σ hσ`. Take `⟨Φ, hΦ1, hΦ2, hΦ3, -, -⟩` from `GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ`. Establish `crit` using `GlobalTheory.adele_idem_prime_criterion F E Φ hΦ1 hΦ2 hΦ3`. Take `⟨α, hα1, hα0⟩` from `exists_indicator F (P.under (𝓞 F))`.

Establish `hε : IsPlaceIdem F (P.under (𝓞 F)) (pairA F 0 α)` using `⟨α, rfl, hα1, hα0⟩`. Use `set ε := pairA F 0 α with hεdef`. Use `set η := algebraMap (AF F) (AE F E) ε with hη`. Take `⟨hη1, hη2⟩` from `hΦ3 _ _ hε`. Rewrite `hη1`, `hη2` using `[← hη]`.

Establish `hη3 : ∀ Q, (Φ η).2 Q = if Q = P ∨ Q = c P then 1 else 0`. Introduce `Q`. Rewrite using `[hη2 Q]`. Conclude with `if_congr (eq_comm.trans (hcund P Q)) rfl rfl`. Establish `mulap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a * b).2 Q = a.2 Q * b.2 Q` using `fun _ _ _ => rfl`.

Establish `addap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a + b).2 Q = a.2 Q + b.2 Q` using `fun _ _ _ => rfl`. Distinguish the cases in `hP : c P = P`. Establish `hηη : η * η = η`. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul]`.

Use `prod_ext ?_ fun Q => ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_mul, hη1, mul_zero]`. Apply the tactic sequence `rw [mulap, hη3]; split_ifs <;> simp`. Use `⟨η, η, Or.inr ⟨rfl, ⟨_, ε, hε, rfl⟩, ?_⟩⟩` and prove the remaining obligations. Use `(crit η P _ ε hε hηη hηη).2 ⟨hη1, ?_, fun Q hQ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hη3, if_pos (Or.inl rfl)]`. Rewrite using `[hη3, if_neg]`. Rewrite using `[hP]`. Simplify using `using hQ`. Take `⟨β, hβ1, hβ0⟩` from `exists_indicator E P set e : AE F E := Φ.symm (0, β) with he`.

Establish `hΦe : Φ e = (0, β)` using `Φ.apply_symm_apply _`. Establish `he1 : (Φ e).1 = 0` using `by rw [hΦe]`. Establish `heP : (Φ e).2 P = 1` using `by rw [hΦe]; exact hβ1`. Establish `he0 : ∀ Q, Q ≠ P → (Φ e).2 Q = 0` using `by rw [hΦe]; exact hβ0`. Establish `hee : e * e = e`.

Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul]`. Use `prod_ext ?_ fun Q => ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_mul, he1, mul_zero]`. Rewrite using `[mulap]`.

Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[heP, mul_one]`. Rewrite using `[he0 Q hQ, mul_zero]`. Establish `heη : e * η = e`.

Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul]`. Use `prod_ext ?_ fun Q => ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_mul, he1, zero_mul]`. Rewrite using `[mulap]`.

Distinguish the cases in `hQ : Q = P`. Rewrite using `[hη3, if_pos (Or.inl hQ), mul_one]`. Rewrite using `[he0 Q hQ, zero_mul]`. Establish `hcr` using `(crit e P _ ε hε hee heη).2 ⟨he1, heP, he0⟩`. Establish `hσσ : ∀ x : E, σ (σ x) = x`.

Introduce `x`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hσ.2.2.2, hσ.2.2.2, star_star]`. Establish `hcr' : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ (c P).asIdeal ↔ finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E)`.

Introduce `x hx`. Establish `hint : IsIntegral ℤ (σ (x : E))` using `(RingOfIntegers.isIntegral_coe x).map (σ.toRingHom.toIntAlgHom)`. Set `y : 𝓞 E` to `⟨σ (x : E), hint⟩`. Establish `hy : (y : E) = σ (x : E)` using `rfl`. Establish `hxy : (x : E) = σ (y : E)` using `by rw [hy, hσσ]`.

Establish `hy0 : y ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hxy, h0]`.

Simplify using the standard rewrite rules. Rewrite using `[(hcmem P y x hxy).1, hcr y hy0, ← hcint, map_mul (cA σ), cA_incA, map_inv₀, ← hxy]`. Establish `hee' : cA σ e * cA σ e = cA σ e` using `by rw [← map_mul, hee]`. Establish `heη' : cA σ e * η = cA σ e`. Use `congrArg (cA σ) heη` as an intermediate fact.

Rewrite `this` using `[map_mul, hη, cA_algebraMap]`. Then use the resulting hypothesis. Take `⟨hc1, hcP, hc0⟩` from `(crit (cA σ e) (c P) _ ε hε hee' heη').1 hcr'`. Use `⟨e, e + cA σ e, Or.inl ⟨⟨⟨hee, ?_, _, ε, hε, ?_⟩, hcr⟩, rfl⟩⟩` and prove the remaining obligations. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_zero]`.

Use `prod_ext ?_ fun Q => ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_mul, he1, zero_mul]`. Both sides reduce to the same expression. Rewrite using `[mulap]`. Distinguish the cases in `hQ : Q = P`.

Rewrite using `[hc0 Q (by rw [hQ]; exact fun h => hP h.symm), mul_zero]; rfl`. Rewrite using `[he0 Q hQ, zero_mul]`. Both sides reduce to the same expression. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_add, ← hη]`.

Use `prod_ext ?_ fun Q => ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_add, he1, hc1, hη1, add_zero]`. Rewrite using `[addap, hη3]`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality.

Rewrite using `[heP, hc0 _ (fun h => hP h.symm), add_zero, if_pos (Or.inl rfl)]`. Distinguish the cases in `hQ' : Q = c P`. Substitute `hQ'` using the available equality. Rewrite using `[he0 _ hQ, hcP, zero_add, if_pos (Or.inr rfl)]`. Rewrite using `[he0 _ hQ, hc0 _ hQ', add_zero, if_neg (by tauto)]`.
-/
theorem exists_isPrimeIdem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  intro F E _ _ _ _ _ σ hσ P
  obtain ⟨c, hcc, -, hcmem, hcund, -, hcint, -⟩ := GlobalTheory.cmConjugation_on_primes_adeles_idempotents F E σ hσ
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, -, -⟩ := GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ
  have crit := GlobalTheory.adele_idem_prime_criterion F E Φ hΦ1 hΦ2 hΦ3
  obtain ⟨α, hα1, hα0⟩ := exists_indicator F (P.under (𝓞 F))
  have hε : IsPlaceIdem F (P.under (𝓞 F)) (pairA F 0 α) := ⟨α, rfl, hα1, hα0⟩
  set ε := pairA F 0 α with hεdef
  set η := algebraMap (AF F) (AE F E) ε with hη
  obtain ⟨hη1, hη2⟩ := hΦ3 _ _ hε
  rw [← hη] at hη1 hη2
  have hη3 : ∀ Q, (Φ η).2 Q = if Q = P ∨ Q = c P then 1 else 0 := by
    intro Q
    rw [hη2 Q]
    exact if_congr (eq_comm.trans (hcund P Q)) rfl rfl
  have mulap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a * b).2 Q = a.2 Q * b.2 Q :=
    fun _ _ _ => rfl
  have addap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a + b).2 Q = a.2 Q + b.2 Q :=
    fun _ _ _ => rfl
  by_cases hP : c P = P
  · have hηη : η * η = η := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, hη1, mul_zero]
      · rw [mulap, hη3]; split_ifs <;> simp
    refine ⟨η, η, Or.inr ⟨rfl, ⟨_, ε, hε, rfl⟩, ?_⟩⟩
    refine (crit η P _ ε hε hηη hηη).2 ⟨hη1, ?_, fun Q hQ => ?_⟩
    · rw [hη3, if_pos (Or.inl rfl)]
    · rw [hη3, if_neg]
      rw [hP]; simpa using hQ
  · obtain ⟨β, hβ1, hβ0⟩ := exists_indicator E P
    set e : AE F E := Φ.symm (0, β) with he
    have hΦe : Φ e = (0, β) := Φ.apply_symm_apply _
    have he1 : (Φ e).1 = 0 := by rw [hΦe]
    have heP : (Φ e).2 P = 1 := by rw [hΦe]; exact hβ1
    have he0 : ∀ Q, Q ≠ P → (Φ e).2 Q = 0 := by rw [hΦe]; exact hβ0
    have hee : e * e = e := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, mul_zero]
      · rw [mulap]
        by_cases hQ : Q = P
        · subst hQ; rw [heP, mul_one]
        · rw [he0 Q hQ, mul_zero]
    have heη : e * η = e := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, zero_mul]
      · rw [mulap]
        by_cases hQ : Q = P
        · rw [hη3, if_pos (Or.inl hQ), mul_one]
        · rw [he0 Q hQ, zero_mul]
    have hcr := (crit e P _ ε hε hee heη).2 ⟨he1, heP, he0⟩
    have hσσ : ∀ x : E, σ (σ x) = x := by
      intro x
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      apply τ.injective
      rw [hσ.2.2.2, hσ.2.2.2, star_star]
    have hcr' : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ (c P).asIdeal ↔
        finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
      intro x hx
      have hint : IsIntegral ℤ (σ (x : E)) :=
        (RingOfIntegers.isIntegral_coe x).map (σ.toRingHom.toIntAlgHom)
      let y : 𝓞 E := ⟨σ (x : E), hint⟩
      have hy : (y : E) = σ (x : E) := rfl
      have hxy : (x : E) = σ (y : E) := by rw [hy, hσσ]
      have hy0 : y ≠ 0 := by
        intro h0
        apply hx
        apply RingOfIntegers.ext
        rw [hxy, h0]; simp
      rw [(hcmem P y x hxy).1, hcr y hy0, ← hcint, map_mul (cA σ), cA_incA, map_inv₀, ← hxy]
    have hee' : cA σ e * cA σ e = cA σ e := by rw [← map_mul, hee]
    have heη' : cA σ e * η = cA σ e := by
      have := congrArg (cA σ) heη
      rwa [map_mul, hη, cA_algebraMap] at this
    obtain ⟨hc1, hcP, hc0⟩ := (crit (cA σ e) (c P) _ ε hε hee' heη').1 hcr'
    refine ⟨e, e + cA σ e, Or.inl ⟨⟨⟨hee, ?_, _, ε, hε, ?_⟩, hcr⟩, rfl⟩⟩
    · apply Φ.injective
      rw [map_mul, map_zero]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, zero_mul]; rfl
      · rw [mulap]
        by_cases hQ : Q = P
        · rw [hc0 Q (by rw [hQ]; exact fun h => hP h.symm), mul_zero]; rfl
        · rw [he0 Q hQ, zero_mul]; rfl
    · apply Φ.injective
      rw [map_add, ← hη]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_add, he1, hc1, hη1, add_zero]
      · rw [addap, hη3]
        by_cases hQ : Q = P
        · subst hQ
          rw [heP, hc0 _ (fun h => hP h.symm), add_zero, if_pos (Or.inl rfl)]
        · by_cases hQ' : Q = c P
          · subst hQ'
            rw [he0 _ hQ, hcP, zero_add, if_pos (Or.inr rfl)]
          · rw [he0 _ hQ, hc0 _ hQ', add_zero, if_neg (by tauto)]

end GlobalTheory.PrimeIdemExists
