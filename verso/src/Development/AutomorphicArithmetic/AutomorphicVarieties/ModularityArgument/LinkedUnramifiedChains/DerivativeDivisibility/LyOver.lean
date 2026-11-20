import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CmpPrime

open Polynomial

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Introduce a local definition for the expression. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem ext_injective {R S K : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field K]
    [IsAlgClosed K] (f : R →+* S) (hi : Function.Injective f) (hf : f.IsIntegral) (φ : R →+* K)
    (hφ : Function.Injective φ) : ∃ ψ : S →+* K, ψ.comp f = φ := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R K := φ.toAlgebra
  haveI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.2 hi
  haveI : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  haveI : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  let e : S →ₐ[R] K := IsAlgClosed.lift
  exact ⟨e.toRingHom, RingHom.ext fun r => e.commutes r⟩

/- English proof (translation)
Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Introduce a local definition for the expression. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem ext_integral {R S K : Type} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    (f : R →+* S) (hf : f.IsIntegral) (φ : R →+* K) (h : RingHom.ker f ≤ RingHom.ker φ) :
    ∃ ψ : S →+* K, ψ.comp f = φ := by
  letI : Algebra R S := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) ⊥ (by
    intro r hr
    apply h
    rw [RingHom.mem_ker]
    exact Ideal.mem_bot.1 (Ideal.mem_comap.1 hr))
  have hQc' : Q.comap f = RingHom.ker φ := hQc
  let φ' : R ⧸ Q.comap f →+* K := Ideal.Quotient.lift _ φ (fun a ha => by
    rw [hQc'] at ha
    exact ha)
  have hφ' : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc']
    exact hx
  obtain ⟨ψ, hψ⟩ := ext_injective (Ideal.quotientMap Q f le_rfl) Ideal.quotientMap_injective
    (RingHom.IsIntegral.quotient f hf) φ' hφ'
  refine ⟨ψ.comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  have := congrArg (fun g => g (Ideal.Quotient.mk _ r)) hψ
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk] at this ⊢
  exact this.trans (Ideal.Quotient.lift_mk _ _ _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.V.J.lyOver :
    UpperTheory.V.J.LyOver := by
  intro O Λ B K _ _ _ _ _ _ _ _ _ lam J t s g hC p z i hz
  obtain ⟨hprime, hdiv, hnot⟩ := UpperTheory.V.J.cmpPrime O Λ B lam J t s g hC i
  set Q := UpperTheory.V.J.cmp lam J t g i with hQdef
  have hJQ : J ≤ Q := by
    intro a ha
    rw [hQdef, UpperTheory.V.J.cmp, Submodule.mem_colon]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    simpa [smul_eq_mul] using J.mul_mem_right _ ha
  let f : Λ[X] →+* B ⧸ Q := (Ideal.Quotient.mk Q).comp (eval₂RingHom (lam : Λ →+* B) t)
  have hfC : f.comp C = (Ideal.Quotient.mk Q).comp (lam : Λ →+* B) := by
    ext c
    simp [f]
  have hint : f.IsIntegral := by
    apply RingHom.IsIntegral.tower_top C f
    rw [hfC]
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, hqm, hq⟩ := hC.int b
    refine ⟨q, hqm, ?_⟩
    rw [← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hJQ hq
  let φ : Λ[X] →+* K := eval₂RingHom (p : Λ →+* K) z
  have hker : RingHom.ker f ≤ RingHom.ker φ := by
    intro q hq
    rw [RingHom.mem_ker] at hq ⊢
    have hq' : eval₂ (lam : Λ →+* B) t q ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [f] using hq
    obtain ⟨r, rfl⟩ := (hdiv q).1 hq'
    simp only [φ, coe_eval₂RingHom, eval₂_mul]
    rw [hz, zero_mul]
  obtain ⟨ψ, hψ⟩ := ext_integral f hint φ hker
  have hc : ∀ c, ψ (Ideal.Quotient.mk Q (lam c)) = p c := by
    intro c
    have := congrArg (fun h => h (C c)) hψ
    simpa [f, φ] using this
  have ht : ψ (Ideal.Quotient.mk Q t) = z := by
    have := congrArg (fun h => h X) hψ
    simpa [f, φ] using this
  refine ⟨{ toRingHom := ψ.comp (Ideal.Quotient.mk Q), commutes' := ?_ }, ?_, ?_, ?_⟩
  · intro o
    have := hc (algebraMap O Λ o)
    simpa using this
  · intro b hb
    rw [RingHom.mem_ker]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hb]
  · ext c
    simpa using hc c
  · simpa using ht
