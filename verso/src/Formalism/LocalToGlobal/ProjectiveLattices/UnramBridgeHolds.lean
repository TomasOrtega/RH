import Mathlib

open NumberField Polynomial

namespace Formalism.L2.Pj

attribute [local instance] FractionRing.liftAlgebra

/- English proof (translation)
Introduce `K _ _ _ hθ`. Use `set F := maximalRealSubfield K with hF`. Establish `hsep : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 K))`. Use `Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_` and prove the remaining obligations. Use extensionality with `_`.

Conclude with `IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm (FractionRing.algEquiv (𝓞 K) K).symm _`. Rewrite using `[Algebra.unramified_iff_forall]`. Introduce and unpack `⟨Q, hQ⟩`. Express the relevant statement in the definitionally equal form `Algebra.IsUnramifiedAt (𝓞 F) Q`. Break down `eq_or_ne Q ⊥ with rfl | hne` into its components or cases.

Conclude with `Algebra.isUnramifiedAt_bot`. Establish `hmax : Q.IsMaximal` using `hQ.isMaximal hne`. Take `⟨θ, hθP⟩` from `hθ Q hmax`. Use `set θ' := RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ with hθ'`. Establish `hσ : θ' = IsCMField.ringOfIntegersComplexConj K θ` using `RingOfIntegers.ext rfl`.

Establish `hne' : θ - θ' ≠ 0` using `fun h => hθP (h ▸ Ideal.zero_mem _)`. Establish `hnotF : (θ : K) ∉ F`. Introduce `hm`. Apply `hne'` to reduce the goal to its premises. Rewrite using `[sub_eq_zero, hσ]`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj]`. Conclude with `((IsCMField.complexConj_eq_self_iff K _).mpr hm).symm`. Establish `hfin : Module.finrank F K = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two F K`. Establish `hint : IsIntegral F (θ : K)` using `Algebra.IsIntegral.isIntegral _`.

Establish `hadj : Algebra.adjoin F {algebraMap (𝓞 K) K θ} = ⊤`. Establish `: IsSimpleOrder (IntermediateField F K)` using `IntermediateField.isSimpleOrder_of_finrank_prime F K (hfin ▸ Nat.prime_two)`. Break down `eq_bot_or_eq_top (IntermediateField.adjoin F {(θ : K)}) with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `h` using `[IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot]`.

Take `⟨y, hy⟩` from `h`. Conclude with `hnotF (hy ▸ y.2)`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Express the relevant statement in the definitionally equal form `(IntermediateField.adjoin F {(θ : K)}).toSubalgebra = ⊤`. Rewrite using `[h, IntermediateField.top_toSubalgebra]`.

Establish `hmem` using `aeval_derivative_mem_differentIdeal (𝓞 F) F K θ hadj`. Use `set f := minpoly (𝓞 F) θ with hf`. Establish `hθint : IsIntegral (𝓞 F) θ` using `Algebra.IsIntegral.isIntegral _`. Establish `hmonic : f.Monic` using `minpoly.monic hθint`. Establish `hdeg : f.natDegree ≤ 2`.

Establish `h1 : f = minpoly (𝓞 F) (algebraMap (𝓞 K) K θ)` using `(minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) θ).symm`. Establish `h2` using `minpoly.isIntegrallyClosed_eq_field_fractions' F (IsIntegral.algebraMap hθint : IsIntegral (𝓞 F) (algebraMap (𝓞 K) K θ))`. Establish `h3 : (minpoly F (algebraMap (𝓞 K) K θ)).natDegree ≤ 2` using `hfin ▸ minpoly.natDegree_le _`. Rewrite `h3` using `[h2, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _)]`. Rewrite using `[h1]`.

Conclude with `h3`. Use `set fK := f.map (algebraMap (𝓞 F) (𝓞 K)) with hfK`. Establish `hKmonic : fK.Monic` using `hmonic.map _`. Establish `hKdeg : fK.natDegree ≤ 2`. Rewrite using `[hfK, hmonic.natDegree_map]`.

Conclude with `hdeg`. Establish `hr1 : fK.IsRoot θ`. Rewrite using `[IsRoot, hfK, eval_map, ← aeval_def]`. Conclude with `minpoly.aeval _ _`. Establish `hr2 : fK.IsRoot θ'`.

Rewrite using `[IsRoot, hfK, eval_map, ← aeval_def, hσ]`. Rewrite using `[show IsCMField.ringOfIntegersComplexConj K θ = (IsCMField.ringOfIntegersComplexConj K).toAlgHom θ from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Use `set g := fK /ₘ (X - C θ) with hg`. Establish `hfg : (X - C θ) * g = fK` using `(mul_divByMonic_eq_iff_isRoot).mpr hr1`. Establish `hg2 : g.IsRoot θ'`.

Use `hr2` as an intermediate fact. Rewrite `this` using `[← hfg, IsRoot, eval_mul]`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hne'` to reduce the goal to its premises.

Simplify using `at h`. Rewrite `h`, the goal using `[sub_eq_zero]`. Conclude with `h.symm`. Conclude with `h`. Use `set h := g /ₘ (X - C θ') with hh`.

Establish `hgh : (X - C θ') * h = g` using `(mul_divByMonic_eq_iff_isRoot).mpr hg2`. Establish `hfac : fK = (X - C θ) * ((X - C θ') * h)` using `by rw [hgh, hfg]`. Establish `hhmonic : h.Monic`. Establish `hm2 : ((X - C θ) * (X - C θ')).Monic` using `(monic_X_sub_C θ).mul (monic_X_sub_C θ')`. Rewrite `hKmonic` using `[hfac, ← mul_assoc]`.

Conclude with `hm2.of_mul_monic_left hKmonic`. Establish `hh1 : h = 1`. Rewrite using `[← hhmonic.natDegree_eq_zero]`. Use `hKdeg` as an intermediate fact. Rewrite `this` using `[hfac, natDegree_mul (X_sub_C_ne_zero θ) (mul_ne_zero (X_sub_C_ne_zero θ') hhmonic.ne_zero), natDegree_mul (X_sub_C_ne_zero θ') hhmonic.ne_zero, natDegree_X_sub_C, natDegree_X_sub_C]`.

Use linear arithmetic over natural numbers and integers. Establish `hval : aeval θ (derivative f) = θ - θ'`. Rewrite using `[aeval_def, ← eval_map, ← derivative_map, ← hfK, hfac, hh1]`. Simplify using `[derivative_mul]`. Rewrite using `[← not_dvd_differentIdeal_iff, Ideal.dvd_iff_le]`.

Introduce `hle`. Conclude with `hθP (hle (hval ▸ hmem))`.
-/
theorem unramBridge_holds : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    (∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ θ : 𝓞 K,
      θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ ∉ P) →
    Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
  intro K _ _ _ hθ
  set F := maximalRealSubfield K with hF
  have hsep : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [Algebra.unramified_iff_forall]
  rintro ⟨Q, hQ⟩
  change Algebra.IsUnramifiedAt (𝓞 F) Q
  rcases eq_or_ne Q ⊥ with rfl | hne
  · exact Algebra.isUnramifiedAt_bot
  have hmax : Q.IsMaximal := hQ.isMaximal hne
  obtain ⟨θ, hθP⟩ := hθ Q hmax
  set θ' := RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ with hθ'
  have hσ : θ' = IsCMField.ringOfIntegersComplexConj K θ := RingOfIntegers.ext rfl
  have hne' : θ - θ' ≠ 0 := fun h => hθP (h ▸ Ideal.zero_mem _)

  have hnotF : (θ : K) ∉ F := by
    intro hm
    apply hne'
    rw [sub_eq_zero, hσ]
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    exact ((IsCMField.complexConj_eq_self_iff K _).mpr hm).symm

  have hfin : Module.finrank F K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F K
  have hint : IsIntegral F (θ : K) := Algebra.IsIntegral.isIntegral _
  have hadj : Algebra.adjoin F {algebraMap (𝓞 K) K θ} = ⊤ := by
    have : IsSimpleOrder (IntermediateField F K) :=
      IntermediateField.isSimpleOrder_of_finrank_prime F K (hfin ▸ Nat.prime_two)
    rcases eq_bot_or_eq_top (IntermediateField.adjoin F {(θ : K)}) with h | h
    · exfalso
      rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot] at h
      obtain ⟨y, hy⟩ := h
      exact hnotF (hy ▸ y.2)
    · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      change (IntermediateField.adjoin F {(θ : K)}).toSubalgebra = ⊤
      rw [h, IntermediateField.top_toSubalgebra]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F K θ hadj

  set f := minpoly (𝓞 F) θ with hf
  have hθint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral _
  have hmonic : f.Monic := minpoly.monic hθint
  have hdeg : f.natDegree ≤ 2 := by
    have h1 : f = minpoly (𝓞 F) (algebraMap (𝓞 K) K θ) :=
      (minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) θ).symm
    have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' F
      (IsIntegral.algebraMap hθint : IsIntegral (𝓞 F) (algebraMap (𝓞 K) K θ))
    have h3 : (minpoly F (algebraMap (𝓞 K) K θ)).natDegree ≤ 2 :=
      hfin ▸ minpoly.natDegree_le _
    rw [h2, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h3
    rw [h1]; exact h3
  set fK := f.map (algebraMap (𝓞 F) (𝓞 K)) with hfK
  have hKmonic : fK.Monic := hmonic.map _
  have hKdeg : fK.natDegree ≤ 2 := by
    rw [hfK, hmonic.natDegree_map]; exact hdeg
  have hr1 : fK.IsRoot θ := by
    rw [IsRoot, hfK, eval_map, ← aeval_def]; exact minpoly.aeval _ _
  have hr2 : fK.IsRoot θ' := by
    rw [IsRoot, hfK, eval_map, ← aeval_def, hσ]
    rw [show IsCMField.ringOfIntegersComplexConj K θ = (IsCMField.ringOfIntegersComplexConj K).toAlgHom θ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  set g := fK /ₘ (X - C θ) with hg
  have hfg : (X - C θ) * g = fK := (mul_divByMonic_eq_iff_isRoot).mpr hr1
  have hg2 : g.IsRoot θ' := by
    have := hr2
    rw [← hfg, IsRoot, eval_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hne'; simp at h; rw [sub_eq_zero] at h ⊢; exact h.symm
    · exact h
  set h := g /ₘ (X - C θ') with hh
  have hgh : (X - C θ') * h = g := (mul_divByMonic_eq_iff_isRoot).mpr hg2
  have hfac : fK = (X - C θ) * ((X - C θ') * h) := by rw [hgh, hfg]
  have hhmonic : h.Monic := by
    have hm2 : ((X - C θ) * (X - C θ')).Monic := (monic_X_sub_C θ).mul (monic_X_sub_C θ')
    rw [hfac, ← mul_assoc] at hKmonic
    exact hm2.of_mul_monic_left hKmonic
  have hh1 : h = 1 := by
    rw [← hhmonic.natDegree_eq_zero]
    have := hKdeg
    rw [hfac, natDegree_mul (X_sub_C_ne_zero θ) (mul_ne_zero (X_sub_C_ne_zero θ') hhmonic.ne_zero),
      natDegree_mul (X_sub_C_ne_zero θ') hhmonic.ne_zero, natDegree_X_sub_C, natDegree_X_sub_C] at this
    omega
  have hval : aeval θ (derivative f) = θ - θ' := by
    rw [aeval_def, ← eval_map, ← derivative_map, ← hfK, hfac, hh1]
    simp [derivative_mul]
  rw [← not_dvd_differentIdeal_iff, Ideal.dvd_iff_le]
  intro hle
  exact hθP (hle (hval ▸ hmem))

end Formalism.L2.Pj
