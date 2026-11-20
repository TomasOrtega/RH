import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
  have h' : Submodule.Quotient.mk (p := (maximalIdeal L ^ n • ⊤ : Submodule L L)) a = 0 := by
    simpa [AdicCompletion.eval] using h
  rw [Submodule.Quotient.mk_eq_zero] at h'
  simpa using h'

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, sub_eq_zero, ← ha]
  simp [AdicCompletion.eval]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Check the elementary cases of the proposition. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.V.CA.cpl_is :
    ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (x : Ideal C) [x.IsMaximal], ∃ _ : IsLocalRing (Cpl x), IsCplAt x (Cpl x) := by
  intro C _ _ x hx
  refine ⟨inferInstance, ?_⟩
  have hL : ∀ (n : ℕ) (a : Localization.AtPrime x),
      a ∈ maximalIdeal (Localization.AtPrime x) ^ n →
      algebraMap (Localization.AtPrime x) (Cpl x) a ∈ maximalIdeal (Cpl x) ^ n := by
    intro n a ha
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  refine
    { noeth := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
      complete := inferInstance
      comap_pow := fun n => ?_
      dense := fun n r => ?_ }
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.comap_comap]
    have e : Ideal.comap (algebraMap (Localization.AtPrime x) (Cpl x)) (maximalIdeal (Cpl x) ^ n) =
        maximalIdeal (Localization.AtPrime x) ^ n := by
      ext a
      exact ⟨strict_loc _ n a, hL n a⟩
    rw [e, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    refine IsLocalization.comap_map_of_isPrimary_disjoint x.primeCompl _ ?_ ?_
    · apply Ideal.isPrimary_of_isMaximal_radical
      rw [Ideal.radical_pow _ hn.ne', (inferInstance : x.IsPrime).radical]
      infer_instance
    · exact Set.disjoint_left.mpr fun s hs hs' => hs (Ideal.pow_le_self hn.ne' hs')
  · obtain ⟨a, ha⟩ := dense_loc _ n r
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective x.primeCompl a
    have hsx : Ideal.span {(s : C)} ⊔ x = ⊤ := by
      rw [sup_comm]
      have hm : (s : C) ∈ x ⊔ Ideal.span {(s : C)} :=
        Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      refine hx.out.2 _ (lt_of_le_of_ne le_sup_left fun e => s.2 ?_)
      rwa [← e] at hm
    have h1 : (1 : C) ∈ Ideal.span {(s : C)} ⊔ x ^ n := by
      rw [Ideal.sup_pow_eq_top hsx]
      trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine ⟨c * t, ?_⟩
    have key : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) =
        IsLocalization.mk' (Localization.AtPrime x) c s * algebraMap C _ z := by
      have hs := IsLocalization.mk'_spec (Localization.AtPrime x) c s
      have hz' : z = 1 - t * s := by
        rw [← hyz]
        ring
      rw [hz', map_sub, map_one, map_mul, map_mul, ← hs]
      ring
    have hmem : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) ∈
        maximalIdeal (Localization.AtPrime x) ^ n := by
      rw [key, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hz)
    have hsum := Ideal.add_mem _ ha (hL n _ hmem)
    rw [map_sub, ← IsScalarTower.algebraMap_apply C (Localization.AtPrime x) (Cpl x)] at hsum
    convert hsum using 1
    ring
