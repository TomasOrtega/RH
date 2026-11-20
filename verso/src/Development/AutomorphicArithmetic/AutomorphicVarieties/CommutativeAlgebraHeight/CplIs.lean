import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Rewrite using `[AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]`. Both sides reduce to the same expression.
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
Rewrite `h` using `[mem_pow_iff, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Establish `h' : Submodule.Quotient.mk (p` using `(maximalIdeal L ^ n • ⊤ : Submodule L L)) a = 0 := by`. Simplify `h` using `[AdicCompletion.eval]`. Rewrite `h'` using `[Submodule.Quotient.mk_eq_zero]`. Simplify using `using h'`.
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
Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_pow_iff, map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero, ← ha]`. Simplify using `[AdicCompletion.eval]`.
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
Introduce `C _ _ x hx`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Establish `hL : ∀ (n : ℕ) (a : Localization.AtPrime x), a ∈ maximalIdeal (Localization.AtPrime x) ^ n → algebraMap (Localization.AtPrime x) (Cpl x) a ∈ maximalIdeal (Cpl x) ^ n`. Introduce `n a ha`. Rewrite using `[AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]`.

Conclude with `Ideal.mem_map_of_mem _ ha`. Use `{ noeth := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _ complete := inferInstance comap_pow := fun n => ?_ dense := fun n r => ?_ }` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.comap_comap]`.

Establish `e : Ideal.comap (algebraMap (Localization.AtPrime x) (Cpl x)) (maximalIdeal (Cpl x) ^ n) = maximalIdeal (Localization.AtPrime x) ^ n`. Use extensionality with `a`. Conclude with `⟨strict_loc _ n a, hL n a⟩`. Rewrite using `[e, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]`. Use `IsLocalization.comap_map_of_isPrimary_disjoint x.primeCompl _ ?_ ?_` and prove the remaining obligations.

Apply `Ideal.isPrimary_of_isMaximal_radical` to reduce the goal to its premises. Rewrite using `[Ideal.radical_pow _ hn.ne', (inferInstance : x.IsPrime).radical]`. Use `infer_instance`. Conclude with `Set.disjoint_left.mpr fun s hs hs' => hs (Ideal.pow_le_self hn.ne' hs')`. Take `⟨a, ha⟩` from `dense_loc _ n r`.

Take `⟨⟨c, s⟩, rfl⟩` from `IsLocalization.mk'_surjective x.primeCompl a`. Establish `hsx : Ideal.span {(s : C)} ⊔ x = ⊤`. Rewrite using `[sup_comm]`. Establish `hm : (s : C) ∈ x ⊔ Ideal.span {(s : C)}` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Use `hx.out.2 _ (lt_of_le_of_ne le_sup_left fun e => s.2 ?_)` and prove the remaining obligations.

Rewrite `hm` using `[← e]`. Then use the resulting hypothesis. Establish `h1 : (1 : C) ∈ Ideal.span {(s : C)} ⊔ x ^ n`. Rewrite using `[Ideal.sup_pow_eq_top hsx]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp h1`.

Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Use `⟨c * t, ?_⟩` and prove the remaining obligations. Establish `key : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) = IsLocalization.mk' (Localization.AtPrime x) c s * algebraMap C _ z`. Establish `hs` using `IsLocalization.mk'_spec (Localization.AtPrime x) c s`. Establish `hz' : z = 1 - t * s`.

Rewrite using `[← hyz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz', map_sub, map_one, map_mul, map_mul, ← hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) ∈ maximalIdeal (Localization.AtPrime x) ^ n`.

Rewrite using `[key, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hz)`. Establish `hsum` using `Ideal.add_mem _ ha (hL n _ hmem)`. Rewrite `hsum` using `[map_sub, ← IsScalarTower.algebraMap_apply C (Localization.AtPrime x) (Cpl x)]`. Use `hsum using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
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
