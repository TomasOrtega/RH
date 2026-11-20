import Mathlib
import GroundTheory.LocalFields.IntermediateField
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.LowerIndex

namespace UpperTheory.Reformulated.B.RamificationLowerIndex

open Polynomial IsLocalRing ValuativeRel
open IsDiscreteValuationRing hiding maximalIdeal

/- English proof (translation)
Establish `h2 : ∀ m : ℕ, ∀ s : S, ∃ a ∈ A, π ^ m ∣ s - a`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro s; exact ⟨0, A.zero_mem, by simp⟩`. Consider the case `succ m ih`.

Introduce `s`. Take `⟨a, ha, t, ht⟩` from `ih s`. Take `⟨b, hb, u, hu⟩` from `h1 t`. Use `⟨a + π ^ m * b, A.add_mem ha (A.mul_mem (A.pow_mem hπ m) hb), u, ?_⟩` and prove the remaining obligations. Take the linear combination `ht + π ^ m * hu`.

Use `eq_top_iff.mpr <| Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥) (?_ : ⊤ ≤ A.toSubmodule ⊔ maximalIdeal R • ⊤)` and prove the remaining obligations. Introduce `s _`. Take `⟨a, ha, t, ht⟩` from `h2 n s`. Rewrite using `[Ideal.smul_top_eq_map]`. Use `Submodule.mem_sup.mpr ⟨a, ha, s - a, ?_, by ring⟩` and prove the remaining obligations.

Rewrite using `[Submodule.restrictScalars_mem, ht]`. Conclude with `Ideal.mul_mem_right _ _ hn`.
-/
private lemma adjoin_eq_top_of {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S] (A : Subalgebra R S) (π : S) (hπ : π ∈ A)
    (h1 : ∀ s : S, ∃ a ∈ A, π ∣ s - a) (n : ℕ)
    (hn : π ^ n ∈ (maximalIdeal R).map (algebraMap R S)) : A = ⊤ := by
  have h2 : ∀ m : ℕ, ∀ s : S, ∃ a ∈ A, π ^ m ∣ s - a := by
    intro m
    induction m with
    | zero => intro s; exact ⟨0, A.zero_mem, by simp⟩
    | succ m ih =>
      intro s
      obtain ⟨a, ha, t, ht⟩ := ih s
      obtain ⟨b, hb, u, hu⟩ := h1 t
      refine ⟨a + π ^ m * b, A.add_mem ha (A.mul_mem (A.pow_mem hπ m) hb), u, ?_⟩
      linear_combination ht + π ^ m * hu
  refine eq_top_iff.mpr <| Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    (?_ : ⊤ ≤ A.toSubmodule ⊔ maximalIdeal R • ⊤)
  intro s _
  obtain ⟨a, ha, t, ht⟩ := h2 n s
  rw [Ideal.smul_top_eq_map]
  refine Submodule.mem_sup.mpr ⟨a, ha, s - a, ?_, by ring⟩
  rw [Submodule.restrictScalars_mem, ht]
  exact Ideal.mul_mem_right _ _ hn

/- English proof (translation)
Set `_ : Fintype (ResidueField S)` to `Fintype.ofFinite _`. Take `⟨g, hg⟩` from `IsCyclic.exists_monoid_generator (α := (ResidueField S)ˣ)`. Take `⟨x₀, hx₀⟩` from `residue_surjective (R := S) (g : ResidueField S)`. Take `⟨ϖ, hϖ⟩` from `exists_irreducible S`. Establish `hm : maximalIdeal S = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`.

Establish `hres : ∀ z : S, residue S z = 0 ↔ ϖ ∣ z` using `fun z => by`. Rewrite using `[residue_eq_zero_iff, hm, Ideal.mem_span_singleton]`. Use `set q := Fintype.card (ResidueField S) with hq`. Establish `hpow : ∀ z : S, ϖ ∣ z ^ q - z` using `fun z => by`. Rewrite using `[← hres, map_sub, map_pow, FiniteField.pow_card, sub_self]`.

Establish `hqd : ϖ ∣ (q : S)`. Rewrite using `[← hres, map_natCast, hq, FiniteField.cast_card_eq_zero]`. Establish `hϖ0 : ϖ ≠ 0` using `hϖ.ne_zero`. Establish `hex : ∃ x : S, residue S x = g ∧ ¬ ϖ ^ 2 ∣ x ^ q - x`. Distinguish the cases in `h : ϖ ^ 2 ∣ x₀ ^ q - x₀`.

Use `⟨x₀ + ϖ, by rw [map_add, hx₀, (hres ϖ).2 dvd_rfl, add_zero], fun h' => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `(X ^ q : S[X]).binomExpansion x₀ ϖ`. Simplify using `only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_C] at hk`. Take `⟨c, hc⟩` from `hqd`. Take `⟨u, hu⟩` from `h`.

Take `⟨w, hw⟩` from `h'`. Establish `: ϖ * 1 = ϖ * (ϖ * (u + c * x₀ ^ (q - 1) + k - w))`. Rewrite `hk` using `[hc]`. Take the linear combination `hu + hk - hw`. Conclude with `hϖ.not_isUnit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hϖ0 this).symm)`.

Conclude with `⟨x₀, hx₀, h⟩`. Take `⟨x, hx, hx2⟩` from `hex`. Take `⟨u, hu⟩` from `hpow x`. Establish `huu : IsUnit u`. Assume the negation of the conclusion as `h`.

Establish `h3 : u ∈ maximalIdeal S` using `h`. Rewrite `h3` using `[hm, Ideal.mem_span_singleton]`. Conclude with `hx2 (by rw [hu, pow_two]; exact mul_dvd_mul_left _ h3)`. Establish `hxA : x ∈ Algebra.adjoin R {x}` using `Algebra.self_mem_adjoin_singleton R x`. Use `⟨x, adjoin_eq_top_of _ (x ^ q - x) (Subalgebra.sub_mem _ (Subalgebra.pow_mem _ hxA _) hxA) (fun s => ?_) n ?_⟩` and prove the remaining obligations.

Rewrite using `[hu]`. Simplify using `only [huu.mul_right_dvd, ← hres]`. Distinguish the cases in `hs : residue S s = 0`. Conclude with `⟨0, Subalgebra.zero_mem _, by simpa using hs⟩`. Take `⟨m, hm'⟩` from `hg (Units.mk0 _ hs)`.

Use `⟨x ^ m, Subalgebra.pow_mem _ hxA _, ?_⟩` and prove the remaining obligations. Use `congrArg Units.val hm'` as an intermediate fact. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mk0] at this`. Rewrite using `[map_sub, map_pow, hx, this, sub_self]`. Apply `hn` to reduce the goal to its premises.

Apply `Ideal.pow_mem_pow` to reduce the goal to its premises. Rewrite using `[hm, Ideal.mem_span_singleton]`. Conclude with `hpow x`.
-/
private lemma exists_generator {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Module.Finite R S] [IsDomain S] [IsDiscreteValuationRing S]
    [Finite (ResidueField S)] (n : ℕ)
    (hn : maximalIdeal S ^ n ≤ (maximalIdeal R).map (algebraMap R S)) :
    ∃ x : S, Algebra.adjoin R {x} = ⊤ := by
  classical
  let _ : Fintype (ResidueField S) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ResidueField S)ˣ)
  obtain ⟨x₀, hx₀⟩ := residue_surjective (R := S) (g : ResidueField S)
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible S
  have hm : maximalIdeal S = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hres : ∀ z : S, residue S z = 0 ↔ ϖ ∣ z := fun z => by
    rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton]
  set q := Fintype.card (ResidueField S) with hq
  have hpow : ∀ z : S, ϖ ∣ z ^ q - z := fun z => by
    rw [← hres, map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hqd : ϖ ∣ (q : S) := by
    rw [← hres, map_natCast, hq, FiniteField.cast_card_eq_zero]
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hex : ∃ x : S, residue S x = g ∧ ¬ ϖ ^ 2 ∣ x ^ q - x := by
    by_cases h : ϖ ^ 2 ∣ x₀ ^ q - x₀
    · refine ⟨x₀ + ϖ, by rw [map_add, hx₀, (hres ϖ).2 dvd_rfl, add_zero], fun h' => ?_⟩
      obtain ⟨k, hk⟩ := (X ^ q : S[X]).binomExpansion x₀ ϖ
      simp only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_C] at hk
      obtain ⟨c, hc⟩ := hqd
      obtain ⟨u, hu⟩ := h
      obtain ⟨w, hw⟩ := h'
      have : ϖ * 1 = ϖ * (ϖ * (u + c * x₀ ^ (q - 1) + k - w)) := by
        rw [hc] at hk
        linear_combination hu + hk - hw
      exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hϖ0 this).symm)
    · exact ⟨x₀, hx₀, h⟩
  obtain ⟨x, hx, hx2⟩ := hex
  obtain ⟨u, hu⟩ := hpow x
  have huu : IsUnit u := by
    by_contra h
    have h3 : u ∈ maximalIdeal S := h
    rw [hm, Ideal.mem_span_singleton] at h3
    exact hx2 (by rw [hu, pow_two]; exact mul_dvd_mul_left _ h3)
  have hxA : x ∈ Algebra.adjoin R {x} := Algebra.self_mem_adjoin_singleton R x
  refine ⟨x, adjoin_eq_top_of _ (x ^ q - x)
    (Subalgebra.sub_mem _ (Subalgebra.pow_mem _ hxA _) hxA) (fun s => ?_) n ?_⟩
  · rw [hu]
    simp only [huu.mul_right_dvd, ← hres]
    by_cases hs : residue S s = 0
    · exact ⟨0, Subalgebra.zero_mem _, by simpa using hs⟩
    · obtain ⟨m, hm'⟩ := hg (Units.mk0 _ hs)
      refine ⟨x ^ m, Subalgebra.pow_mem _ hxA _, ?_⟩
      have := congrArg Units.val hm'
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      rw [map_sub, map_pow, hx, this, sub_self]
  · apply hn
    apply Ideal.pow_mem_pow
    rw [hm, Ideal.mem_span_singleton]
    exact hpow x

/- English proof (translation)
Establish `hd : ∏ t, (X - C (a t)) ∣ g.map (algebraMap R S) - C y`. Distinguish the cases in `h0 : g.map (algebraMap R S) - C y = 0`. Rewrite using `[h0]`. Conclude with `dvd_zero _`. Use `(Multiset.prod_X_sub_C_dvd_iff_le_roots h0 (Finset.univ.val.map a)).2 (by` as an intermediate fact.

Rewrite using `[Multiset.le_iff_subset (Finset.univ.nodup.map ha)]`. Introduce `z hz`. Take `⟨t, -, rfl⟩` from `Multiset.mem_map.1 hz`. Rewrite using `[mem_roots h0, IsRoot, eval_sub, eval_map_algebraMap, eval_C, hr, sub_self])`. Rewrite `this` using `[Multiset.map_map]`. Then use the resulting hypothesis.

Establish `h2` using `_root_.map_dvd ((evalRingHom x).comp (mapRingHom (s : S →+* S))) hd`. Establish `h3 : (s : S →+* S).comp (algebraMap R S) = algebraMap R S` using `s.comp_algebraMap`. Simplify using `only [map_prod, map_sub, RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, map_X, map_C, eval_X, eval_C, Polynomial.map_map, h3, eval_map_algebraMap, hx, RingHom.coe_coe] at h2`. Conclude with `dvd_sub_comm.1 h2`.
-/
private lemma prod_dvd_sub {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    {H : Type*} [Fintype H] (a : H → S) (ha : Function.Injective a) (x y : S)
    (s : S →ₐ[R] S) (g : R[X]) (hr : ∀ t, aeval (a t) g = y) (hx : aeval x g = y) :
    ∏ t, (x - s (a t)) ∣ s y - y := by
  classical
  have hd : ∏ t, (X - C (a t)) ∣ g.map (algebraMap R S) - C y := by
    by_cases h0 : g.map (algebraMap R S) - C y = 0
    · rw [h0]; exact dvd_zero _
    have := (Multiset.prod_X_sub_C_dvd_iff_le_roots h0 (Finset.univ.val.map a)).2 (by
      rw [Multiset.le_iff_subset (Finset.univ.nodup.map ha)]
      intro z hz
      obtain ⟨t, -, rfl⟩ := Multiset.mem_map.1 hz
      rw [mem_roots h0, IsRoot, eval_sub, eval_map_algebraMap, eval_C, hr, sub_self])
    rwa [Multiset.map_map] at this
  have h2 := _root_.map_dvd ((evalRingHom x).comp (mapRingHom (s : S →+* S))) hd
  have h3 : (s : S →+* S).comp (algebraMap R S) = algebraMap R S := s.comp_algebraMap
  simp only [map_prod, map_sub, RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, map_X,
    map_C, eval_X, eval_C, Polynomial.map_map, h3, eval_map_algebraMap, hx, RingHom.coe_coe] at h2
  exact dvd_sub_comm.1 h2

/- English proof (translation)
Establish `h1 : C d ∣ (∏ t, (X - C (a t))).map s - ∏ t, (X - C (a t))`. Rewrite using `[C_dvd_iff_dvd_coeff]`. Introduce `i`. Rewrite using `[coeff_sub, coeff_map]`. Conclude with `h i`.

Establish `h2` using `_root_.map_dvd (evalRingHom (a t₀)) h1`. Establish `h3 : ∏ t, (a t₀ - a t) = 0` using `Finset.prod_eq_zero (Finset.mem_univ t₀) (sub_self _)`. Simplify `h2` using `only [Polynomial.map_prod, Polynomial.map_sub, map_prod, map_sub, coe_evalRingHom, map_X, map_C, eval_X, eval_C, h3, sub_zero]`.
-/
private lemma dvd_prod {S : Type*} [CommRing S]
    {H : Type*} [Fintype H] (a : H → S) (t₀ : H) (d : S) (s : S →+* S)
    (h : ∀ i, d ∣ s ((∏ t, (X - C (a t))).coeff i) - (∏ t, (X - C (a t))).coeff i) :
    d ∣ ∏ t, (a t₀ - s (a t)) := by
  have h1 : C d ∣ (∏ t, (X - C (a t))).map s - ∏ t, (X - C (a t)) := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_map]
    exact h i
  have h2 := _root_.map_dvd (evalRingHom (a t₀)) h1
  have h3 : ∏ t, (a t₀ - a t) = 0 := Finset.prod_eq_zero (Finset.mem_univ t₀) (sub_self _)
  simpa only [Polynomial.map_prod, Polynomial.map_sub, map_prod, map_sub, coe_evalRingHom, map_X,
    map_C, eval_X, eval_C, h3, sub_zero] using h2

/- English proof (translation)
Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Rewrite using `[map_zero, addVal_zero, addVal_zero, ENat.mul_top (by exact_mod_cast he)]`. Take `⟨π, hπ⟩` from `exists_irreducible T`. Take `⟨ϖ, hϖ⟩` from `exists_irreducible S`.

Rewrite `h` using `[hπ.maximalIdeal_eq, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]`. Take `⟨w, hw⟩` from `h.symm`. Take `⟨n, u, rfl⟩` from `eq_unit_mul_pow_irreducible hz hπ`. Rewrite using `[addVal_def' u hπ n, ← Nat.cast_mul]`. Use `addVal_def _ (Units.map (algebraMap T S : T →* S) u * w ^ n) hϖ _ ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, ← hw]`. Simplify using `only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma addVal_algebraMap {T S : Type*} [CommRing T] [CommRing S] [IsDomain T] [IsDomain S]
    [IsDiscreteValuationRing T] [IsDiscreteValuationRing S] [Algebra T S] (e : ℕ) (he : e ≠ 0)
    (h : (maximalIdeal T).map (algebraMap T S) = maximalIdeal S ^ e) (z : T) :
    addVal S (algebraMap T S z) = e * addVal T z := by
  by_cases hz : z = 0
  · subst hz
    rw [map_zero, addVal_zero, addVal_zero, ENat.mul_top (by exact_mod_cast he)]
  obtain ⟨π, hπ⟩ := exists_irreducible T
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible S
  rw [hπ.maximalIdeal_eq, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨w, hw⟩ := h.symm
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hz hπ
  rw [addVal_def' u hπ n, ← Nat.cast_mul]
  refine addVal_def _ (Units.map (algebraMap T S : T →* S) u * w ^ n) hϖ _ ?_
  rw [map_mul, map_pow, ← hw]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  ring

/- English proof (translation)
Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert t F ht ih => rw [Finset.prod_insert ht, Finset.sum_insert ht, addVal_mul, ih]`.
-/
private lemma addVal_prod {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {H : Type*} (F : Finset H) (b : H → S) :
    addVal S (∏ t ∈ F, b t) = ∑ t ∈ F, addVal S (b t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert t F ht ih => rw [Finset.prod_insert ht, Finset.sum_insert ht, addVal_mul, ih]

end UpperTheory.Reformulated.B.RamificationLowerIndex

open Polynomial IsLocalRing ValuativeRel GroundTheory.LocalField in
open IsDiscreteValuationRing hiding maximalIdeal in
/- English proof (translation)
Introduce `K L _ _ _ _ _ _ _ _ _ _ _ M _ _ σ`. Take `⟨x, hx⟩` from `exists_generator (R := 𝒪[K]) (S := 𝒪[L]) _ (map_maximalIdeal K L).ge`. Establish `hv` using `addVal_algebraMap (T := 𝒪[M]) (S := 𝒪[L]) _ (ramificationIndex_pos M L).ne' (map_maximalIdeal M L)`. Use `set σ' : Gal(M/K) := AlgEquiv.restrictNormalHom M σ with hσ'`. Set `r : Gal(L/M) → (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L])` to `fun τ => integerAlgEquiv K L (τ.restrictScalars K)`.

Set `s` to `integerAlgEquiv K L σ`. Set `a : Gal(L/M) → 𝒪[L]` to `fun τ => r τ x`. Establish `ha1 : a 1 = x` using `rfl`. Establish `hamul : ∀ ρ τ, r ρ (a τ) = a (ρ * τ)` using `fun _ _ => rfl`. Establish `hcomm : ∀ y : 𝒪[M], s (algebraMap 𝒪[M] 𝒪[L] y) = algebraMap 𝒪[M] 𝒪[L] (integerAlgEquiv K M σ' y)` using `fun y => Subtype.ext (AlgEquiv.restrictNormal_commutes σ M (y : M)).symm`.

Establish `hfix : ∀ τ (y : 𝒪[M]), r τ (algebraMap 𝒪[M] 𝒪[L] y) = algebraMap 𝒪[M] 𝒪[L] y` using `fun τ y => Subtype.ext (τ.commutes (y : M))`. Establish `hinj : Function.Injective a`. Introduce `τ ρ h`. Establish `h1 : r (ρ⁻¹ * τ) x - x = 0`. Express the relevant statement in the definitionally equal form `a (ρ⁻¹ * τ) - x = 0`.

Rewrite using `[← hamul, h, hamul, inv_mul_cancel, ha1, sub_self]`. Establish `h2 : lowerIndex K L ((ρ⁻¹ * τ).restrictScalars K) = ⊤`. Rewrite using `[lowerIndex_eq_addVal_of_adjoin_eq_top hx, addVal_eq_top_iff]`. Conclude with `h1`. Rewrite `h2` using `[lowerIndex_restrictScalars, lowerIndex_eq_top_iff, inv_mul_eq_one]`.

Conclude with `h2.symm`. Establish `hsum : ∑ τ : Gal(L/M), lowerIndex K L (σ * τ.restrictScalars K) = addVal 𝒪[L] (∏ τ, (x - s (a τ)))`. Rewrite using `[addVal_prod]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[lowerIndex_eq_addVal_of_adjoin_eq_top hx, ← AddValuation.map_neg, neg_sub]`.

Both sides reduce to the same expression. Take `⟨y₀, hy₀⟩` from `ENat.exists_eq_iInf (fun y : 𝒪[M] => addVal 𝒪[M] (integerAlgEquiv K M σ' y - y))`. Establish `hy₁ : lowerIndex K M σ' = addVal 𝒪[M] (integerAlgEquiv K M σ' y₀ - y₀)` using `hy₀.symm`. Rewrite using `[hsum, hy₁, ← hv]`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[addVal_le_iff_dvd, ← ha1]`. Use `dvd_prod a 1 _ (s : 𝒪[L] →+* 𝒪[L]) fun i => ?_` and prove the remaining obligations. Use `set f : 𝒪[L][X] := ∏ τ, (X - C (a τ)) with hf`. Establish `hfr : ∀ ρ, r ρ (f.coeff i) = f.coeff i`. Introduce `ρ`.

Establish `: f.map (r ρ : 𝒪[L] →+* 𝒪[L]) = f`. Rewrite using `[hf, Polynomial.map_prod]`. Use `Fintype.prod_equiv (Equiv.mulLeft ρ) _ _ fun τ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.map_sub, map_X, map_C]`. Both sides reduce to the same expression.

Use `conv_rhs => rw [← this, coeff_map]`. Both sides reduce to the same expression. Take `⟨m, hm⟩` from `(IsGalois.mem_range_algebraMap_iff_fixed (F := M) ((f.coeff i : 𝒪[L]) : L)).2 fun ρ => congrArg Subtype.val (hfr ρ)`. Establish `hm1 : m ∈ 𝒪[M]`. Establish `h1 : valuation L (algebraMap M L m) ≤ 1` using `by rw [hm]; exact (f.coeff i).2`.

Conclude with `(Valuation.HasExtension.val_map_le_one_iff (valuation M) (valuation L) m).1 h1`. Establish `hy : f.coeff i = algebraMap 𝒪[M] 𝒪[L] ⟨m, hm1⟩` using `Subtype.ext hm.symm`. Rewrite using `[hy, RingHom.coe_coe, hcomm, ← map_sub]`. Apply `_root_.map_dvd` to reduce the goal to its premises. Rewrite using `[← addVal_le_iff_dvd, ← hy₁]`.

Conclude with `lowerIndex_le _ _`. Rewrite using `[addVal_le_iff_dvd, map_sub, ← hcomm]`. Establish `hz : algebraMap 𝒪[M] 𝒪[L] y₀ ∈ Algebra.adjoin 𝒪[K] {x}` using `hx ▸ trivial`. Rewrite `hz` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨g, hg⟩` from `hz`.

Use `replace hg : aeval x g = algebraMap 𝒪[M] 𝒪[L] y₀ := hg`. Use `prod_dvd_sub a hinj x _ (s : 𝒪[L] →ₐ[𝒪[K]] 𝒪[L]) g (fun τ => ?_) hg` and prove the remaining obligations. Rewrite using `[← hfix τ, ← hg]`. Conclude with `aeval_algHom_apply (r τ) x g`.
-/
theorem UpperTheory.Reformulated.B.RamificationLowerIndex.ramificationIndex_mul_lowerIndex_restrictNormalHom.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] [inst_4 : Field L] [inst_5 : ValuativeRel L] [inst_6 : TopologicalSpace L]
      [inst_7 : IsNonarchimedeanLocalField L] [inst_8 : Algebra K L] [inst_9 : ValuativeExtension K L]
      [inst_10 : FiniteDimensional K L] (M : IntermediateField K L) [IsGalois K L] [inst_12 : Normal K ↥M] (σ : Gal(L/K)),
      (↑(GroundTheory.LocalField.ramificationIndex (↥M) L) : ℕ∞) *
          GroundTheory.LocalField.lowerIndex K (↥M) ((AlgEquiv.restrictNormalHom ↥M : Gal(L/K) → Gal(↥M/K)) σ) =
        ∑ τ : Gal(L/↥M), GroundTheory.LocalField.lowerIndex K L (σ * AlgEquiv.restrictScalars K τ) := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ M _ _ σ
  obtain ⟨x, hx⟩ := exists_generator (R := 𝒪[K]) (S := 𝒪[L]) _ (map_maximalIdeal K L).ge
  have hv := addVal_algebraMap (T := 𝒪[M]) (S := 𝒪[L]) _ (ramificationIndex_pos M L).ne'
    (map_maximalIdeal M L)
  set σ' : Gal(M/K) := AlgEquiv.restrictNormalHom M σ with hσ'
  let r : Gal(L/M) → (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) := fun τ => integerAlgEquiv K L (τ.restrictScalars K)
  let s := integerAlgEquiv K L σ
  let a : Gal(L/M) → 𝒪[L] := fun τ => r τ x
  have ha1 : a 1 = x := rfl
  have hamul : ∀ ρ τ, r ρ (a τ) = a (ρ * τ) := fun _ _ => rfl
  have hcomm : ∀ y : 𝒪[M], s (algebraMap 𝒪[M] 𝒪[L] y) =
      algebraMap 𝒪[M] 𝒪[L] (integerAlgEquiv K M σ' y) := fun y =>
    Subtype.ext (AlgEquiv.restrictNormal_commutes σ M (y : M)).symm
  have hfix : ∀ τ (y : 𝒪[M]), r τ (algebraMap 𝒪[M] 𝒪[L] y) = algebraMap 𝒪[M] 𝒪[L] y :=
    fun τ y => Subtype.ext (τ.commutes (y : M))
  have hinj : Function.Injective a := by
    intro τ ρ h
    have h1 : r (ρ⁻¹ * τ) x - x = 0 := by
      change a (ρ⁻¹ * τ) - x = 0
      rw [← hamul, h, hamul, inv_mul_cancel, ha1, sub_self]
    have h2 : lowerIndex K L ((ρ⁻¹ * τ).restrictScalars K) = ⊤ := by
      rw [lowerIndex_eq_addVal_of_adjoin_eq_top hx, addVal_eq_top_iff]
      exact h1
    rw [lowerIndex_restrictScalars, lowerIndex_eq_top_iff, inv_mul_eq_one] at h2
    exact h2.symm
  have hsum : ∑ τ : Gal(L/M), lowerIndex K L (σ * τ.restrictScalars K) =
      addVal 𝒪[L] (∏ τ, (x - s (a τ))) := by
    rw [addVal_prod]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [lowerIndex_eq_addVal_of_adjoin_eq_top hx, ← AddValuation.map_neg, neg_sub]
    rfl
  obtain ⟨y₀, hy₀⟩ := ENat.exists_eq_iInf
    (fun y : 𝒪[M] => addVal 𝒪[M] (integerAlgEquiv K M σ' y - y))
  have hy₁ : lowerIndex K M σ' = addVal 𝒪[M] (integerAlgEquiv K M σ' y₀ - y₀) := hy₀.symm
  rw [hsum, hy₁, ← hv]
  apply le_antisymm
  · rw [addVal_le_iff_dvd, ← ha1]
    refine dvd_prod a 1 _ (s : 𝒪[L] →+* 𝒪[L]) fun i => ?_
    set f : 𝒪[L][X] := ∏ τ, (X - C (a τ)) with hf
    have hfr : ∀ ρ, r ρ (f.coeff i) = f.coeff i := by
      intro ρ
      have : f.map (r ρ : 𝒪[L] →+* 𝒪[L]) = f := by
        rw [hf, Polynomial.map_prod]
        refine Fintype.prod_equiv (Equiv.mulLeft ρ) _ _ fun τ => ?_
        rw [Polynomial.map_sub, map_X, map_C]
        rfl
      conv_rhs => rw [← this, coeff_map]
      rfl
    obtain ⟨m, hm⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := M)
      ((f.coeff i : 𝒪[L]) : L)).2 fun ρ => congrArg Subtype.val (hfr ρ)
    have hm1 : m ∈ 𝒪[M] := by
      have h1 : valuation L (algebraMap M L m) ≤ 1 := by rw [hm]; exact (f.coeff i).2
      exact (Valuation.HasExtension.val_map_le_one_iff (valuation M) (valuation L) m).1 h1
    have hy : f.coeff i = algebraMap 𝒪[M] 𝒪[L] ⟨m, hm1⟩ := Subtype.ext hm.symm
    rw [hy, RingHom.coe_coe, hcomm, ← map_sub]
    apply _root_.map_dvd
    rw [← addVal_le_iff_dvd, ← hy₁]
    exact lowerIndex_le _ _
  · rw [addVal_le_iff_dvd, map_sub, ← hcomm]
    have hz : algebraMap 𝒪[M] 𝒪[L] y₀ ∈ Algebra.adjoin 𝒪[K] {x} := hx ▸ trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨g, hg⟩ := hz
    replace hg : aeval x g = algebraMap 𝒪[M] 𝒪[L] y₀ := hg
    refine prod_dvd_sub a hinj x _ (s : 𝒪[L] →ₐ[𝒪[K]] 𝒪[L]) g (fun τ => ?_) hg
    rw [← hfix τ, ← hg]
    exact aeval_algHom_apply (r τ) x g
