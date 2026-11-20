import Formalism.HyperbolicPlaceProducts.Statement

open Module

noncomputable section

namespace Formalism.SLP.P

/- English proof (translation)
Set `f : R →ₗ[R] M` to `LinearMap.toSpanSingleton R M v`. Set `I : Ideal R` to `N.comap f`. Set `J : Ideal R` to `LinearMap.ker f`. Establish `hJI : J ≤ I` using `fun r hr => by show f r ∈ N`. Rewrite using `[LinearMap.mem_ker.1 hr]`.

Conclude with `N.zero_mem`. Establish `key : ∃ x, J ⊔ Ideal.span {x} = I`. Distinguish the cases in `hJ : J = ⊥`. Establish `hinj : Function.Injective f` using `LinearMap.ker_eq_bot.1 hJ`. Use `haveI : Finite R := Finite.of_injective f hinj`.

Establish `hF : IsField R` using `Finite.isField_of_domain R`. Distinguish the cases in `hI : I = ⊥`. Conclude with `⟨0, by rw [hJ, hI]; simp⟩`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Take `⟨b, hb⟩` from `hF.mul_inv_cancel ha0`.

Establish `hIt : I = ⊤` using `(Ideal.eq_top_iff_one I).2 (by rw [← hb]; exact I.mul_mem_right b ha)`. Conclude with `⟨1, by rw [hIt, Ideal.span_singleton_one, sup_top_eq]⟩`. Conclude with `IsDedekindDomain.exists_sup_span_eq hJI hJ`. Take `⟨x, hx⟩` from `key`. Use `⟨x • v, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Establish `hxI : x ∈ I` using `hx ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)`. Establish `hfx : f x ∈ N` using `hxI`. Simplify `hfx` using `[f]`. Introduce `n hn`.

Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 (hN hn)`. Establish `hr : r ∈ I` using `by show f r ∈ N`. Simplify `hn` using `[f]`. Rewrite `hr` using `[← hx, Submodule.mem_sup]`. Take `⟨j, hj, y, hy, rfl⟩` from `hr`.

Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Establish `hjv : j • v = 0` using `by simpa [f] using LinearMap.mem_ker.1 hj`. Rewrite using `[Submodule.mem_span_singleton]`. Conclude with `⟨s, by rw [add_smul, hjv, zero_add, mul_smul]⟩`.
-/
private theorem exists_span_singleton_eq_of_le_span_singleton {R M : Type} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [Finite M] (v : M) (N : Submodule R M)
    (hN : N ≤ R ∙ v) : ∃ t : M, (R ∙ t) = N := by
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M v
  let I : Ideal R := N.comap f
  let J : Ideal R := LinearMap.ker f
  have hJI : J ≤ I := fun r hr => by
    show f r ∈ N
    rw [LinearMap.mem_ker.1 hr]
    exact N.zero_mem
  have key : ∃ x, J ⊔ Ideal.span {x} = I := by
    by_cases hJ : J = ⊥
    ·
      have hinj : Function.Injective f := LinearMap.ker_eq_bot.1 hJ
      haveI : Finite R := Finite.of_injective f hinj
      have hF : IsField R := Finite.isField_of_domain R
      by_cases hI : I = ⊥
      · exact ⟨0, by rw [hJ, hI]; simp⟩
      · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
        obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
        have hIt : I = ⊤ := (Ideal.eq_top_iff_one I).2 (by rw [← hb]; exact I.mul_mem_right b ha)
        exact ⟨1, by rw [hIt, Ideal.span_singleton_one, sup_top_eq]⟩
    · exact IsDedekindDomain.exists_sup_span_eq hJI hJ
  obtain ⟨x, hx⟩ := key
  refine ⟨x • v, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    have hxI : x ∈ I := hx ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
    have hfx : f x ∈ N := hxI
    simpa [f] using hfx
  · intro n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 (hN hn)
    have hr : r ∈ I := by
      show f r ∈ N
      simpa [f] using hn
    rw [← hx, Submodule.mem_sup] at hr
    obtain ⟨j, hj, y, hy, rfl⟩ := hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hjv : j • v = 0 := by simpa [f] using LinearMap.mem_ker.1 hj
    rw [Submodule.mem_span_singleton]
    exact ⟨s, by rw [add_smul, hjv, zero_add, mul_smul]⟩

/- English proof (translation)
Introduce `e`. Proceed by induction on `e with`. Consider the case `zero`. Introduce `v N hN`. Use `⟨v, ?_⟩` and prove the remaining obligations.

Rewrite `hN`, the goal using `[Set.range_eq_empty v, Submodule.span_empty]`. Conclude with `(le_bot_iff.1 hN).symm`. Consider the case `succ e ih`. Introduce `v N hN`. Use `set S' : Submodule R M := Submodule.span R (Set.range (Fin.tail v)) with hS'`.

Establish `hv : Submodule.span R (Set.range v) = (R ∙ v 0) ⊔ S'` using `by conv_lhs => rw [← Fin.cons_self_tail v]`. Rewrite using `[Fin.range_cons, Submodule.span_insert]`. Use `haveI : Finite (M ⧸ S') := Finite.of_surjective _ (Submodule.mkQ_surjective S')`. Establish `hπ : N.map S'.mkQ ≤ R ∙ S'.mkQ (v 0)`. Rewrite using `[Submodule.map_le_iff_le_comap]`.

Introduce `n hn`. Establish `h` using `hN hn`. Rewrite `h` using `[hv, Submodule.mem_sup]`. Take `⟨a, ha, b, hb, rfl⟩` from `h`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 ha`.

Rewrite using `[Submodule.mem_comap, map_add, map_smul]`. Establish `hb0 : S'.mkQ b = 0` using `(Submodule.Quotient.mk_eq_zero S').2 hb`. Rewrite using `[hb0, add_zero]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Take `⟨t', ht'⟩` from `exists_span_singleton_eq_of_le_span_singleton (S'.mkQ (v 0)) (N.map S'.mkQ) hπ`.

Establish `ht'm : t' ∈ N.map S'.mkQ` using `ht' ▸ Submodule.mem_span_singleton_self t'`. Take `⟨n0, hn0, hn0t⟩` from `ht'm`. Take `⟨u, hu⟩` from `ih (Fin.tail v) (N ⊓ S') inf_le_right`. Use `⟨Fin.cons n0 u, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.range_cons, Submodule.span_insert, hu]`.

Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hn0) inf_le_left`. Introduce `n hn`. Establish `hπn : S'.mkQ n ∈ R ∙ S'.mkQ n0`. Rewrite using `[hn0t, ht']`.

Conclude with `Submodule.mem_map_of_mem hn`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 hπn`. Establish `hd : n - r • n0 ∈ S'`. Establish `h0 : S'.mkQ (n - r • n0) = 0` using `by rw [map_sub, map_smul, hr, sub_self]`. Conclude with `(Submodule.Quotient.mk_eq_zero S').1 h0`.

Rewrite using `[Submodule.mem_sup]`. Conclude with `⟨r • n0, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), n - r • n0, ⟨N.sub_mem hn (N.smul_mem _ hn0), hd⟩, by abel⟩`.
-/
theorem exists_family_span_eq_of_le {R M : Type} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [Finite M] :
    ∀ (e : ℕ) (v : Fin e → M) (N : Submodule R M), N ≤ Submodule.span R (Set.range v) →
      ∃ t : Fin e → M, Submodule.span R (Set.range t) = N := by
  intro e
  induction e with
  | zero =>
    intro v N hN
    refine ⟨v, ?_⟩
    rw [Set.range_eq_empty v, Submodule.span_empty] at hN ⊢
    exact (le_bot_iff.1 hN).symm
  | succ e ih =>
    intro v N hN
    set S' : Submodule R M := Submodule.span R (Set.range (Fin.tail v)) with hS'
    have hv : Submodule.span R (Set.range v) = (R ∙ v 0) ⊔ S' := by
      conv_lhs => rw [← Fin.cons_self_tail v]
      rw [Fin.range_cons, Submodule.span_insert]
    haveI : Finite (M ⧸ S') := Finite.of_surjective _ (Submodule.mkQ_surjective S')

    have hπ : N.map S'.mkQ ≤ R ∙ S'.mkQ (v 0) := by
      rw [Submodule.map_le_iff_le_comap]
      intro n hn
      have h := hN hn
      rw [hv, Submodule.mem_sup] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 ha
      rw [Submodule.mem_comap, map_add, map_smul]
      have hb0 : S'.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero S').2 hb
      rw [hb0, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨t', ht'⟩ := exists_span_singleton_eq_of_le_span_singleton (S'.mkQ (v 0)) (N.map S'.mkQ) hπ
    have ht'm : t' ∈ N.map S'.mkQ := ht' ▸ Submodule.mem_span_singleton_self t'
    obtain ⟨n0, hn0, hn0t⟩ := ht'm
    obtain ⟨u, hu⟩ := ih (Fin.tail v) (N ⊓ S') inf_le_right
    refine ⟨Fin.cons n0 u, ?_⟩
    rw [Fin.range_cons, Submodule.span_insert, hu]
    apply le_antisymm
    · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hn0) inf_le_left
    · intro n hn
      have hπn : S'.mkQ n ∈ R ∙ S'.mkQ n0 := by
        rw [hn0t, ht']
        exact Submodule.mem_map_of_mem hn
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hπn
      have hd : n - r • n0 ∈ S' := by
        have h0 : S'.mkQ (n - r • n0) = 0 := by rw [map_sub, map_smul, hr, sub_self]
        exact (Submodule.Quotient.mk_eq_zero S').1 h0
      rw [Submodule.mem_sup]
      exact ⟨r • n0, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), n - r • n0,
        ⟨N.sub_mem hn (N.smul_mem _ hn0), hd⟩, by abel⟩

/- English proof (translation)
Introduce `R M _ _ _ _ _ e v hv`. Establish `hsurj : Function.Surjective (fun t : Fin e → M => Submodule.span R (Set.range t))`. Introduce `N`. Conclude with `exists_family_span_eq_of_le e v N (by rw [hv]; exact le_top)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem card_submodules_le_of_dedekind : Formalism.SLP.SubmoduleCountDed := by
  intro R M _ _ _ _ _ e v hv
  have hsurj : Function.Surjective
      (fun t : Fin e → M => Submodule.span R (Set.range t)) := by
    intro N
    exact exists_family_span_eq_of_le e v N (by rw [hv]; exact le_top)
  calc Nat.card (Submodule R M) ≤ Nat.card (Fin e → M) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card M ^ e := by
        rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Formalism.SLP.P

end
