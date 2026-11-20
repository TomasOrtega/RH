import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotExtend
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotOfSpan

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Use `set I := (maximalIdeal A).map (algebraMap A B) with hI`. Take `⟨s, y, -, hy, hs⟩` from `cotInd_extend A κ x hx`. Take `⟨t, w, -, hw, ht⟩` from `cotInd_extend (B ⧸ I) Empty (fun e => e.elim) ⟨fun e => e.elim, fun _ _ e => e.elim⟩`. Use `choose v hv using fun j => Ideal.Quotient.mk_surjective (w j)`. Establish `hw' : Ideal.span (Set.range w) = maximalIdeal (B ⧸ I)`.

Rewrite using `[← hw, Set.Sum.elim_range, Set.range_eq_empty (ι := Empty), Set.empty_union]`. Establish `hmap : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I)` using `IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hIle : I ≤ maximalIdeal B` using `IsLocalRing.map_maximalIdeal_le _`. Use `⟨s, t, Sum.elim (fun i => algebraMap A B (Sum.elim x y i)) v, fun k => rfl, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Sum.elim_range, Ideal.span_union]`.

Establish `h1 : Ideal.span (Set.range fun i => algebraMap A B (Sum.elim x y i)) = I`. Rewrite using `[hI, ← hy, Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `h2 : (Ideal.span (Set.range v)).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I)`. Rewrite using `[Ideal.map_span, ← Set.range_comp, ← hw']`.

Use `congr 2`. Use function extensionality and compare the values at `j`. Conclude with `hv j`. Establish `h3` using `congrArg (Ideal.comap (Ideal.Quotient.mk I)) (h2.trans hmap.symm)`. Rewrite `h3` using `[Ideal.comap_map_quotientMk, Ideal.comap_map_quotientMk, sup_eq_right.2 hIle]`.

Rewrite using `[h1, h3]`. Use `haveI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat`. Establish `H` using `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)`. Rewrite `H` using `[← hI, hmap]`. Establish `H'` using `congrArg (fun a : ℕ∞ => (a : WithBot ℕ∞)) H`.

Simplify using `only [WithBot.coe_add, IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at H'`. Rewrite using `[H', ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A), ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B ⧸ I), ← hs, ← ht]`. Simplify using the standard rewrite rules.
-/
private theorem flat_regular_cotangent_extension
    (A B : Type) [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))]
    (κ : Type) [Fintype κ] (x : κ → A) (hx : CotInd A x) :
    ∃ (s t : ℕ) (z : (κ ⊕ Fin s) ⊕ Fin t → B), (∀ k, z (Sum.inl (Sum.inl k)) = algebraMap A B (x k)) ∧
      Ideal.span (Set.range z) = maximalIdeal B ∧
      ((Fintype.card ((κ ⊕ Fin s) ⊕ Fin t) : ℕ) : WithBot ℕ∞) = ringKrullDim B := by
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  obtain ⟨s, y, -, hy, hs⟩ := cotInd_extend A κ x hx
  obtain ⟨t, w, -, hw, ht⟩ := cotInd_extend (B ⧸ I) Empty (fun e => e.elim)
    ⟨fun e => e.elim, fun _ _ e => e.elim⟩
  choose v hv using fun j => Ideal.Quotient.mk_surjective (w j)
  have hw' : Ideal.span (Set.range w) = maximalIdeal (B ⧸ I) := by
    rw [← hw, Set.Sum.elim_range, Set.range_eq_empty (ι := Empty), Set.empty_union]
  have hmap : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hIle : I ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le _
  refine ⟨s, t, Sum.elim (fun i => algebraMap A B (Sum.elim x y i)) v, fun k => rfl, ?_, ?_⟩
  · rw [Set.Sum.elim_range, Ideal.span_union]
    have h1 : Ideal.span (Set.range fun i => algebraMap A B (Sum.elim x y i)) = I := by
      rw [hI, ← hy, Ideal.map_span, ← Set.range_comp]
      rfl
    have h2 : (Ideal.span (Set.range v)).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) := by
      rw [Ideal.map_span, ← Set.range_comp, ← hw']
      congr 2
      funext j
      exact hv j
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) (h2.trans hmap.symm)
    rw [Ideal.comap_map_quotientMk, Ideal.comap_map_quotientMk, sup_eq_right.2 hIle] at h3
    rw [h1, h3]
  · haveI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
    have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
    rw [← hI, hmap] at H
    have H' := congrArg (fun a : ℕ∞ => (a : WithBot ℕ∞)) H
    simp only [WithBot.coe_add, IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at H'
    rw [H', ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A),
      ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B ⧸ I), ← hs, ← ht]
    simp

/- English proof (translation)
Introduce `A B _ _ _ _ _ _ _ _ _`. Prove the components needed by the constructor for the conclusion. Take `⟨s, t, z, -, hz, hc⟩` from `flat_regular_cotangent_extension A B Empty (fun e => e.elim) ⟨fun e => e.elim, fun _ _ e => e.elim⟩`. Apply `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` to reduce the goal to its premises. Rewrite using `[← hc, ← hz, Nat.cast_le]`.

Use `(Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_` and prove the remaining obligations. Rewrite using `[← Set.image_univ, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]`. Conclude with `Set.ncard_image_le`. Introduce `κ _ x hx`. Take `⟨s, t, z, hzx, hz, hc⟩` from `flat_regular_cotangent_extension A B κ x hx`.

Establish `h1` using `ringKrullDim_le_spanFinrank_maximalIdeal B`. Rewrite `h1` using `[← hc, Nat.cast_le]`. Establish `h2` using `(cotInd_of_span B _ z hz h1).comp (fun k : κ => Sum.inl (Sum.inl k)) (Sum.inl_injective.comp Sum.inl_injective)`. Establish `h3 : (z ∘ fun k : κ => Sum.inl (Sum.inl k)) = fun k => algebraMap A B (x k)` using `funext hzx`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.AlgebraTools.regular_of_flat_fibre :
    ∀ (A B : Type) [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
      [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))],
      IsRegularLocalRing B ∧ ∀ (κ : Type) [Fintype κ] (x : κ → A), CotInd A x → CotInd B (fun k => algebraMap A B (x k)) := by
  intro A B _ _ _ _ _ _ _ _ _
  constructor
  · obtain ⟨s, t, z, -, hz, hc⟩ := flat_regular_cotangent_extension A B Empty (fun e => e.elim)
      ⟨fun e => e.elim, fun _ _ e => e.elim⟩
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hc, ← hz, Nat.cast_le]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
    rw [← Set.image_univ, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_image_le
  · intro κ _ x hx
    obtain ⟨s, t, z, hzx, hz, hc⟩ := flat_regular_cotangent_extension A B κ x hx
    have h1 := ringKrullDim_le_spanFinrank_maximalIdeal B
    rw [← hc, Nat.cast_le] at h1
    have h2 := (cotInd_of_span B _ z hz h1).comp (fun k : κ => Sum.inl (Sum.inl k))
      (Sum.inl_injective.comp Sum.inl_injective)
    have h3 : (z ∘ fun k : κ => Sum.inl (Sum.inl k)) = fun k => algebraMap A B (x k) := funext hzx
    rwa [h3] at h2
