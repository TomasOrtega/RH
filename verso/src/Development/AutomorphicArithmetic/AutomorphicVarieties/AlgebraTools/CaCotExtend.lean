import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `R _ _ _ κ _ x hx`. Take `⟨hm, hli⟩` from `(cotInd_iff R x).mp hx`. Use `set v : κ → CotangentSpace R := fun k => (maximalIdeal R).toCotangent ⟨x k, hm k⟩ with hv`. Set `bW` to `Module.Basis.span hli`. Set `bQ` to `Module.finBasis (ResidueField R) (CotangentSpace R ⧸ Submodule.span (ResidueField R) (Set.range v))`.

Set `B` to `Module.Basis.sumQuot bW bQ`. Use `choose z hz using fun i => (maximalIdeal R).toCotangent_surjective (B (Sum.inr i))`. Use `⟨_, fun i => (z i : R), ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ j, Sum.elim x (fun i => (z i : R)) j ∈ maximalIdeal R`. Introduce and unpack `(k | i)`.

Conclude with `hm k`. Conclude with `(z i).2`. Establish `hB : (fun j => (maximalIdeal R).toCotangent ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩) = ⇑B`. Use function extensionality and compare the values at `j`. Break down `j with k | i` into its components or cases.

Simplify using `[B, bW, Module.Basis.span_apply, hv]`. Simplify using `using hz i`. Establish `hfg : (maximalIdeal R).FG` using `IsNoetherian.noetherian _`. Use `⟨(cotInd_iff R _).mpr ⟨hmem, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hB]`.

Conclude with `B.linearIndependent`. Set `g : κ ⊕ Fin _ → maximalIdeal R` to `fun j => ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩`. Establish `hspan : Submodule.span R (Set.range g) = ⊤`. Rewrite using `[← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]`. Establish `: (maximalIdeal R).toCotangent ∘ g = ⇑B` using `hB`.

Rewrite using `[this, B.span_eq]`. Use `congrArg (Submodule.map (maximalIdeal R).subtype) hspan` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`. Conclude with `this`. Rewrite using `[spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg, Module.finrank_eq_card_basis B, Fintype.card_sum, Fintype.card_fin]`.
-/
theorem UpperTheory.V.AlgebraTools.cotInd_extend :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∃ (s : ℕ) (y : Fin s → R), CotInd R (Sum.elim x y) ∧
        Ideal.span (Set.range (Sum.elim x y)) = maximalIdeal R ∧
        Fintype.card κ + s = (maximalIdeal R).spanFinrank := by
  intro R _ _ _ κ _ x hx
  obtain ⟨hm, hli⟩ := (cotInd_iff R x).mp hx
  set v : κ → CotangentSpace R := fun k => (maximalIdeal R).toCotangent ⟨x k, hm k⟩ with hv
  let bW := Module.Basis.span hli
  let bQ := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ Submodule.span (ResidueField R) (Set.range v))
  let B := Module.Basis.sumQuot bW bQ
  choose z hz using fun i => (maximalIdeal R).toCotangent_surjective (B (Sum.inr i))
  refine ⟨_, fun i => (z i : R), ?_⟩
  have hmem : ∀ j, Sum.elim x (fun i => (z i : R)) j ∈ maximalIdeal R := by
    rintro (k | i)
    · exact hm k
    · exact (z i).2
  have hB : (fun j => (maximalIdeal R).toCotangent ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩) = ⇑B := by
    funext j
    rcases j with k | i
    · simp [B, bW, Module.Basis.span_apply, hv]
    · simpa using hz i
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  refine ⟨(cotInd_iff R _).mpr ⟨hmem, ?_⟩, ?_, ?_⟩
  · rw [hB]
    exact B.linearIndependent
  · let g : κ ⊕ Fin _ → maximalIdeal R := fun j => ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩
    have hspan : Submodule.span R (Set.range g) = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]
      have : (maximalIdeal R).toCotangent ∘ g = ⇑B := hB
      rw [this, B.span_eq]
    have := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  · rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg, Module.finrank_eq_card_basis B,
      Fintype.card_sum, Fintype.card_fin]
