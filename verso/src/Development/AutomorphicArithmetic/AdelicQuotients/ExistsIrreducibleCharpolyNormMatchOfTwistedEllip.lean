import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

/- English proof (translation)
Introduce `hN1 hN2 F E _ _ _ _ _ _ σ hgen n _ δ hδ`. Take `⟨p, hp, hpm⟩` from `hδ`. Establish `hℓ : σ ^ Module.finrank F E = 1`. Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Conclude with `pow_card_eq_one'`.

Establish `hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1`. Rewrite using `[← sigmaGL_pow, hℓ, sigmaGL_one]`. Establish `hc : ∀ d h : GL (Fin n) E, normGL σ (h⁻¹ * d * sigmaGL σ h) = h⁻¹ * normGL σ d * h` using `fun d h => twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ h d`. Establish `hreg : IsTwRegSemisimple σ δ`. Unfold `IsTwRegSemisimple`.

Rewrite using `[← hpm]`. Conclude with `hp.separable.map`. Take `⟨h, γ, hγ⟩` from `hN1 F E σ hgen n δ hreg`. Establish `hv : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E)` using `rfl`. Establish `hγp : (γ : Matrix (Fin n) (Fin n) F).charpoly = p`.

Apply `Polynomial.map_injective (algebraMap F E) (algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[hpm, ← Matrix.charpoly_map, ← hv, ← hγ, hc, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']`. Use `⟨γ, hγp ▸ hp, fun γ' hγ' => ?_⟩` and prove the remaining obligations. Establish `hr : IsRegSemisimple γ`. Unfold `IsRegSemisimple`.

Rewrite using `[hγp]`. Conclude with `hp.separable`. Establish `hr' : IsRegSemisimple γ'`. Unfold `IsRegSemisimple`. Rewrite using `[hγ', hγp]`.

Conclude with `hp.separable`. Take `⟨g, hg⟩` from `(hN2 F E σ hgen n).2 γ γ' hr hγ'.symm`. Establish `h0 : normGL σ ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) = incl γ'`. Rewrite using `[hc, hγ, hg, map_mul, map_mul, map_inv]`. Use `⟨⟨_, h0⟩, fun δ' hδ' => ?_⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `(hN2 F E σ hgen n).1 δ' _ γ' hr' hδ' h0`. Use `⟨k * (incl g)⁻¹ * h⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, map_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.exists_irreducible_charpoly_norm_match_of_twistedElliptic :
    N1 → N2 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ δ : GL (Fin n) E, EllElt σ δ →
        ∃ γ : GL (Fin n) F, Irreducible (γ : Matrix (Fin n) (Fin n) F).charpoly ∧
          ∀ γ' : GL (Fin n) F, (γ' : Matrix (Fin n) (Fin n) F).charpoly = (γ : Matrix (Fin n) (Fin n) F).charpoly →
            (∃ δ' : GL (Fin n) E, normGL σ δ' = incl γ') ∧
            ∀ δ' : GL (Fin n) E, normGL σ δ' = incl γ' → ∃ h : GL (Fin n) E, δ = h⁻¹ * δ' * sigmaGL σ h := by
  intro hN1 hN2 F E _ _ _ _ _ _ σ hgen n _ δ hδ
  obtain ⟨p, hp, hpm⟩ := hδ
  have hℓ : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have hc : ∀ d h : GL (Fin n) E, normGL σ (h⁻¹ * d * sigmaGL σ h) = h⁻¹ * normGL σ d * h :=
    fun d h => twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ h d
  have hreg : IsTwRegSemisimple σ δ := by
    unfold IsTwRegSemisimple
    rw [← hpm]
    exact hp.separable.map
  obtain ⟨h, γ, hγ⟩ := hN1 F E σ hgen n δ hreg
  have hv : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E) := rfl
  have hγp : (γ : Matrix (Fin n) (Fin n) F).charpoly = p := by
    apply Polynomial.map_injective (algebraMap F E) (algebraMap F E).injective
    rw [hpm, ← Matrix.charpoly_map, ← hv, ← hγ, hc, Units.val_mul, Units.val_mul,
      Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  refine ⟨γ, hγp ▸ hp, fun γ' hγ' => ?_⟩
  have hr : IsRegSemisimple γ := by
    unfold IsRegSemisimple
    rw [hγp]; exact hp.separable
  have hr' : IsRegSemisimple γ' := by
    unfold IsRegSemisimple
    rw [hγ', hγp]; exact hp.separable
  obtain ⟨g, hg⟩ := (hN2 F E σ hgen n).2 γ γ' hr hγ'.symm
  have h0 : normGL σ ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) = incl γ' := by
    rw [hc, hγ, hg, map_mul, map_mul, map_inv]
  refine ⟨⟨_, h0⟩, fun δ' hδ' => ?_⟩
  obtain ⟨k, hk⟩ := (hN2 F E σ hgen n).1 δ' _ γ' hr' hδ' h0
  refine ⟨k * (incl g)⁻¹ * h⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv]
  calc δ = h * incl g * ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) *
        (sigmaGL σ (incl g))⁻¹ * (sigmaGL σ h)⁻¹ := by group
    _ = _ := by rw [hk]; group
