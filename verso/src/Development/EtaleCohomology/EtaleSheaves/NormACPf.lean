import Development.EtaleCohomology.EtaleSheaves.CompCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CompCut

namespace LateralTheory.E.NormACPf

/- English proof (translation)
Introduce `p hp hd`. Take `⟨a, ha⟩` from `hK (p.map (integralClosure A K).val.toRingHom) (hp.map _) (by rwa [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective])`. Establish `hint : IsIntegral (integralClosure A K) a` using `⟨p, hp, by`. Rewrite `ha` using `[Polynomial.eval_map]`. Conclude with `ha⟩`.

Establish `haA : a ∈ integralClosure A K` using `isIntegral_trans (R := A) a hint`. Use `⟨⟨a, haA⟩, Subtype.val_injective ?_⟩` and prove the remaining obligations. Establish `h4 : (integralClosure A K).val.toRingHom (Polynomial.eval (⟨a, haA⟩ : integralClosure A K) p) = 0`. Rewrite using `[← Polynomial.eval₂_at_apply]`. Rewrite `ha` using `[Polynomial.eval_map]`.

Conclude with `ha`. Simplify using `using h4`.
-/
theorem aic_integralClosure (A K : Type) [CommRing A] [CommRing K] [Algebra A K] (hK : AIC K) :
    AIC (integralClosure A K) := by
  intro p hp hd
  obtain ⟨a, ha⟩ := hK (p.map (integralClosure A K).val.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective])
  have hint : IsIntegral (integralClosure A K) a := ⟨p, hp, by
    rw [Polynomial.eval_map] at ha; exact ha⟩
  have haA : a ∈ integralClosure A K := isIntegral_trans (R := A) a hint
  refine ⟨⟨a, haA⟩, Subtype.val_injective ?_⟩
  have h4 : (integralClosure A K).val.toRingHom (Polynomial.eval (⟨a, haA⟩ : integralClosure A K) p) = 0 := by
    rw [← Polynomial.eval₂_at_apply]; rw [Polynomial.eval_map] at ha; exact ha
  simpa using h4

/- English proof (translation)
Introduce `_ _ _` and use `⟨0, Subsingleton.elim _ _⟩`.
-/
theorem aic_of_subsingleton (R : Type) [CommRing R] [Subsingleton R] : AIC R :=
  fun _ _ _ => ⟨0, Subsingleton.elim _ _⟩

/- English proof (translation)
Introduce `p hp hd`. Take `⟨a, ha⟩` from `h (p.map e.symm.toRingHom) (hp.map _) (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])`. Use `⟨e a, ?_⟩` and prove the remaining obligations. Establish `h4 : e.symm.toRingHom (Polynomial.eval (e a) p) = 0`. Rewrite using `[← Polynomial.eval₂_at_apply]`.

Rewrite `ha` using `[Polynomial.eval_map]`. Simplify using `using ha`. Simplify using `using h4`.
-/
theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have h4 : e.symm.toRingHom (Polynomial.eval (e a) p) = 0 := by
    rw [← Polynomial.eval₂_at_apply]; rw [Polynomial.eval_map] at ha; simpa using ha
  simpa using h4

/- English proof (translation)
Distinguish the cases in `h : (default : Spec (CommRingCat.of K)) ∈ W`. Establish `: W = ⊤`. Use extensionality with `x`. Simplify using `only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]`. Rewrite using `[Subsingleton.elim x default]` and apply the resulting hypothesis.

Substitute `this` using the available equality. Conclude with `aic_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm hA`. Establish `: W = ⊥`. Use extensionality with `x`. Simplify using `only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]`.

Rewrite using `[Subsingleton.elim x default]` and apply the resulting hypothesis. Substitute `this` using the available equality. Conclude with `aic_of_subsingleton _`.
-/
theorem aic_spec_field (K : Type) [Field K] (hA : AIC K) (W : (Spec (CommRingCat.of K)).Opens) :
    AIC Γ(Spec (CommRingCat.of K), W) := by
  by_cases h : (default : Spec (CommRingCat.of K)) ∈ W
  · have : W = ⊤ := by
      ext x; simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rwa [Subsingleton.elim x default]
    subst this
    exact aic_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm hA
  · have : W = ⊥ := by
      ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      rwa [Subsingleton.elim x default]
    subst this
    exact aic_of_subsingleton _

def Loc : Prop := ∀ (Z : Scheme.{0}), IsIntegral Z → (∀ z : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U ∧ AIC Γ(Z, U)) →
  ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U)

/- English proof (translation)
Introduce `P _ _ K _ hF hA v`. Set `` to `hF.toField`. Establish `hI : IsIntegral v.normalization` using `inferInstance`. Use `⟨hI, hL _ hI ?_⟩` and prove the remaining obligations. Introduce `z`.

Take `⟨V, hV, hz, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens (show v.fromNormalization z ∈ (⊤ : P.Opens) from trivial)`. Use `⟨v.fromNormalization ⁻¹ᵁ V, hV.preimage _, hz, ?_⟩` and prove the remaining obligations. Use `letI := (v.app V).hom.toAlgebra`. Conclude with `aic_of_ringEquiv (v.normalizationObjIso hV).commRingCatIsoToRingEquiv.symm (aic_integralClosure _ _ (aic_spec_field K hA _))`.
-/
theorem NormAC_of (hL : Loc) : NormAC := by
  intro P _ _ K _ hF hA v
  let := hF.toField
  have hI : IsIntegral v.normalization := inferInstance
  refine ⟨hI, hL _ hI ?_⟩
  intro z
  obtain ⟨V, hV, hz, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens
    (show v.fromNormalization z ∈ (⊤ : P.Opens) from trivial)
  refine ⟨v.fromNormalization ⁻¹ᵁ V, hV.preimage _, hz, ?_⟩
  letI := (v.app V).hom.toAlgebra
  exact aic_of_ringEquiv (v.normalizationObjIso hV).commRingCatIsoToRingEquiv.symm
    (aic_integralClosure _ _ (aic_spec_field K hA _))

end LateralTheory.E.NormACPf
