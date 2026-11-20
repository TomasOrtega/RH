import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `l Y T U hU`. Use `haveI := T.fin`. Use `letI := T.alg U`. Establish `hZ : IsAffineOpen (T.p ⁻¹ᵁ U)` using `hU.preimage T.p`. Establish `hsq : Spec.map (T.p.app U) ≫ hU.fromSpec = hZ.fromSpec ≫ T.p`.

Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `IsAffineOpen.SpecMap_appLE_fromSpec T.p hU hZ le_rfl`. Use `⟨hZ, fun B _ _ => ?_⟩` and prove the remaining obligations. Establish `hrange : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)), Set.range z.1 ⊆ Set.range hZ.fromSpec`. Introduce and unpack `z _ ⟨x, rfl⟩`.

Rewrite using `[hZ.range_fromSpec]`. Establish `hx : (z.1 ≫ T.p) x ∈ Set.range hU.fromSpec`. Rewrite using `[z.2]`. Unfold `ptOf`. Rewrite using `[Scheme.Hom.comp_apply]`.

Conclude with `⟨_, rfl⟩`. Rewrite `hx` using `[hU.range_fromSpec]`. Simplify using `using hx`. Establish `hlift : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)), Spec.map (T.p.app U ≫ Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z))) = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B))`. Introduce `z`.

Rewrite using `[← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, hsq, Spec.map_preimage, IsOpenImmersion.lift_fac_assoc]`. Conclude with `z.2`. Use `⟨{ toFun := fun g => ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hZ.fromSpec, ?_⟩, invFun := fun z => { toRingHom := (Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z))).hom commutes' := fun r => by` and prove the remaining obligations. Establish `h` using `congrArg (fun φ => φ.hom r) (Spec.map_injective (hlift z))`. Conclude with `h }`.

Use `left_inv := fun g => ?_`. Use `right_inv := fun z => ?_ }, fun z => rfl⟩`. Use `show _ = Spec.map _ ≫ hU.fromSpec`. Rewrite using `[Category.assoc, ← hsq, ← Spec.map_comp_assoc]`. Use `congr 2`.

Use extensionality with `r`. Conclude with `g.commutes r`. Apply `AlgHom.coe_ringHom_injective show (Spec.preimage _).hom = (CommRingCat.ofHom g.toRingHom).hom` to reduce the goal to its premises. Use `congr 1`. Apply `Spec.map_injective` to reduce the goal to its premises.

Rewrite using `[Spec.map_preimage]`. Conclude with `(IsOpenImmersion.lift_uniq _ _ _ _ rfl).symm`. Apply `Subtype.ext show Spec.map (Spec.preimage _) ≫ _ = _` to reduce the goal to its premises. Rewrite using `[Spec.map_preimage, IsOpenImmersion.lift_fac]`.
-/
theorem UpperTheory.Gal.crystallineComparison.secChart_of :
    SecChart := by
  intro l Y T U hU
  haveI := T.fin
  letI := T.alg U
  have hZ : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  have hsq : Spec.map (T.p.app U) ≫ hU.fromSpec = hZ.fromSpec ≫ T.p := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec T.p hU hZ le_rfl
  refine ⟨hZ, fun B _ _ => ?_⟩
  have hrange : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)),
      Set.range z.1 ⊆ Set.range hZ.fromSpec := by
    rintro z _ ⟨x, rfl⟩
    rw [hZ.range_fromSpec]
    have hx : (z.1 ≫ T.p) x ∈ Set.range hU.fromSpec := by
      rw [z.2]
      unfold ptOf
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hx
    simpa using hx
  have hlift : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)),
      Spec.map (T.p.app U ≫ Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z)))
        = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B)) := by
    intro z
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, hsq, Spec.map_preimage,
      IsOpenImmersion.lift_fac_assoc]
    exact z.2
  refine ⟨{ toFun := fun g => ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hZ.fromSpec, ?_⟩,
            invFun := fun z =>
              { toRingHom := (Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z))).hom
                commutes' := fun r => by
                  have h := congrArg (fun φ => φ.hom r) (Spec.map_injective (hlift z))
                  exact h }
            left_inv := fun g => ?_
            right_inv := fun z => ?_ }, fun z => rfl⟩
  · show _ = Spec.map _ ≫ hU.fromSpec
    rw [Category.assoc, ← hsq, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact g.commutes r
  · apply AlgHom.coe_ringHom_injective
    show (Spec.preimage _).hom = (CommRingCat.ofHom g.toRingHom).hom
    congr 1
    apply Spec.map_injective
    rw [Spec.map_preimage]
    exact (IsOpenImmersion.lift_uniq _ _ _ _ rfl).symm
  · apply Subtype.ext
    show Spec.map (Spec.preimage _) ≫ _ = _
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
