import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IInfMapLeMapIInfOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatComapMapOfOneTmulMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealSheafMapOfAffineCoverPreimageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealMapOfGermsAffineSchemeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecTensorToPullbackSectionsCompatStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlatPush

/- English proof (translation)
Establish `hf : (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) = X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo ξ`. Rewrite using `[Scheme.germ_stalkClosedPointTo]`. Both sides reduce to the same expression. Rewrite using `[hf, CommRingCat.hom_comp]`. Use `RingHom.Flat.comp ?_ hfl` and prove the remaining obligations.

Use `letI : Algebra Γ(X, U) (X.presheaf.stalk (ξ (closedPoint R))) := X.presheaf.algebra_section_stalk ⟨_, hx⟩`. Use `haveI := U.2.isLocalization_stalk ⟨_, hx⟩`. Establish `: Module.Flat Γ(X, U) (X.presheaf.stalk (ξ (closedPoint R)))` using `IsLocalization.flat _ (U.2.primeIdealOf ⟨_, hx⟩).asIdeal.primeCompl`. Conclude with `this`.
-/
theorem flat_sections_to_chart {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens)
    (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (hx : ξ (closedPoint R) ∈ (U : X.Opens)) (hfl : (Scheme.stalkClosedPointTo ξ).hom.Flat) :
    (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.Flat := by
  have hf : (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) =
      X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo ξ := by
    rw [Scheme.germ_stalkClosedPointTo]; rfl
  rw [hf, CommRingCat.hom_comp]
  refine RingHom.Flat.comp ?_ hfl
  letI : Algebra Γ(X, U) (X.presheaf.stalk (ξ (closedPoint R))) := X.presheaf.algebra_section_stalk ⟨_, hx⟩
  haveI := U.2.isLocalization_stalk ⟨_, hx⟩
  have : Module.Flat Γ(X, U) (X.presheaf.stalk (ξ (closedPoint R))) := IsLocalization.flat _ (U.2.primeIdealOf ⟨_, hx⟩).asIdeal.primeCompl
  exact this

/- English proof (translation)
Use `letI := (ρ.appLE U W hW).hom.toAlgebra`. Use `letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra`. Take `⟨κ, hκ, hL, hR⟩` from `GlobalTheory.T.exists_specTensor_to_pullback_sections_compat ρ ξ U hle W hW`. Take `⟨s0, hs0⟩ : ∃ s0, (pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h) = s0` from `⟨_, rfl⟩`. Rewrite `hh` using `[hs0]`.

Establish `hs : ∀ t, ((Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).presheaf.germ ⊤ t trivial).hom (κ.appTop.hom s0) ∈ FinalTheorems.stalkId (I.comap (κ ≫ pullback.snd ξ ρ)) t`. Introduce `t`. Establish `e` using `Scheme.Hom.germ_stalkMap_apply κ ⊤ t trivial s0`. Rewrite using `[Scheme.IdealSheafData.comap_comp]`. Use `GlobalTheory.VanStalk.map_le_stalkId_comap κ _ t ?_` and prove the remaining obligations.

Establish `: (κ.stalkMap t).hom (((pullback ξ ρ).presheaf.germ ⊤ (κ t) trivial).hom s0) ∈ _` using `Ideal.mem_map_of_mem _ (hh (κ t))`. Rewrite `this` using `[e]`. Conclude with `this`. Establish `h4` using `GlobalTheory.T.mem_ideal_map_of_germs_affineScheme (κ ≫ pullback.snd ξ ρ) I W hκ _ hs`. Establish `h5` using `Ideal.mem_map_of_mem (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).hom.hom h4`.

Rewrite `h5` using `[Ideal.map_map]`. Establish `e1 : (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom s0) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] h`. Rewrite using `[← hR h, ← hs0]`. Establish `e2 : (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).hom.hom.comp ((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom = Algebra.TensorProduct.includeLeftRingHom`. Use extensionality with `c`.

Conclude with `hL c`. Rewrite `h5` using `[e1, e2]`. Then use the resulting hypothesis.
-/
theorem tmul_mem_of_germ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) (I : Y'.IdealSheafData) {R : Type} [CommRing R]
    (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens)
    (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)) (h : R)
    (hh : ∀ v : ↥(pullback ξ ρ : Scheme.{0}), ((pullback ξ ρ).presheaf.germ ⊤ v trivial).hom
      ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h)) ∈
        FinalTheorems.stalkId (I.comap (pullback.snd ξ ρ)) v) :
    letI := (ρ.appLE U W hW).hom.toAlgebra
    letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
    (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] h ∈ (I.ideal W).map
      (Algebra.TensorProduct.includeLeftRingHom : Γ(Y', W) →+* Γ(Y', W) ⊗[Γ(X, U)] R) := by
  letI := (ρ.appLE U W hW).hom.toAlgebra
  letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  obtain ⟨κ, hκ, hL, hR⟩ := GlobalTheory.T.exists_specTensor_to_pullback_sections_compat ρ ξ U hle W hW
  obtain ⟨s0, hs0⟩ : ∃ s0, (pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h) = s0 :=
    ⟨_, rfl⟩
  rw [hs0] at hh
  have hs : ∀ t, ((Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).presheaf.germ ⊤ t trivial).hom
      (κ.appTop.hom s0) ∈ FinalTheorems.stalkId (I.comap (κ ≫ pullback.snd ξ ρ)) t := by
    intro t
    have e := Scheme.Hom.germ_stalkMap_apply κ ⊤ t trivial s0
    rw [Scheme.IdealSheafData.comap_comp]
    refine GlobalTheory.VanStalk.map_le_stalkId_comap κ _ t ?_
    have : (κ.stalkMap t).hom (((pullback ξ ρ).presheaf.germ ⊤ (κ t) trivial).hom s0) ∈ _ :=
      Ideal.mem_map_of_mem _ (hh (κ t))
    rw [e] at this
    exact this
  have h4 := GlobalTheory.T.mem_ideal_map_of_germs_affineScheme (κ ≫ pullback.snd ξ ρ) I W hκ _ hs
  have h5 := Ideal.mem_map_of_mem (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).hom.hom h4
  rw [Ideal.map_map] at h5
  have e1 : (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom s0) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] h := by
    rw [← hR h, ← hs0]
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).hom.hom.comp
      ((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom = Algebra.TensorProduct.includeLeftRingHom := by
    ext c; exact hL c
  rwa [e1, e2] at h5

/- English proof (translation)
Introduce `X Y' ρ _ _ I R _ _ ξ hfl h hh`. Take `⟨U₀, hU, hx, -⟩` from `Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)`. Set `U : X.affineOpens` to `⟨U₀, hU⟩`. Establish `hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)` using `(Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge`. Rewrite using `[TraitOrder.idlAlong_eq_map (I.map ρ) ξ U hle]`.

Establish `hc : IsCompact ((ρ ⁻¹ᵁ (U : X.Opens) : Y'.Opens) : Set Y')` using `QuasiCompact.isCompact_preimage (f := ρ) _ U.1.isOpen U.2.isCompact`. Take `⟨Us, hUs, hfin, heq⟩` from `Y'.isBasis_affineOpens.exists_finite_of_isCompact hc`. Set `ι` to `↥Us`. Use `haveI : Finite ι := hfin.to_subtype`. Set `W : ι → Y'.affineOpens` to `fun i => ⟨i.1, hUs i.2⟩`.

Establish `hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)` using `fun i => heq ▸ le_sSup i.2`. Establish `hcov : ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens)`. Rewrite using `[heq, sSup_le_iff]`. Introduce `V hV`. Conclude with `le_iSup (fun i : ι => (W i : Y'.Opens)) ⟨V, hV⟩`.

Use `letI : Algebra Γ(X, U) R := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra`. Use `haveI : Module.Flat Γ(X, U) R := GlobalTheory.FlatPush.flat_sections_to_chart ξ U hle hx hfl`. Set `K : ι → Ideal Γ(X, U)` to `fun i => (I.ideal (W i)).comap (ρ.appLE U (W i) (hW i)).hom`. Establish `h1 : ⨅ i, K i ≤ (I.map ρ).ideal U` using `fun b hb => GlobalTheory.T.mem_idealSheaf_map_of_affineCover_preimage ρ I U W hW hcov b fun i => (Ideal.mem_iInf.1 hb i)`. Establish `h2 : h ∈ ⨅ i, (K i).map (algebraMap Γ(X, U) R)`.

Use `Ideal.mem_iInf.2 fun i => ?_` and prove the remaining obligations. Use `letI : Algebra Γ(X, U) Γ(Y', W i) := (ρ.appLE U (W i) (hW i)).hom.toAlgebra`. Conclude with `GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map (I.ideal (W i)) h (tmul_mem_of_germ ρ I ξ U hle (W i) (hW i) h hh)`. Conclude with `Ideal.map_mono h1 (GlobalTheory.T.iInf_map_le_map_iInf_of_flat K h2)`.
-/
theorem mem_idlAlong_map_of_flat : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] [QuasiSeparated ρ]
    (I : Y'.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X),
    (Scheme.stalkClosedPointTo ξ).hom.Flat → ∀ h : R, (∀ v : ↥(pullback ξ ρ : Scheme.{0}),
      ((pullback ξ ρ).presheaf.germ ⊤ v trivial).hom ((pullback.fst ξ ρ).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h)) ∈ FinalTheorems.stalkId (I.comap (pullback.snd ξ ρ)) v) →
      h ∈ idlAlong (I.map ρ) ξ := by
  intro X Y' ρ _ _ I R _ _ ξ hfl h hh
  obtain ⟨U₀, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  let U : X.affineOpens := ⟨U₀, hU⟩
  have hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens) := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
  rw [TraitOrder.idlAlong_eq_map (I.map ρ) ξ U hle]
  have hc : IsCompact ((ρ ⁻¹ᵁ (U : X.Opens) : Y'.Opens) : Set Y') :=
    QuasiCompact.isCompact_preimage (f := ρ) _ U.1.isOpen U.2.isCompact
  obtain ⟨Us, hUs, hfin, heq⟩ := Y'.isBasis_affineOpens.exists_finite_of_isCompact hc
  let ι := ↥Us
  haveI : Finite ι := hfin.to_subtype
  let W : ι → Y'.affineOpens := fun i => ⟨i.1, hUs i.2⟩
  have hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens) := fun i => heq ▸ le_sSup i.2
  have hcov : ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) := by
    rw [heq, sSup_le_iff]
    intro V hV
    exact le_iSup (fun i : ι => (W i : Y'.Opens)) ⟨V, hV⟩
  letI : Algebra Γ(X, U) R := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  haveI : Module.Flat Γ(X, U) R := GlobalTheory.FlatPush.flat_sections_to_chart ξ U hle hx hfl
  let K : ι → Ideal Γ(X, U) := fun i => (I.ideal (W i)).comap (ρ.appLE U (W i) (hW i)).hom
  have h1 : ⨅ i, K i ≤ (I.map ρ).ideal U := fun b hb =>
    GlobalTheory.T.mem_idealSheaf_map_of_affineCover_preimage ρ I U W hW hcov b fun i => (Ideal.mem_iInf.1 hb i)
  have h2 : h ∈ ⨅ i, (K i).map (algebraMap Γ(X, U) R) := by
    refine Ideal.mem_iInf.2 fun i => ?_
    letI : Algebra Γ(X, U) Γ(Y', W i) := (ρ.appLE U (W i) (hW i)).hom.toAlgebra
    exact GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map (I.ideal (W i)) h (tmul_mem_of_germ ρ I ξ U hle (W i) (hW i) h hh)
  exact Ideal.map_mono h1 (GlobalTheory.T.iInf_map_le_map_iInf_of_flat K h2)

end GlobalTheory.FlatPush
