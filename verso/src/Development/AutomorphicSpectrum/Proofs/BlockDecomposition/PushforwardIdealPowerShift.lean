import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenRestrictionFunctionsCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturalityStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

namespace GlobalTheory.CompanionTheory.GE.FormalShift

attribute [local instance] algebraOfOver

/- English proof (translation)
Use `letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩`. Establish `s1 : algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b = (φ ∣_ V).appTop (V.topIso.inv b)`. Express the relevant statement in the definitionally equal form `(φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _`. Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply]`. Use `erw [Iso.inv_hom_id_apply]`.

Rewrite using `[s1]`. Use `erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]`. Use `(RelSerre.app_eqToHom_apply φ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem algebraMap_overPre {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (b : Γ(X, V)) :
    letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
    Z.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      φ.app V b := by
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  have s1 : algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b = (φ ∣_ V).appTop (V.topIso.inv b) := by
    change (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (RelSerre.app_eqToHom_apply φ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp

/- English proof (translation)
Introduce `X Z φ V hV G`. Use `letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩`. Introduce `J x hx`. Set `L : Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)] Γ((Scheme.Modules.pushforward φ).obj G, V)` to `{ toFun := fun x => G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op (Sheaf.H.equiv₀ (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x : Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) map_add' := fun x y => by`. Rewrite using `[map_add]`.

Conclude with `map_add _ _ _`. Use the proof step `map_smul' := fun b x => by`. Rewrite using `[H.smul_def, ← Sheaf.H.equiv₀_naturality]`. Use `(RelSerre.smul_restrict_top G (φ ⁻¹ᵁ V) _ _).trans ?_` and prove the remaining obligations. Use `(congrArg (· • _) (algebraMap_overPre φ V hV b)).trans ?_` and prove the remaining obligations.

Conclude with `(smul_pushforward φ G b _).symm }`. Express the relevant statement in the definitionally equal form `L x ∈ _`. Use `Submodule.smul_induction_on hx (p := fun x => L x ∈ (J • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V))) (fun b hb y _ => ?_) (fun y y' hy hy' => ?_)` and prove the remaining obligations. Use `show L (b • y) ∈ _`. Rewrite using `[map_smul]`.

Conclude with `Submodule.smul_mem_smul hb Submodule.mem_top`. Use `show L (y + y') ∈ _`. Rewrite using `[map_add]`. Conclude with `add_mem hy hy'`.
-/
theorem zeroth_cohomology_ideal_transfer : ∀ {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (G : Z.Modules), letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (J : Ideal Γ(X, V)) (x : Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0), x ∈ (J • ⊤ : Submodule Γ(X, V) (Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op (Sheaf.H.equiv₀ (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x : Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))) ∈ (J • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  intro X Z φ V hV G
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  intro J x hx
  let L : Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward φ).obj G, V) :=
    { toFun := fun x => G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
        (Sheaf.H.equiv₀ (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x :
          Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
      map_add' := fun x y => by
        rw [map_add]
        exact map_add _ _ _
      map_smul' := fun b x => by
        rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
        refine (RelSerre.smul_restrict_top G (φ ⁻¹ᵁ V) _ _).trans ?_
        refine (congrArg (· • _) (algebraMap_overPre φ V hV b)).trans ?_
        exact (smul_pushforward φ G b _).symm }
  change L x ∈ _
  refine Submodule.smul_induction_on hx (p := fun x => L x ∈ (J • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V))) (fun b hb y _ => ?_) (fun y y' hy hy' => ?_)
  · show L (b • y) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  · show L (y + y') ∈ _
    rw [map_add]
    exact add_mem hy hy'

/- English proof (translation)
Use `⟨(Sheaf.H.equiv₀ (modulesAb (idealPow J F (k + 1))) isTerminalTop).symm (g.app ⊤ p), ?_⟩` and prove the remaining obligations. Use `(Sheaf.H.equiv₀_symm_naturality (hT := isTerminalTop) (modulesAbMap (idealPowι J F (k + 1))) (g.app ⊤ p)).trans ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← hg]`. Both sides reduce to the same expression.
-/
theorem mem_formalK_of_factor {B : Type} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {Y : Scheme.{0}} [Y.Over (Spec (.of B))] {P F : Y.Modules} (f : P ⟶ F) (k : ℕ)
    (g : P ⟶ idealPow J F (k + 1)) (hg : g ≫ idealPowι J F (k + 1) = f) (p : Γ(P, ⊤)) :
    (Sheaf.H.equiv₀ (modulesAb F) isTerminalTop).symm (f.app ⊤ p) ∈ formalK J F 0 k := by
  refine ⟨(Sheaf.H.equiv₀ (modulesAb (idealPow J F (k + 1))) isTerminalTop).symm (g.app ⊤ p), ?_⟩
  refine (Sheaf.H.equiv₀_symm_naturality (hT := isTerminalTop)
    (modulesAbMap (idealPowι J F (k + 1))) (g.app ⊤ p)).trans ?_
  congr 1
  rw [← hg]
  rfl

/- English proof (translation)
Introduce `A _ _ I X Z _ _ _ φ hprop hφ G hG V hV`. Use `haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Use `letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩`. Use `haveI : IsProper ((φ ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(X, V))) := by`. Express the relevant statement in the definitionally equal form `IsProper (φ ∣_ V ≫ hV.isoSpec.hom)`.

Use `infer_instance`. Use `haveI := hG.1`. Establish `hF : IsCoherent (G.restrict (φ ⁻¹ᵁ V).ι)` using `hG.restrict _`. Take `⟨c₀, hc₀⟩` from `exists_formalK_le (Ideal.map (toFunctions (A := A) V) I) hF 0`. Use `⟨c₀ + 1, fun n s hs => ?_⟩` and prove the remaining obligations.

Take `⟨t, rfl⟩` from `hs`. Take `⟨g, hg⟩` from `GlobalTheory.T.affine_restriction_functions_naturality I φ V hV (GlobalTheory.T.open_restriction_functions_compatible φ hφ V hV) G (n + c₀ + 1)`. Set `p : Γ((idealPow I G (n + c₀ + 1)).restrict (φ ⁻¹ᵁ V).ι, ⊤)` to `(idealPow I G (n + c₀ + 1)).presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t`. Establish `hx` using `mem_formalK_of_factor _ _ (n + c₀) g hg p`. Establish `hx2` using `hc₀ n hx`.

Establish `hx3` using `zeroth_cohomology_ideal_transfer φ V hV G _ _ hx2`. Rewrite `hx3` using `[← Ideal.map_pow]`. Use `hx3 using 1` and compare the differences between its conclusion and the goal. Simplify using `only`. Use `erw [AddEquiv.apply_symm_apply]`.

Establish `nat` using `NatTrans.naturality_apply (idealPowι I G (n + c₀ + 1)).mapPresheaf (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t`. Express the relevant statement in the definitionally equal form `_ = G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op ((idealPowι I G (n + c₀ + 1)).mapPresheaf.app (op ((φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) ((idealPow I G (n + c₀ + 1)).presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t))`. Rewrite using `[nat]`. Rewrite using `[← ConcreteCategory.comp_apply, ← Functor.map_comp]`. Simplify using `only [eqToHom_op, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]`.

Both sides reduce to the same expression.
-/
theorem formal_shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {G : Z.Modules}, IsCoherent G → ∀ (V : X.Opens), IsAffineOpen V → ∃ c : ℕ, ∀ (n : ℕ) (s : Γ(G, φ ⁻¹ᵁ V)), s ∈ Set.range ((idealPowι I G (n + c)).app (φ ⁻¹ᵁ V)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from s) ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  intro A _ _ I X Z _ _ _ φ hprop hφ G hG V hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  haveI : IsProper ((φ ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(X, V))) := by
    change IsProper (φ ∣_ V ≫ hV.isoSpec.hom)
    infer_instance
  haveI := hG.1
  have hF : IsCoherent (G.restrict (φ ⁻¹ᵁ V).ι) := hG.restrict _
  obtain ⟨c₀, hc₀⟩ := exists_formalK_le (Ideal.map (toFunctions (A := A) V) I) hF 0
  refine ⟨c₀ + 1, fun n s hs => ?_⟩
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨g, hg⟩ := GlobalTheory.T.affine_restriction_functions_naturality I φ V hV (GlobalTheory.T.open_restriction_functions_compatible φ hφ V hV) G (n + c₀ + 1)
  let p : Γ((idealPow I G (n + c₀ + 1)).restrict (φ ⁻¹ᵁ V).ι, ⊤) :=
    (idealPow I G (n + c₀ + 1)).presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t
  have hx := mem_formalK_of_factor _ _ (n + c₀) g hg p
  have hx2 := hc₀ n hx
  have hx3 := zeroth_cohomology_ideal_transfer φ V hV G _ _ hx2
  rw [← Ideal.map_pow] at hx3
  convert hx3 using 1
  dsimp only
  erw [AddEquiv.apply_symm_apply]
  have nat := NatTrans.naturality_apply (idealPowι I G (n + c₀ + 1)).mapPresheaf
    (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t
  change _ = G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
    ((idealPowι I G (n + c₀ + 1)).mapPresheaf.app (op ((φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
      ((idealPow I G (n + c₀ + 1)).presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t))
  rw [nat]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [eqToHom_op, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory.CompanionTheory.GE.FormalShift
