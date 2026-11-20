import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobFilt.ExtPres

/- English proof (translation)
Use `P.iso` as an intermediate fact. Set `j` to `B.gen.ι`. Establish `hR : IsIso ((Scheme.Modules.restrictFunctor j).map P.ψ)`. Set `e` to `Scheme.Modules.restrictFunctorIsoPullback j`. Establish `h : (Scheme.Modules.restrictFunctor j).map P.ψ = e.hom.app _ ≫ B.genRes.map P.ψ ≫ e.inv.app _`.

Rewrite using `[← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]`. Rewrite using `[h]`. Use `infer_instance`. Establish `hinj : ∀ U : B.gen.toScheme.Opens, Function.Injective (P.ψ.app (j ''ᵁ U))` using `fun U => app_injective_of_mono ((Scheme.Modules.restrictFunctor j).map P.ψ) U`. Use `mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩` and prove the remaining obligations.

Establish `hηW : genericPoint B.X ∈ W` using `(genericPoint_specializes x).mem_open W.isOpen hx`. Establish `hV : j ''ᵁ (j ⁻¹ᵁ W) = B.gen ⊓ W`. Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]`. Establish `hVW : j ''ᵁ (j ⁻¹ᵁ W) ≤ W` using `hV.le.trans inf_le_right`. Establish `hηV : genericPoint B.X ∈ j ''ᵁ (j ⁻¹ᵁ W)`.

Rewrite using `[hV]`. Conclude with `⟨B.genericPoint_mem_gen, hηW⟩`. Use `sub_eq_zero.1 (P.vb'.isTorsionFree W hηW _ ?_)` and prove the remaining obligations. Establish `h0 : Twist.resM _ hVW (a - b) = 0`. Apply `hinj (j ⁻¹ᵁ W)` to reduce the goal to its premises.

Rewrite using `[Twist.app_resM, map_sub, e, sub_self, map_zero, map_zero]`. Rewrite using `[← Twist.germ_resM hVW hηV, h0, map_zero]`.
-/
theorem mono_ψ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} (P : Pres B) :
    Mono P.ψ := by
  have := P.iso
  let j := B.gen.ι
  have hR : IsIso ((Scheme.Modules.restrictFunctor j).map P.ψ) := by
    let e := Scheme.Modules.restrictFunctorIsoPullback j
    have h : (Scheme.Modules.restrictFunctor j).map P.ψ = e.hom.app _ ≫ B.genRes.map P.ψ ≫ e.inv.app _ := by
      rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [h]; infer_instance
  have hinj : ∀ U : B.gen.toScheme.Opens, Function.Injective (P.ψ.app (j ''ᵁ U)) := fun U =>
    app_injective_of_mono ((Scheme.Modules.restrictFunctor j).map P.ψ) U
  refine mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hηW : genericPoint B.X ∈ W := (genericPoint_specializes x).mem_open W.isOpen hx
  have hV : j ''ᵁ (j ⁻¹ᵁ W) = B.gen ⊓ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hVW : j ''ᵁ (j ⁻¹ᵁ W) ≤ W := hV.le.trans inf_le_right
  have hηV : genericPoint B.X ∈ j ''ᵁ (j ⁻¹ᵁ W) := by
    rw [hV]; exact ⟨B.genericPoint_mem_gen, hηW⟩
  refine sub_eq_zero.1 (P.vb'.isTorsionFree W hηW _ ?_)
  have h0 : Twist.resM _ hVW (a - b) = 0 := by
    apply hinj (j ⁻¹ᵁ W)
    rw [Twist.app_resM, map_sub, e, sub_self, map_zero, map_zero]
  rw [← Twist.germ_resM hVW hηV, h0, map_zero]

/- English proof (translation)
Set `a : E₃' ⟶ pullback f (cokernel.π ψ)` to `pullback.lift 0 ψ (by simp)`. Set `b : kernel f ⟶ pullback f (cokernel.π ψ)` to `pullback.lift (kernel.ι f) 0 (by simp)`. Establish `ha₁ : a ≫ pullback.fst f (cokernel.π ψ) = 0` using `pullback.lift_fst _ _ _`. Establish `ha₂ : a ≫ pullback.snd f (cokernel.π ψ) = ψ` using `pullback.lift_snd _ _ _`. Establish `hb₁ : b ≫ pullback.fst f (cokernel.π ψ) = kernel.ι f` using `pullback.lift_fst _ _ _`.

Establish `hb₂ : b ≫ pullback.snd f (cokernel.π ψ) = 0` using `pullback.lift_snd _ _ _`. Establish `hC : (ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)).Exact` using `ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ψ)`. Set `S₁ : ShortComplex X.Modules` to `ShortComplex.mk a (pullback.fst f (cokernel.π ψ)) ha₁`. Establish `hS₁ : S₁.ShortExact`. Use `ShortComplex.ShortExact.mk' ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[ShortComplex.exact_iff_exact_up_to_refinements]`. Introduce `A x₂ hx₂`. Establish `hx₂' : x₂ ≫ pullback.fst f (cokernel.π ψ) = 0` using `hx₂`. Establish `h0 : (x₂ ≫ pullback.snd f (cokernel.π ψ)) ≫ cokernel.π ψ = 0`. Rewrite using `[Category.assoc, ← pullback.condition, ← Category.assoc, hx₂', zero_comp]`.

Take `⟨A', π', hπ', x₁, hx₁⟩` from `hC.exact_up_to_refinements _ h0`. Use `⟨A', π', hπ', x₁, ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _`. Rewrite using `[Category.assoc, Category.assoc, hx₂', ha₁, comp_zero, comp_zero]`.

Express the relevant statement in the definitionally equal form `(π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _`. Rewrite using `[Category.assoc, Category.assoc, ha₂]`. Conclude with `hx₁`. Establish `: Mono (a ≫ pullback.snd f (cokernel.π ψ))` using `by rw [ha₂]; infer_instance`. Conclude with `mono_of_mono a (pullback.snd f (cokernel.π ψ))`.

Conclude with `Abelian.epi_pullback_of_epi_g f (cokernel.π ψ)`. Set `S₂ : ShortComplex X.Modules` to `ShortComplex.mk b (pullback.snd f (cokernel.π ψ)) hb₂`. Establish `hS₂ : S₂.ShortExact`. Use `ShortComplex.ShortExact.mk' ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[ShortComplex.exact_iff_exact_up_to_refinements]`.

Introduce `A x₂ hx₂`. Establish `hx₂' : x₂ ≫ pullback.snd f (cokernel.π ψ) = 0` using `hx₂`. Establish `h0 : (x₂ ≫ pullback.fst f (cokernel.π ψ)) ≫ f = 0`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hx₂', zero_comp]`. Use `⟨A, 𝟙 A, inferInstance, kernel.lift f _ h0, ?_⟩` and prove the remaining obligations.

Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(𝟙 A ≫ x₂) ≫ _ = (kernel.lift f _ h0 ≫ b) ≫ _`. Rewrite using `[Category.assoc, Category.assoc, hb₁, kernel.lift_ι, Category.id_comp]`. Express the relevant statement in the definitionally equal form `(𝟙 A ≫ x₂) ≫ _ = (kernel.lift f _ h0 ≫ b) ≫ _`. Rewrite using `[Category.assoc, Category.assoc, hb₂, comp_zero, Category.id_comp, hx₂']`.

Establish `: Mono (b ≫ pullback.fst f (cokernel.π ψ))` using `by rw [hb₁]; infer_instance`. Conclude with `mono_of_mono b (pullback.fst f (cokernel.π ψ))`. Conclude with `Abelian.epi_pullback_of_epi_f f (cokernel.π ψ)`. Establish `hF : GlobalTheory.VB.IsVB (pullback f (cokernel.π ψ)) (r + s)`. Use `GlobalTheory.VBExt.isVB_X₂_of_shortExact X S₁ s r hS₁ h₃' hE` as an intermediate fact.

Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis. Conclude with `GlobalTheory.VB.isVB_X₁_of_shortExact X S₂ r s hS₂ hF h₃`.
-/
theorem isVB_kernel {X : Scheme.{0}} {E E₃' E₃ : X.Modules} (ψ : E₃' ⟶ E₃) [Mono ψ] (f : E ⟶ cokernel ψ) [Epi f]
    {r s : ℕ} (hE : GlobalTheory.VB.IsVB E r) (h₃ : GlobalTheory.VB.IsVB E₃ s) (h₃' : GlobalTheory.VB.IsVB E₃' s) :
    GlobalTheory.VB.IsVB (kernel f) r := by
  let a : E₃' ⟶ pullback f (cokernel.π ψ) := pullback.lift 0 ψ (by simp)
  let b : kernel f ⟶ pullback f (cokernel.π ψ) := pullback.lift (kernel.ι f) 0 (by simp)
  have ha₁ : a ≫ pullback.fst f (cokernel.π ψ) = 0 := pullback.lift_fst _ _ _
  have ha₂ : a ≫ pullback.snd f (cokernel.π ψ) = ψ := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.fst f (cokernel.π ψ) = kernel.ι f := pullback.lift_fst _ _ _
  have hb₂ : b ≫ pullback.snd f (cokernel.π ψ) = 0 := pullback.lift_snd _ _ _
  have hC : (ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ψ)
  let S₁ : ShortComplex X.Modules := ShortComplex.mk a (pullback.fst f (cokernel.π ψ)) ha₁
  have hS₁ : S₁.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro A x₂ hx₂
      have hx₂' : x₂ ≫ pullback.fst f (cokernel.π ψ) = 0 := hx₂
      have h0 : (x₂ ≫ pullback.snd f (cokernel.π ψ)) ≫ cokernel.π ψ = 0 := by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, hx₂', zero_comp]
      obtain ⟨A', π', hπ', x₁, hx₁⟩ := hC.exact_up_to_refinements _ h0
      refine ⟨A', π', hπ', x₁, ?_⟩
      apply pullback.hom_ext
      · change (π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _
        rw [Category.assoc, Category.assoc, hx₂', ha₁, comp_zero, comp_zero]
      · change (π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _
        rw [Category.assoc, Category.assoc, ha₂]
        exact hx₁
    · have : Mono (a ≫ pullback.snd f (cokernel.π ψ)) := by rw [ha₂]; infer_instance
      exact mono_of_mono a (pullback.snd f (cokernel.π ψ))
    · exact Abelian.epi_pullback_of_epi_g f (cokernel.π ψ)
  let S₂ : ShortComplex X.Modules := ShortComplex.mk b (pullback.snd f (cokernel.π ψ)) hb₂
  have hS₂ : S₂.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro A x₂ hx₂
      have hx₂' : x₂ ≫ pullback.snd f (cokernel.π ψ) = 0 := hx₂
      have h0 : (x₂ ≫ pullback.fst f (cokernel.π ψ)) ≫ f = 0 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hx₂', zero_comp]
      refine ⟨A, 𝟙 A, inferInstance, kernel.lift f _ h0, ?_⟩
      apply pullback.hom_ext
      · change (𝟙 A ≫ x₂) ≫ _ = (kernel.lift f _ h0 ≫ b) ≫ _
        rw [Category.assoc, Category.assoc, hb₁, kernel.lift_ι, Category.id_comp]
      · change (𝟙 A ≫ x₂) ≫ _ = (kernel.lift f _ h0 ≫ b) ≫ _
        rw [Category.assoc, Category.assoc, hb₂, comp_zero, Category.id_comp, hx₂']
    · have : Mono (b ≫ pullback.fst f (cokernel.π ψ)) := by rw [hb₁]; infer_instance
      exact mono_of_mono b (pullback.fst f (cokernel.π ψ))
    · exact Abelian.epi_pullback_of_epi_f f (cokernel.π ψ)
  have hF : GlobalTheory.VB.IsVB (pullback f (cokernel.π ψ)) (r + s) := by
    have := GlobalTheory.VBExt.isVB_X₂_of_shortExact X S₁ s r hS₁ h₃' hE
    rwa [add_comm] at this
  exact GlobalTheory.VB.isVB_X₁_of_shortExact X S₂ r s hS₂ hF h₃

/- English proof (translation)
Take `⟨n, k, φ, hφ⟩` from `(hL.eventually_exists_epi_sigma F).exists`. Establish `hL'` using `Twist.isLB_lbZPow hL.isLB (-n)`. Use `Twist.preservesColimits_twistFunctor hL'` as an intermediate fact. Set `e : (∐ fun _ : Fin k => LB.toMod (lbZPow L (-n))) ≅ GlobalTheory.twist (freeModule X (Fin k)) (lbZPow L (-n))` to `Sigma.mapIso (fun _ => (Twist.unitTwistIso (lbZPow L (-n))).symm) ≪≫ (PreservesCoproduct.iso (twistFunctor (lbZPow L (-n))) fun _ : Fin k => structureModule X).symm`. Conclude with `⟨k, _, φ, ((GlobalTheory.VB.isVB_freeModule_fin X k).twist hL').of_iso e.symm, hφ⟩`.
-/
theorem exists_epi_of_isAmpleLB {X : Scheme.{0}} {L : LB X} (hL : IsAmpleLB L) (F : X.Modules)
    [IsFiniteQC F] : ∃ (k : ℕ) (V : X.Modules) (φ : V ⟶ F), GlobalTheory.VB.IsVB V k ∧ Epi φ := by
  obtain ⟨n, k, φ, hφ⟩ := (hL.eventually_exists_epi_sigma F).exists
  have hL' := Twist.isLB_lbZPow hL.isLB (-n)
  have := Twist.preservesColimits_twistFunctor hL'
  let e : (∐ fun _ : Fin k => LB.toMod (lbZPow L (-n))) ≅
      GlobalTheory.twist (freeModule X (Fin k)) (lbZPow L (-n)) :=
    Sigma.mapIso (fun _ => (Twist.unitTwistIso (lbZPow L (-n))).symm) ≪≫
      (PreservesCoproduct.iso (twistFunctor (lbZPow L (-n))) fun _ : Fin k => structureModule X).symm
  exact ⟨k, _, φ, ((GlobalTheory.VB.isVB_freeModule_fin X k).twist hL').of_iso e.symm, hφ⟩

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}

/- English proof (translation)
Use `P.vb.isFiniteQC` as an intermediate fact. Use `P.vb'.isFiniteQC` as an intermediate fact. Establish `: IsFiniteQC P.mod` using `inferInstanceAs (IsFiniteQC (cokernel P.ψ))`. Conclude with `IsFiniteQC.of_iso e.symm`.
-/
theorem isFiniteQC_of_iso (P : Pres B) {M : B.X.Modules} (e : M ≅ P.mod) : IsFiniteQC M := by
  have := P.vb.isFiniteQC
  have := P.vb'.isFiniteQC
  have : IsFiniteQC P.mod := inferInstanceAs (IsFiniteQC (cokernel P.ψ))
  exact IsFiniteQC.of_iso e.symm

/- English proof (translation)
Use `P.iso` as an intermediate fact. Establish `h : IsZero (cokernel (B.genRes.map P.ψ))` using `isZero_cokernel_of_epi _`. Conclude with `(h.of_iso (PreservesCokernel.iso B.genRes P.ψ)).of_iso (B.genRes.mapIso e)`.
-/
theorem isZero_genRes (P : Pres B) {M : B.X.Modules} (e : M ≅ P.mod) : IsZero (B.genRes.obj M) := by
  have := P.iso
  have h : IsZero (cokernel (B.genRes.map P.ψ)) := isZero_cokernel_of_epi _
  exact (h.of_iso (PreservesCokernel.iso B.genRes P.ψ)).of_iso (B.genRes.mapIso e)

/- English proof (translation)
Use `mono_ψ P` as an intermediate fact. Set `g' : E ⟶ cokernel P.ψ` to `g ≫ e.hom`. Use `haveI : Epi g' := @epi_comp _ _ _ _ _ g _ e.hom _`. Establish `hK : GlobalTheory.VB.IsVB (kernel g) r` using `(isVB_kernel P.ψ g' hE P.vb P.vb').of_iso (kernelCompMono g e.hom)`. Use `⟨hK, ?_⟩` and prove the remaining obligations.

Use `hK.isQuasicoherent` as an intermediate fact. Use `hE.isQuasicoherent` as an intermediate fact. Establish `hm : Mono (B.genRes.map (kernel.ι g))` using `mono_pullback_map _ _`. Establish `e' : cokernel (kernel.ι g) ≅ M` using `IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel g))`. Establish `hz : IsZero (cokernel (B.genRes.map (kernel.ι g)))` using `((isZero_genRes P e).of_iso (B.genRes.mapIso e')).of_iso (PreservesCokernel.iso B.genRes (kernel.ι g)).symm`.

Establish `he : Epi (B.genRes.map (kernel.ι g))` using `Preadditive.epi_of_isZero_cokernel _ hz`. Conclude with `isIso_of_mono_of_epi _`.
-/
theorem kernel_step (P : Pres B) {M E : B.X.Modules} (e : M ≅ P.mod) (g : E ⟶ M) [Epi g] {r : ℕ}
    (hE : GlobalTheory.VB.IsVB E r) :
    GlobalTheory.VB.IsVB (kernel g) r ∧ IsIso (B.genRes.map (kernel.ι g)) := by
  have := mono_ψ P
  let g' : E ⟶ cokernel P.ψ := g ≫ e.hom
  haveI : Epi g' := @epi_comp _ _ _ _ _ g _ e.hom _
  have hK : GlobalTheory.VB.IsVB (kernel g) r :=
    (isVB_kernel P.ψ g' hE P.vb P.vb').of_iso (kernelCompMono g e.hom)
  refine ⟨hK, ?_⟩
  have := hK.isQuasicoherent
  have := hE.isQuasicoherent
  have hm : Mono (B.genRes.map (kernel.ι g)) := mono_pullback_map _ _
  have e' : cokernel (kernel.ι g) ≅ M := IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel g))
  have hz : IsZero (cokernel (B.genRes.map (kernel.ι g))) :=
    ((isZero_genRes P e).of_iso (B.genRes.mapIso e')).of_iso
      (PreservesCokernel.iso B.genRes (kernel.ι g)).symm
  have he : Epi (B.genRes.map (kernel.ι g)) := Preadditive.epi_of_isZero_cokernel _ hz
  exact isIso_of_mono_of_epi _

/- English proof (translation)
Use `hS.mono_f` as an intermediate fact. Use `hS.epi_g` as an intermediate fact. Set `q : P₃.E ⟶ S.X₃` to `cokernel.π P₃.ψ ≫ e₃.inv`. Use `haveI : Epi q := @epi_comp _ _ _ _ _ (cokernel.π P₃.ψ) inferInstance e₃.inv (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv e₃))`. Set `a : S.X₁ ⟶ pullback S.g q` to `pullback.lift S.f 0 (by simp)`.

Establish `ha₁ : a ≫ pullback.fst S.g q = S.f` using `pullback.lift_fst _ _ _`. Establish `ha₂ : a ≫ pullback.snd S.g q = 0` using `pullback.lift_snd _ _ _`. Set `T : ShortComplex B.X.Modules` to `ShortComplex.mk a (pullback.snd S.g q) ha₂`. Establish `hT : T.ShortExact`. Use `ShortComplex.ShortExact.mk' ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[ShortComplex.exact_iff_exact_up_to_refinements]`. Introduce `A x₂ hx₂`. Establish `hx₂' : x₂ ≫ pullback.snd S.g q = 0` using `hx₂`. Establish `h0 : (x₂ ≫ pullback.fst S.g q) ≫ S.g = 0`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hx₂', zero_comp]`.

Take `⟨A', π', hπ', x₁, hx₁⟩` from `hS.exact.exact_up_to_refinements _ h0`. Use `⟨A', π', hπ', x₁, ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _`. Rewrite using `[Category.assoc, Category.assoc, ha₁]`.

Conclude with `hx₁`. Express the relevant statement in the definitionally equal form `(π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _`. Rewrite using `[Category.assoc, Category.assoc, hx₂', ha₂, comp_zero, comp_zero]`. Establish `: Mono (a ≫ pullback.fst S.g q)` using `by rw [ha₁]; infer_instance`. Conclude with `mono_of_mono a (pullback.fst S.g q)`.

Conclude with `Abelian.epi_pullback_of_epi_f S.g q`. Use `haveI : IsFiniteQC T.X₁ := isFiniteQC_of_iso P₁ e₁`. Use `haveI : IsFiniteQC T.X₃ := P₃.vb.isFiniteQC`. Use `haveI : T.X₂.IsQuasicoherent := FlagPull.isQuasicoherent_X₂ T hT P₃.vb`. Establish `hQ : IsFiniteQC T.X₂` using `IsFiniteQC.of_shortExact hT`.

Use `haveI : IsFiniteQC (pullback S.g q) := hQ`. Take `⟨L, hL⟩` from `B.exists_isAmpleLB`. Take `⟨k, V, φ, hV, hφ⟩` from `exists_epi_of_isAmpleLB hL (pullback S.g q)`. Use `haveI : Epi (pullback.fst S.g q) := Abelian.epi_pullback_of_epi_g S.g q`. Conclude with `⟨k, V, φ ≫ pullback.fst S.g q, hV, inferInstance⟩`.
-/
theorem exists_epi (S : ShortComplex B.X.Modules) (hS : S.ShortExact) (P₁ P₃ : Pres B)
    (e₁ : S.X₁ ≅ P₁.mod) (e₃ : S.X₃ ≅ P₃.mod) :
    ∃ (k : ℕ) (V : B.X.Modules) (φ : V ⟶ S.X₂), GlobalTheory.VB.IsVB V k ∧ Epi φ := by
  have := hS.mono_f
  have := hS.epi_g
  let q : P₃.E ⟶ S.X₃ := cokernel.π P₃.ψ ≫ e₃.inv
  haveI : Epi q := @epi_comp _ _ _ _ _ (cokernel.π P₃.ψ) inferInstance e₃.inv
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv e₃))
  let a : S.X₁ ⟶ pullback S.g q := pullback.lift S.f 0 (by simp)
  have ha₁ : a ≫ pullback.fst S.g q = S.f := pullback.lift_fst _ _ _
  have ha₂ : a ≫ pullback.snd S.g q = 0 := pullback.lift_snd _ _ _
  let T : ShortComplex B.X.Modules := ShortComplex.mk a (pullback.snd S.g q) ha₂
  have hT : T.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro A x₂ hx₂
      have hx₂' : x₂ ≫ pullback.snd S.g q = 0 := hx₂
      have h0 : (x₂ ≫ pullback.fst S.g q) ≫ S.g = 0 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hx₂', zero_comp]
      obtain ⟨A', π', hπ', x₁, hx₁⟩ := hS.exact.exact_up_to_refinements _ h0
      refine ⟨A', π', hπ', x₁, ?_⟩
      apply pullback.hom_ext
      · change (π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _
        rw [Category.assoc, Category.assoc, ha₁]
        exact hx₁
      · change (π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _
        rw [Category.assoc, Category.assoc, hx₂', ha₂, comp_zero, comp_zero]
    · have : Mono (a ≫ pullback.fst S.g q) := by rw [ha₁]; infer_instance
      exact mono_of_mono a (pullback.fst S.g q)
    · exact Abelian.epi_pullback_of_epi_f S.g q
  haveI : IsFiniteQC T.X₁ := isFiniteQC_of_iso P₁ e₁
  haveI : IsFiniteQC T.X₃ := P₃.vb.isFiniteQC
  haveI : T.X₂.IsQuasicoherent := FlagPull.isQuasicoherent_X₂ T hT P₃.vb
  have hQ : IsFiniteQC T.X₂ := IsFiniteQC.of_shortExact hT
  haveI : IsFiniteQC (pullback S.g q) := hQ
  obtain ⟨L, hL⟩ := B.exists_isAmpleLB
  obtain ⟨k, V, φ, hV, hφ⟩ := exists_epi_of_isAmpleLB hL (pullback S.g q)
  haveI : Epi (pullback.fst S.g q) := Abelian.epi_pullback_of_epi_g S.g q
  exact ⟨k, V, φ ≫ pullback.fst S.g q, hV, inferInstance⟩

end Model

/- English proof (translation)
Introduce `O _ _ _ p _ _ _ B S hS ⟨P₁, ⟨e₁⟩⟩ ⟨P₃, ⟨e₃⟩⟩`. Use `hS.mono_f` as an intermediate fact. Use `hS.epi_g` as an intermediate fact. Take `⟨k, V, f, hV, hf⟩` from `exists_epi S hS P₁ P₃ e₁ e₃`. Take `⟨hK₃, hi₃⟩` from `kernel_step P₃ e₃ (f ≫ S.g) hV`.

Set `h : kernel (f ≫ S.g) ⟶ S.X₁` to `hS.exact.lift (kernel.ι (f ≫ S.g) ≫ f) (by`. Rewrite using `[Category.assoc]`. Conclude with `kernel.condition _)`. Establish `hh : h ≫ S.f = kernel.ι (f ≫ S.g) ≫ f` using `hS.exact.lift_f _ _`. Use `haveI : Epi h := by`.

Rewrite using `[epi_iff_surjective_up_to_refinements]`. Introduce `A y`. Take `⟨A', π', hπ', x, hx⟩` from `surjective_up_to_refinements_of_epi f (y ≫ S.f)`. Use `⟨A', π', hπ', kernel.lift (f ≫ S.g) x (by simp [← reassoc_of% hx]), ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono S.f, Category.assoc, Category.assoc, hh, kernel.lift_ι_assoc, hx]`.

Take `⟨hK, hi⟩` from `kernel_step P₁ e₁ h hK₃`. Set `ψ : kernel h ⟶ V` to `kernel.ι h ≫ kernel.ι (f ≫ S.g)`. Establish `hψ : IsIso (B.genRes.map ψ)`. Rewrite using `[Functor.map_comp]`. Use `infer_instance`.

Establish `h0 : ψ ≫ f = 0`. Rewrite using `[Category.assoc, ← hh, kernel.condition_assoc, zero_comp]`. Set `T : ShortComplex B.X.Modules` to `ShortComplex.mk ψ f h0`. Establish `hT : T.Exact`. Rewrite using `[ShortComplex.exact_iff_exact_up_to_refinements]`.

Introduce `A x hx`. Establish `hx' : x ≫ f = 0` using `hx`. Set `y : A ⟶ kernel (f ≫ S.g)` to `kernel.lift _ x (by rw [← Category.assoc, hx', zero_comp])`. Establish `hy : y ≫ h = 0`. Rewrite using `[← cancel_mono S.f, Category.assoc, hh, kernel.lift_ι_assoc, hx', zero_comp]`.

Use `⟨A, 𝟙 A, inferInstance, kernel.lift h y hy, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `𝟙 A ≫ x = kernel.lift h y hy ≫ kernel.ι h ≫ kernel.ι (f ≫ S.g)`. Rewrite using `[kernel.lift_ι_assoc, kernel.lift_ι, Category.id_comp]`. Use `haveI : Epi T.g := hf`. Conclude with `⟨⟨k, V, kernel h, hV, hK, ψ, hψ⟩, ⟨IsColimit.coconePointUniqueUpToIso hT.gIsCokernel (colimit.isColimit _)⟩⟩`.
-/
theorem exists_pres_of_shortExact : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ)
    [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O),
    ∀ S : ShortComplex B.X.Modules, S.ShortExact → (∃ P : Pres B, Nonempty (S.X₁ ≅ P.mod)) →
      (∃ P : Pres B, Nonempty (S.X₃ ≅ P.mod)) → ∃ P : Pres B, Nonempty (S.X₂ ≅ P.mod) := by
  intro O _ _ _ p _ _ _ B S hS ⟨P₁, ⟨e₁⟩⟩ ⟨P₃, ⟨e₃⟩⟩
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨k, V, f, hV, hf⟩ := exists_epi S hS P₁ P₃ e₁ e₃
  obtain ⟨hK₃, hi₃⟩ := kernel_step P₃ e₃ (f ≫ S.g) hV
  let h : kernel (f ≫ S.g) ⟶ S.X₁ := hS.exact.lift (kernel.ι (f ≫ S.g) ≫ f) (by
    rw [Category.assoc]; exact kernel.condition _)
  have hh : h ≫ S.f = kernel.ι (f ≫ S.g) ≫ f := hS.exact.lift_f _ _
  haveI : Epi h := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A y
    obtain ⟨A', π', hπ', x, hx⟩ := surjective_up_to_refinements_of_epi f (y ≫ S.f)
    refine ⟨A', π', hπ', kernel.lift (f ≫ S.g) x (by simp [← reassoc_of% hx]), ?_⟩
    rw [← cancel_mono S.f, Category.assoc, Category.assoc, hh, kernel.lift_ι_assoc, hx]
  obtain ⟨hK, hi⟩ := kernel_step P₁ e₁ h hK₃
  let ψ : kernel h ⟶ V := kernel.ι h ≫ kernel.ι (f ≫ S.g)
  have hψ : IsIso (B.genRes.map ψ) := by
    rw [Functor.map_comp]; infer_instance
  have h0 : ψ ≫ f = 0 := by
    rw [Category.assoc, ← hh, kernel.condition_assoc, zero_comp]
  let T : ShortComplex B.X.Modules := ShortComplex.mk ψ f h0
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x hx
    have hx' : x ≫ f = 0 := hx
    let y : A ⟶ kernel (f ≫ S.g) := kernel.lift _ x (by rw [← Category.assoc, hx', zero_comp])
    have hy : y ≫ h = 0 := by
      rw [← cancel_mono S.f, Category.assoc, hh, kernel.lift_ι_assoc, hx', zero_comp]
    refine ⟨A, 𝟙 A, inferInstance, kernel.lift h y hy, ?_⟩
    change 𝟙 A ≫ x = kernel.lift h y hy ≫ kernel.ι h ≫ kernel.ι (f ≫ S.g)
    rw [kernel.lift_ι_assoc, kernel.lift_ι, Category.id_comp]
  haveI : Epi T.g := hf
  exact ⟨⟨k, V, kernel h, hV, hK, ψ, hψ⟩,
    ⟨IsColimit.coconePointUniqueUpToIso hT.gIsCokernel (colimit.isColimit _)⟩⟩

end GlobalTheory.FrobFilt.ExtPres
