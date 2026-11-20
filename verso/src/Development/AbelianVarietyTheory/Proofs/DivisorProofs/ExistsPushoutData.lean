import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueToLocallyDirectedColimitOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectivePreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyDirectedOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecMapOfThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackConeFstSndRingNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSurjectiveNilpotentKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutGoodBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAwayFibStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqOfFactorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.FerrandPush

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Use `IsClosedImmersion.spec_of_surjective _ h` as an intermediate fact. Rewrite using `[← hO.isoSpec_hom]`. Use `infer_instance`.
-/
theorem isClosedImmersion_toSpecΓ_comp {X : Scheme.{0}} (O : X.Opens) (hO : IsAffineOpen O)
    {A : CommRingCat.{0}} (q : A ⟶ Γ(X, O)) (h : Function.Surjective q.hom) :
    IsClosedImmersion (O.toSpecΓ ≫ Spec.map q) := by
  have := IsClosedImmersion.spec_of_surjective _ h
  rw [← hO.isoSpec_hom]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Establish `: Surjective (Spec.map q)`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `Function.Surjective (PrimeSpectrum.comap q.hom)`. Rewrite using `[← Set.range_eq_univ, range_comap_of_surjective _ _ h, PrimeSpectrum.zeroLocus_eq_univ_iff]`. Introduce `x hx`.

Take `⟨n, hn⟩` from `h'`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `Ideal.pow_mem_pow hx n` as an intermediate fact. Rewrite `this` using `[hn]`. Then use the resulting hypothesis. Rewrite using `[← hO.isoSpec_hom]`.

Use `infer_instance`.
-/
theorem surjective_toSpecΓ_comp {X : Scheme.{0}} (O : X.Opens) (hO : IsAffineOpen O)
    {A : CommRingCat.{0}} (q : A ⟶ Γ(X, O)) (h : Function.Surjective q.hom)
    (h' : IsNilpotent (RingHom.ker q.hom)) : Surjective (O.toSpecΓ ≫ Spec.map q) := by
  have : Surjective (Spec.map q) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap q.hom)
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ h,
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn] at this
  rw [← hO.isoSpec_hom]
  infer_instance

/- English proof (translation)
The claim follows from `SetLike.ext_iff.mp (preimage_upOpen i U) x`.
-/
theorem mem_upOpen_iff {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (x : Y₀) : i x ∈ upOpen i U ↔ x ∈ U :=
  SetLike.ext_iff.mp (preimage_upOpen i U) x

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `Y₀ Y₁ Y₂ i₁ i₂ hc₁ hc₂ hs₁ hs₂ hn₁ hn₂`. Use `haveI := hc₁`. Use `haveI := hc₂`. Use `haveI := hs₁`. Use `haveI := hs₂`.

Establish `hR : ∀ U ∈ good i₁ i₂, _` using `fun U (hU : U ∈ good i₁ i₂) ↦ GlobalTheory.T.pullbackCone_surjective_nilpotent_ker (res i₁ U) (res i₂ U) (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₁ hn₁ U hU.2.1).1 (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₁ hn₁ U hU.2.1).2 (GlobalTheo …`. Establish `hπ : ∀ U ∈ good i₁ i₂, Function.Surjective ((fibπ i₁ i₂).app (op U)).hom ∧ IsNilpotent (RingHom.ker ((fibπ i₁ i₂).app (op U)).hom)` using `fun U hU ↦ (hR U hU).2.2`. Establish `hbas₀ : ∀ U ∈ good i₁ i₂, ∀ (W : Y₀.Opens) (x : Y₀), x ∈ U → x ∈ W → ∃ V ∈ good i₁ i₂, x ∈ V ∧ V ≤ U ∧ V ≤ W`. Introduce `U hU W x hxU hxW`. Take `⟨f, hf, hxf⟩` from `hU.1.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU`.

Take `⟨a, rfl⟩` from `(hπ U hU).1 f`. Conclude with `⟨_, GlobalTheory.T.ferrand_pushout_good_basic_open i₁ i₂ U hU a, hxf, Y₀.basicOpen_le _, hf⟩`. Establish `hopen` using `GlobalTheory.T.isOpenImmersion_of_nilpotent_thickening_cover Y₀ (good i₁ i₂) (fun U hU ↦ hU.1) (fib i₁ i₂) (fibπ i₁ i₂) hπ (GlobalTheory.T.isLocalization_away_ferrandPush_fib i₁ i₂)`. Set `F` to `ThickGlue.specDiagram (good i₁ i₂) (fib i₁ i₂)`. Use `haveI hF : ∀ {U V : good i₁ i₂} (f : U ⟶ V), IsOpenImmersion (F.map f) := fun {U V} f ↦ hopen _ U.2 _ V.2 f.le`.

Use `haveI : (F ⋙ Scheme.forget).IsLocallyDirected := GlobalTheory.T.isLocallyDirected_of_bijective_basis_compatible (good i₁ i₂) (fun U hU V _ x hx hy ↦ hbas₀ U hU V x hx hy) F hF (fun U ↦ ThickGlue.toSpec (fibπ i₁ i₂) U.1) (fun U ↦ by haveI := ThickGlue.isClosedImmersion_toSpec (fib …`. Conclude with `(ThickGlue.toSpec _ U.1).isClosedEmbedding.injective)`. Use the proof step `(fun U ↦ by haveI := ThickGlue.surjective_toSpec (fibπ i₁ i₂) U.2.1 (hπ U.1 U.2).1 (hπ U.1 U.2).2`. Conclude with `(ThickGlue.toSpec _ U.1).surjective)`. Use the proof step `(fun h ↦ ThickGlue.toSpec_naturality _ h)`.

Set `e₁ : ∀ U : good i₁ i₂, (upOpen i₁ U.1).toScheme ⟶ F.obj U` to `fun U ↦ (upOpen i₁ U.1).toSpecΓ ≫ Spec.map (cone i₁ i₂ U.1).fst`. Set `e₂ : ∀ U : good i₁ i₂, (upOpen i₂ U.1).toScheme ⟶ F.obj U` to `fun U ↦ (upOpen i₂ U.1).toSpecΓ ≫ Spec.map (cone i₁ i₂ U.1).snd`. Establish `hn1 : ∀ {U V : good i₁ i₂} (h : U.1 ≤ V.1), Y₁.homOfLE (upOpen_mono i₁ h) ≫ e₁ V = e₁ U ≫ F.map (homOfLE (show U ≤ V from h))`. Introduce `U V h`. Express the relevant statement in the definitionally equal form `_ = _ ≫ Spec.map (fibMap i₁ i₂ h)`.

Simplify using `only [e₁]`. Rewrite using `[← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, fibMap_fst]`. Establish `hn2 : ∀ {U V : good i₁ i₂} (h : U.1 ≤ V.1), Y₂.homOfLE (upOpen_mono i₂ h) ≫ e₂ V = e₂ U ≫ F.map (homOfLE (show U ≤ V from h))`. Introduce `U V h`. Express the relevant statement in the definitionally equal form `_ = _ ≫ Spec.map (fibMap i₁ i₂ h)`.

Simplify using `only [e₂]`. Rewrite using `[← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, fibMap_snd]`. Establish `hbasK : ∀ {Yk : Scheme.{0}} (ik : Y₀ ⟶ Yk) [IsClosedImmersion ik] [Surjective ik], ∀ U ∈ good i₁ i₂, ∀ V ∈ good i₁ i₂, ∀ y : Yk, y ∈ upOpen ik U → y ∈ upOpen ik V → ∃ W ∈ good i₁ i₂, y ∈ upOpen ik W ∧ W ≤ U ∧ W ≤ V`. Introduce `Yk ik _ _ U hU V _ y hyU hyV`. Take `⟨x, rfl⟩` from `ik.surjective y`.

Rewrite `hyU`, `hyV` using `[mem_upOpen_iff]`. Take `⟨W, hW, hxW, h1, h2⟩` from `hbas₀ U hU V x hyU hyV`. Conclude with `⟨W, hW, (mem_upOpen_iff ik W x).2 hxW, h1, h2⟩`. Establish `hcovK : ∀ {Yk : Scheme.{0}} (ik : Y₀ ⟶ Yk) [IsClosedImmersion ik] [Surjective ik], ∀ y : Yk, ∃ U ∈ good i₁ i₂, y ∈ upOpen ik U`. Introduce `Yk ik _ _ y`.

Take `⟨x, rfl⟩` from `ik.surjective y`. Take `⟨U, hU, hx⟩` from `GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x`. Conclude with `⟨U, hU, (mem_upOpen_iff ik U x).2 hx⟩`. Take `⟨j₁, hj₁⟩` from `GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis (good i₁ i₂) F Y₁ (upOpen i₁) (upOpen_mono i₁) (hbasK i₁) (hcovK i₁) e₁ hn1`. Take `⟨j₂, hj₂⟩` from `GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis (good i₁ i₂) F Y₂ (upOpen i₂) (upOpen_mono i₂) (hbasK i₂) (hcovK i₂) e₂ hn2`.

Take `⟨ci₁, su₁, pre₁⟩` from `GlobalTheory.T.isClosedImmersion_surjective_to_colimit (good i₁ i₂) F Y₁ (upOpen i₁) (upOpen_mono i₁) (hcovK i₁) e₁ (fun U ↦ isClosedImmersion_toSpecΓ_comp _ U.2.2.1 _ (hR U.1 U.2).1.1) (fun U ↦ surjective_toSpecΓ_comp _ U.2.2.1 _ (hR U.1 U.2).1.1 (hR U.1 U.2).1.2) hn1 j₁ hj₁`. Take `⟨ci₂, su₂, pre₂⟩` from `GlobalTheory.T.isClosedImmersion_surjective_to_colimit (good i₁ i₂) F Y₂ (upOpen i₂) (upOpen_mono i₂) (hcovK i₂) e₂ (fun U ↦ isClosedImmersion_toSpecΓ_comp _ U.2.2.2 _ (hR U.1 U.2).2.1.1) (fun U ↦ surjective_toSpecΓ_comp _ U.2.2.2 _ (hR U.1 U.2).2.1.1 (hR U.1 U.2).2.1.2) hn2 j₂ h …`. Establish `key1 : ∀ U : good i₁ i₂, U.1.ι ≫ i₁ ≫ j₁ = U.1.toSpecΓ ≫ Spec.map ((cone i₁ i₂ U.1).fst ≫ res i₁ U.1) ≫ colimit.ι F U`. Introduce `U`. Rewrite using `[← Scheme.Hom.resLE_comp_ι_assoc i₁ (preimage_upOpen i₁ U.1).ge, hj₁ U]`.

Simplify using `only [e₁, res, Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]`. Establish `key2 : ∀ U : good i₁ i₂, U.1.ι ≫ i₂ ≫ j₂ = U.1.toSpecΓ ≫ Spec.map ((cone i₁ i₂ U.1).snd ≫ res i₂ U.1) ≫ colimit.ι F U`. Introduce `U`. Rewrite using `[← Scheme.Hom.resLE_comp_ι_assoc i₂ (preimage_upOpen i₂ U.1).ge, hj₂ U]`. Simplify using `only [e₂, res, Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]`.

Establish `hw : i₁ ≫ j₁ = i₂ ≫ j₂`. Use `Scheme.hom_ext_of_forall _ _ fun x ↦ ?_` and prove the remaining obligations. Take `⟨U, hU, hx⟩` from `GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x`. Use `⟨U, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[key1 ⟨U, hU⟩, key2 ⟨U, hU⟩, (cone i₁ i₂ U).condition]`.

Establish `h0 : ∀ U : good i₁ i₂, (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F U).opensRange = U.1`. Introduce `U`. Express the relevant statement in the definitionally equal form `i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ (colimit.ι F U).opensRange) = U.1`. Rewrite using `[pre₁ U, preimage_upOpen]`. Use `⟨colimit F, j₁, j₂, hw, ci₁, ci₂, su₁, su₂, Set.range (fun U : good i₁ i₂ ↦ (colimit.ι F U).opensRange), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[TopologicalSpace.Opens.isBasis_iff_nbhd]`. Introduce `O y hy`. Take `⟨x, rfl⟩` from `(i₁ ≫ j₁).surjective y`. Take `⟨U₀, hU₀, hx₀⟩` from `GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x`. Take `⟨U, hU, hxU, -, hUO⟩` from `hbas₀ U₀ hU₀ ((i₁ ≫ j₁) ⁻¹ᵁ O) x hx₀ hy`.

Use `⟨_, ⟨⟨U, hU⟩, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show x ∈ (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F ⟨U, hU⟩).opensRange`. Rewrite using `[h0 ⟨U, hU⟩]`. Conclude with `hxU`. Introduce `z hz`.

Take `⟨x', rfl⟩` from `(i₁ ≫ j₁).surjective z`. Establish `hx' : x' ∈ (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F ⟨U, hU⟩).opensRange` using `hz`. Rewrite `hx'` using `[h0 ⟨U, hU⟩]`. Conclude with `hUO hx'`. Introduce and unpack `_ ⟨U, rfl⟩`.

Establish `hle : ⊤ ≤ (colimit.ι F U) ⁻¹ᵁ (colimit.ι F U).opensRange` using `fun x _ ↦ ⟨x, rfl⟩`. Use `haveI hiso : IsIso ((colimit.ι F U).appLE (colimit.ι F U).opensRange ⊤ hle) := by`. Use `(colimit.ι F U).isIso_app (colimit.ι F U).opensRange le_rfl` as an intermediate fact. Establish `: IsIso (homOfLE hle)` using `homOfLE_isIso_of_eq _ (top_le_iff.mp hle).symm`. Rewrite using `[Scheme.Hom.appLE]`.

Use `infer_instance`. Set `ψ : Γ(colimit F, (colimit.ι F U).opensRange) ≅ (fib i₁ i₂).obj (op U.1)` to `asIso ((colimit.ι F U).appLE (colimit.ι F U).opensRange ⊤ hle) ≪≫ Scheme.ΓSpecIso _`. Establish `a1` using `GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor (A := (fib i₁ i₂).obj (op U.1)) (colimit.ι F U) j₁ (upOpen i₁ U.1) (cone i₁ i₂ U.1).fst (pre₁ U) (hj₁ U)`. Establish `a2` using `GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor (A := (fib i₁ i₂).obj (op U.1)) (colimit.ι F U) j₂ (upOpen i₂ U.1) (cone i₁ i₂ U.1).snd (pre₂ U) (hj₂ U)`. Establish `P` using `IsPullback.of_isLimit (coneIsLimit i₁ i₂ U.1)`.

Use `P.of_iso ψ.symm (Y₁.presheaf.mapIso (eqToIso (pre₁ U)).op) (Y₂.presheaf.mapIso (eqToIso (pre₂ U)).op) (Y₀.presheaf.mapIso (eqToIso (h0 U)).op) ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Iso.symm_hom, Iso.eq_inv_comp]`. Simplify using `only [ψ, Iso.trans_hom, asIso_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]`. Rewrite using `[← reassoc_of% a1]`. Simplify using `only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map_assoc]`.

Rewrite using `[Iso.symm_hom, Iso.eq_inv_comp]`. Simplify using `only [ψ, Iso.trans_hom, asIso_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]`. Rewrite using `[← reassoc_of% a2]`. Simplify using `only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map_assoc]`. Simplify using `only [res, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]`.

Simplify using `only [res, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]`.
-/
theorem exists_pushout_data : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ Surjective j₁ ∧ Surjective j₂ ∧ ∃ 𝒱 : Set Y.Opens, TopologicalSpace.Opens.IsBasis 𝒱 ∧ ∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ hc₁ hc₂ hs₁ hs₂ hn₁ hn₂
  haveI := hc₁; haveI := hc₂; haveI := hs₁; haveI := hs₂
  have hR : ∀ U ∈ good i₁ i₂, _ := fun U (hU : U ∈ good i₁ i₂) ↦
    GlobalTheory.T.pullbackCone_surjective_nilpotent_ker (res i₁ U) (res i₂ U) (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₁ hn₁ U hU.2.1).1 (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₁ hn₁ U hU.2.1).2
      (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₂ hn₂ U hU.2.2).1 (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₂ hn₂ U hU.2.2).2
  have hπ : ∀ U ∈ good i₁ i₂, Function.Surjective ((fibπ i₁ i₂).app (op U)).hom ∧
      IsNilpotent (RingHom.ker ((fibπ i₁ i₂).app (op U)).hom) := fun U hU ↦ (hR U hU).2.2
  have hbas₀ : ∀ U ∈ good i₁ i₂, ∀ (W : Y₀.Opens) (x : Y₀), x ∈ U → x ∈ W →
      ∃ V ∈ good i₁ i₂, x ∈ V ∧ V ≤ U ∧ V ≤ W := by
    intro U hU W x hxU hxW
    obtain ⟨f, hf, hxf⟩ := hU.1.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
    obtain ⟨a, rfl⟩ := (hπ U hU).1 f
    exact ⟨_, GlobalTheory.T.ferrand_pushout_good_basic_open i₁ i₂ U hU a, hxf, Y₀.basicOpen_le _, hf⟩
  have hopen := GlobalTheory.T.isOpenImmersion_of_nilpotent_thickening_cover Y₀ (good i₁ i₂) (fun U hU ↦ hU.1) (fib i₁ i₂) (fibπ i₁ i₂) hπ (GlobalTheory.T.isLocalization_away_ferrandPush_fib i₁ i₂)
  let F := ThickGlue.specDiagram (good i₁ i₂) (fib i₁ i₂)
  haveI hF : ∀ {U V : good i₁ i₂} (f : U ⟶ V), IsOpenImmersion (F.map f) :=
    fun {U V} f ↦ hopen _ U.2 _ V.2 f.le
  haveI : (F ⋙ Scheme.forget).IsLocallyDirected :=
    GlobalTheory.T.isLocallyDirected_of_bijective_basis_compatible (good i₁ i₂) (fun U hU V _ x hx hy ↦ hbas₀ U hU V x hx hy) F hF
      (fun U ↦ ThickGlue.toSpec (fibπ i₁ i₂) U.1)
      (fun U ↦ by
        haveI := ThickGlue.isClosedImmersion_toSpec (fibπ i₁ i₂) U.2.1 (hπ U.1 U.2).1
        exact (ThickGlue.toSpec _ U.1).isClosedEmbedding.injective)
      (fun U ↦ by
        haveI := ThickGlue.surjective_toSpec (fibπ i₁ i₂) U.2.1 (hπ U.1 U.2).1 (hπ U.1 U.2).2
        exact (ThickGlue.toSpec _ U.1).surjective)
      (fun h ↦ ThickGlue.toSpec_naturality _ h)
  let e₁ : ∀ U : good i₁ i₂, (upOpen i₁ U.1).toScheme ⟶ F.obj U := fun U ↦
    (upOpen i₁ U.1).toSpecΓ ≫ Spec.map (cone i₁ i₂ U.1).fst
  let e₂ : ∀ U : good i₁ i₂, (upOpen i₂ U.1).toScheme ⟶ F.obj U := fun U ↦
    (upOpen i₂ U.1).toSpecΓ ≫ Spec.map (cone i₁ i₂ U.1).snd
  have hn1 : ∀ {U V : good i₁ i₂} (h : U.1 ≤ V.1), Y₁.homOfLE (upOpen_mono i₁ h) ≫ e₁ V =
      e₁ U ≫ F.map (homOfLE (show U ≤ V from h)) := by
    intro U V h
    change _ = _ ≫ Spec.map (fibMap i₁ i₂ h)
    simp only [e₁]
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, fibMap_fst]
  have hn2 : ∀ {U V : good i₁ i₂} (h : U.1 ≤ V.1), Y₂.homOfLE (upOpen_mono i₂ h) ≫ e₂ V =
      e₂ U ≫ F.map (homOfLE (show U ≤ V from h)) := by
    intro U V h
    change _ = _ ≫ Spec.map (fibMap i₁ i₂ h)
    simp only [e₂]
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, fibMap_snd]
  have hbasK : ∀ {Yk : Scheme.{0}} (ik : Y₀ ⟶ Yk) [IsClosedImmersion ik] [Surjective ik],
      ∀ U ∈ good i₁ i₂, ∀ V ∈ good i₁ i₂, ∀ y : Yk, y ∈ upOpen ik U → y ∈ upOpen ik V →
        ∃ W ∈ good i₁ i₂, y ∈ upOpen ik W ∧ W ≤ U ∧ W ≤ V := by
    intro Yk ik _ _ U hU V _ y hyU hyV
    obtain ⟨x, rfl⟩ := ik.surjective y
    rw [mem_upOpen_iff] at hyU hyV
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas₀ U hU V x hyU hyV
    exact ⟨W, hW, (mem_upOpen_iff ik W x).2 hxW, h1, h2⟩
  have hcovK : ∀ {Yk : Scheme.{0}} (ik : Y₀ ⟶ Yk) [IsClosedImmersion ik] [Surjective ik],
      ∀ y : Yk, ∃ U ∈ good i₁ i₂, y ∈ upOpen ik U := by
    intro Yk ik _ _ y
    obtain ⟨x, rfl⟩ := ik.surjective y
    obtain ⟨U, hU, hx⟩ := GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x
    exact ⟨U, hU, (mem_upOpen_iff ik U x).2 hx⟩
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis (good i₁ i₂) F Y₁ (upOpen i₁) (upOpen_mono i₁) (hbasK i₁)
    (hcovK i₁) e₁ hn1
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis (good i₁ i₂) F Y₂ (upOpen i₂) (upOpen_mono i₂) (hbasK i₂)
    (hcovK i₂) e₂ hn2
  obtain ⟨ci₁, su₁, pre₁⟩ := GlobalTheory.T.isClosedImmersion_surjective_to_colimit (good i₁ i₂) F Y₁ (upOpen i₁) (upOpen_mono i₁) (hcovK i₁) e₁
    (fun U ↦ isClosedImmersion_toSpecΓ_comp _ U.2.2.1 _ (hR U.1 U.2).1.1)
    (fun U ↦ surjective_toSpecΓ_comp _ U.2.2.1 _ (hR U.1 U.2).1.1 (hR U.1 U.2).1.2) hn1 j₁ hj₁
  obtain ⟨ci₂, su₂, pre₂⟩ := GlobalTheory.T.isClosedImmersion_surjective_to_colimit (good i₁ i₂) F Y₂ (upOpen i₂) (upOpen_mono i₂) (hcovK i₂) e₂
    (fun U ↦ isClosedImmersion_toSpecΓ_comp _ U.2.2.2 _ (hR U.1 U.2).2.1.1)
    (fun U ↦ surjective_toSpecΓ_comp _ U.2.2.2 _ (hR U.1 U.2).2.1.1 (hR U.1 U.2).2.1.2) hn2 j₂ hj₂
  have key1 : ∀ U : good i₁ i₂, U.1.ι ≫ i₁ ≫ j₁ =
      U.1.toSpecΓ ≫ Spec.map ((cone i₁ i₂ U.1).fst ≫ res i₁ U.1) ≫ colimit.ι F U := by
    intro U
    rw [← Scheme.Hom.resLE_comp_ι_assoc i₁ (preimage_upOpen i₁ U.1).ge, hj₁ U]
    simp only [e₁, res, Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  have key2 : ∀ U : good i₁ i₂, U.1.ι ≫ i₂ ≫ j₂ =
      U.1.toSpecΓ ≫ Spec.map ((cone i₁ i₂ U.1).snd ≫ res i₂ U.1) ≫ colimit.ι F U := by
    intro U
    rw [← Scheme.Hom.resLE_comp_ι_assoc i₂ (preimage_upOpen i₂ U.1).ge, hj₂ U]
    simp only [e₂, res, Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  have hw : i₁ ≫ j₁ = i₂ ≫ j₂ := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨U, hU, hx⟩ := GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x
    refine ⟨U, hx, ?_⟩
    rw [key1 ⟨U, hU⟩, key2 ⟨U, hU⟩, (cone i₁ i₂ U).condition]
  have h0 : ∀ U : good i₁ i₂, (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    intro U
    change i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ (colimit.ι F U).opensRange) = U.1
    rw [pre₁ U, preimage_upOpen]
  refine ⟨colimit F, j₁, j₂, hw, ci₁, ci₂, su₁, su₂,
    Set.range (fun U : good i₁ i₂ ↦ (colimit.ι F U).opensRange), ?_, ?_⟩
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O y hy
    obtain ⟨x, rfl⟩ := (i₁ ≫ j₁).surjective y
    obtain ⟨U₀, hU₀, hx₀⟩ := GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x
    obtain ⟨U, hU, hxU, -, hUO⟩ := hbas₀ U₀ hU₀ ((i₁ ≫ j₁) ⁻¹ᵁ O) x hx₀ hy
    refine ⟨_, ⟨⟨U, hU⟩, rfl⟩, ?_, ?_⟩
    · show x ∈ (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F ⟨U, hU⟩).opensRange
      rw [h0 ⟨U, hU⟩]
      exact hxU
    · intro z hz
      obtain ⟨x', rfl⟩ := (i₁ ≫ j₁).surjective z
      have hx' : x' ∈ (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F ⟨U, hU⟩).opensRange := hz
      rw [h0 ⟨U, hU⟩] at hx'
      exact hUO hx'
  · rintro _ ⟨U, rfl⟩
    have hle : ⊤ ≤ (colimit.ι F U) ⁻¹ᵁ (colimit.ι F U).opensRange := fun x _ ↦ ⟨x, rfl⟩
    haveI hiso : IsIso ((colimit.ι F U).appLE (colimit.ι F U).opensRange ⊤ hle) := by
      have := (colimit.ι F U).isIso_app (colimit.ι F U).opensRange le_rfl
      have : IsIso (homOfLE hle) := homOfLE_isIso_of_eq _ (top_le_iff.mp hle).symm
      rw [Scheme.Hom.appLE]
      infer_instance
    let ψ : Γ(colimit F, (colimit.ι F U).opensRange) ≅ (fib i₁ i₂).obj (op U.1) :=
      asIso ((colimit.ι F U).appLE (colimit.ι F U).opensRange ⊤ hle) ≪≫ Scheme.ΓSpecIso _
    have a1 := GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor (A := (fib i₁ i₂).obj (op U.1)) (colimit.ι F U) j₁ (upOpen i₁ U.1)
      (cone i₁ i₂ U.1).fst (pre₁ U) (hj₁ U)
    have a2 := GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor (A := (fib i₁ i₂).obj (op U.1)) (colimit.ι F U) j₂ (upOpen i₂ U.1)
      (cone i₁ i₂ U.1).snd (pre₂ U) (hj₂ U)
    have P := IsPullback.of_isLimit (coneIsLimit i₁ i₂ U.1)
    refine P.of_iso ψ.symm (Y₁.presheaf.mapIso (eqToIso (pre₁ U)).op)
      (Y₂.presheaf.mapIso (eqToIso (pre₂ U)).op) (Y₀.presheaf.mapIso (eqToIso (h0 U)).op)
      ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Iso.eq_inv_comp]
      simp only [ψ, Iso.trans_hom, asIso_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom,
        eqToIso.hom]
      rw [← reassoc_of% a1]
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map_assoc]
    · rw [Iso.symm_hom, Iso.eq_inv_comp]
      simp only [ψ, Iso.trans_hom, asIso_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom,
        eqToIso.hom]
      rw [← reassoc_of% a2]
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map_assoc]
    · simp only [res, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
    · simp only [res, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]

end GlobalTheory.FerrandPush
