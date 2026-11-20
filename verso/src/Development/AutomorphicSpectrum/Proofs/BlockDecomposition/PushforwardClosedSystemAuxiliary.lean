import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.KerSupp

/- English proof (translation)
Set `S : ShortComplex X.Modules` to `ShortComplex.mk (kernel.ι g) g (kernel.condition _)`. Establish `hex : S.Exact` using `ShortComplex.exact_kernel _`. Establish `hm : Mono (cokernel.desc S.f S.g S.zero)` using `S.exact_iff_mono_cokernel_desc.1 hex`. Establish `h1 : Scheme.Modules.SupportedIn (cokernel (kernel.ι g)) T` using `Scheme.Modules.SupportedIn.of_mono (cokernel.desc S.f S.g S.zero) h`. Establish `e : (kernelSubobjectIso g).hom ≫ kernel.ι g = (kernelSubobject g).arrow` using `kernelSubobject_arrow g`.

Set `i : cokernel (kernelSubobject g).arrow ≅ cokernel (kernel.ι g)` to `cokernelIsoOfEq e.symm ≪≫ (cokernelEpiComp (kernelSubobjectIso g).hom _)`. Conclude with `h1.of_iso i.symm`.
-/
theorem supportedIn_cokernel_kernelSubobject {X : Scheme.{0}} {F G : X.Modules} (g : F ⟶ G) {T : Set X}
    (h : Scheme.Modules.SupportedIn G T) :
    Scheme.Modules.SupportedIn (cokernel (kernelSubobject g).arrow) T := by
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι g) g (kernel.condition _)
  have hex : S.Exact := ShortComplex.exact_kernel _
  have hm : Mono (cokernel.desc S.f S.g S.zero) := S.exact_iff_mono_cokernel_desc.1 hex
  have h1 : Scheme.Modules.SupportedIn (cokernel (kernel.ι g)) T :=
    Scheme.Modules.SupportedIn.of_mono (cokernel.desc S.f S.g S.zero) h
  have e : (kernelSubobjectIso g).hom ≫ kernel.ι g = (kernelSubobject g).arrow :=
    kernelSubobject_arrow g
  let i : cokernel (kernelSubobject g).arrow ≅ cokernel (kernel.ι g) :=
    cokernelIsoOfEq e.symm ≪≫ (cokernelEpiComp (kernelSubobjectIso g).hom _)
  exact h1.of_iso i.symm

/- English proof (translation)
Use `⟨fun y => ?_⟩` and prove the remaining obligations. Establish `h1 : f.imageι y ∈ (f.ker.support : Set X)` using `f.ker.range_subschemeι.le ⟨y, rfl⟩`. Rewrite `h1` using `[Scheme.Hom.support_ker, f.isClosedMap.isClosed_range.closure_eq]`. Take `⟨x, hx⟩` from `h1`. Use `⟨x, f.imageι.isEmbedding.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]`.
-/
theorem toImage_surjective {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] : Surjective f.toImage := by
  refine ⟨fun y => ?_⟩
  have h1 : f.imageι y ∈ (f.ker.support : Set X) := f.ker.range_subschemeι.le ⟨y, rfl⟩
  rw [Scheme.Hom.support_ker, f.isClosedMap.isClosed_range.closure_eq] at h1
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, f.imageι.isEmbedding.injective ?_⟩
  rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

/- English proof (translation)
Use `toImage_surjective f` as an intermediate fact. Establish `hu : UniversallyClosed (f.toImage ≫ f.ker.subschemeι ≫ p)`. Rewrite using `[← Category.assoc]`. Express the relevant statement in the definitionally equal form `UniversallyClosed ((f.toImage ≫ f.imageι) ≫ p)`. Rewrite using `[Scheme.Hom.toImage_imageι]`.

Use `infer_instance`. Establish `: UniversallyClosed (f.ker.subschemeι ≫ p)` using `.of_comp_surjective f.toImage _`. Conclude with `⟨⟩`.
-/
theorem isProper_image {S Y X : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p] [IsProper f] (hY : IsProper (f ≫ p)) :
    IsProper (f.ker.subschemeι ≫ p) := by
  have := toImage_surjective f
  have hu : UniversallyClosed (f.toImage ≫ f.ker.subschemeι ≫ p) := by
    rw [← Category.assoc]
    change UniversallyClosed ((f.toImage ≫ f.imageι) ≫ p)
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : UniversallyClosed (f.ker.subschemeι ≫ p) := .of_comp_surjective f.toImage _
  exact ⟨⟩

/- English proof (translation)
Take `⟨TZ, hTZ, hsupp⟩` from `hB`. Set `f : TZ.subscheme ⟶ X` to `TZ.subschemeι ≫ φ`. Establish `hf : IsProper f` using `inferInstance`. Establish `hfp : IsProper (f ≫ (X ↘ Spec (.of A)))`. Express the relevant statement in the definitionally equal form `IsProper ((TZ.subschemeι ≫ φ) ≫ (X ↘ Spec (.of A)))`.

Rewrite using `[Category.assoc, hc]`. Conclude with `hTZ`. Use `⟨f.ker, isProper_image f _ hfp, ?_⟩` and prove the remaining obligations. Establish `hpush` using `hsupp.pushforward φ`. Establish `hsub : φ.base '' (TZ.support : Set Z) ⊆ (f.ker.support : Set X)`.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨w, hw⟩` from `TZ.range_subschemeι.ge hz`. Rewrite using `[Scheme.Hom.support_ker]`. Use `subset_closure ⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw]`.

Both sides reduce to the same expression. Conclude with `supportedIn_cokernel_kernelSubobject (adjMap φ B) (hpush.mono hsub)`.
-/
theorem propSupp_adjKer {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : PropSupp A B) :
    PropSupp A (adjKer φ B) := by
  obtain ⟨TZ, hTZ, hsupp⟩ := hB
  let f : TZ.subscheme ⟶ X := TZ.subschemeι ≫ φ
  have hf : IsProper f := inferInstance
  have hfp : IsProper (f ≫ (X ↘ Spec (.of A))) := by
    change IsProper ((TZ.subschemeι ≫ φ) ≫ (X ↘ Spec (.of A)))
    rw [Category.assoc, hc]
    exact hTZ
  refine ⟨f.ker, isProper_image f _ hfp, ?_⟩
  have hpush := hsupp.pushforward φ
  have hsub : φ.base '' (TZ.support : Set Z) ⊆ (f.ker.support : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := TZ.range_subschemeι.ge hz
    rw [Scheme.Hom.support_ker]
    refine subset_closure ⟨w, ?_⟩
    rw [← hw]
    rfl
  exact supportedIn_cokernel_kernelSubobject (adjMap φ B) (hpush.mono hsub)

end GlobalTheory.CompanionTheory.GE.KerSupp
