import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartPreirreducibleFiberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceTensorOfPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
The claim follows from `SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen c) P`.
-/
theorem affineOpen_fromSpec_mem_basicOpen_iff {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U)
    (c : Γ(Y, U)) (P : PrimeSpectrum Γ(Y, U)) : hU.fromSpec P ∈ Y.basicOpen c ↔ c ∉ P.asIdeal :=
  SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen c) P

/- English proof (translation)
Introduce `X S f e hf hef s`. Take `⟨V, W, hWV, hV, hW, hes, hirr⟩` from `GlobalTheory.T.exists_affine_chart_preirreducible_fiber' X S f e hf hef s`. Establish `hfes : f (e s) = s` using `by rw [← Scheme.Hom.comp_apply, hef]; rfl`. Establish `hsV : s ∈ V` using `by have h := hWV hes; rwa [Scheme.Hom.mem_preimage, hfes] at h`. Use `letI : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra`.

Establish `hsm : Algebra.Smooth Γ(S, V) Γ(X, W)` using `RingHom.smooth_algebraMap.mp (HasRingHomProperty.appLE @Smooth f hf ⟨V, hV⟩ ⟨W, hW⟩ hWV)`. Establish `hcomap : ∀ (x : X) (hxW : x ∈ W) (hxV : f x ∈ V), (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal` using `fun x hxW hxV => congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hxW)`. Establish `hfx : ∀ r : Spec Γ(X, W), f (hW.fromSpec r) = hV.fromSpec (Spec.map (f.appLE V W hWV) r)` using `fun r => by show (hW.fromSpec ≫ f) r = (Spec.map (f.appLE V W hWV) ≫ hV.fromSpec) r`. Rewrite using `[IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV]`. Use `set q := hW.primeIdealOf ⟨e s, hes⟩ with hqdef`.

Use `set p₀ := hV.primeIdealOf ⟨s, hsV⟩ with hp₀def`. Establish `hq : q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = p₀.asIdeal`. Rewrite using `[hqdef, hcomap (e s) hes (hWV hes)]`. Use `congr 2`. Conclude with `Subtype.ext hfes`.

Set `Ω` to `AlgebraicClosure p₀.asIdeal.ResidueField`. Establish `hker : RingHom.ker (algebraMap Γ(S, V) Ω) = p₀.asIdeal`. Rewrite using `[IsScalarTower.algebraMap_eq Γ(S, V) p₀.asIdeal.ResidueField Ω, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap p₀.asIdeal.ResidueField Ω).injective]`. Conclude with `Ideal.ker_algebraMap_residueField _`. Establish `hpt : (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) ≫ hV.fromSpec) (IsLocalRing.closedPoint Ω) = s`.

Establish `: Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω) = p₀`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap Γ(S, V) Ω) (IsLocalRing.maximalIdeal Ω) = p₀.asIdeal`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]`. Use `show hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω)) = s`.

Rewrite using `[this, hp₀def, hV.fromSpec_primeIdealOf]`. Establish `h1` using `hirr Ω _ hpt`. Establish `h2` using `GlobalTheory.T.preirreducibleSpace_tensor_of_pullback' X S f V W hWV hV hW Ω rfl h1`. Take `⟨b, a, I, hb, ha, hI, hmain⟩` from `GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth Γ(S, V) Γ(X, W) hsm q Ω (hq.trans hker.symm) h2`. Use `⟨X.basicOpen b, S.basicOpen a, V, I, S.basicOpen_le a, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `(affineOpen_fromSpec_mem_basicOpen_iff hV a p₀).mpr (by rw [← hq]; exact ha)`. Rewrite `h` using `[hp₀def, hV.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Establish `h` using `(affineOpen_fromSpec_mem_basicOpen_iff hW b q).mpr hb`. Rewrite `h` using `[hqdef, hW.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Introduce `c hc hsc`.

Establish `h` using `(affineOpen_fromSpec_mem_basicOpen_iff hV c p₀).mp (by rw [hp₀def, hV.fromSpec_primeIdealOf]; exact hsc)`. Conclude with `h (by rw [← hq]; exact hI c hc)`. Introduce `t htV₀ htI`. Establish `htV : t ∈ V` using `S.basicOpen_le a htV₀`. Use `set t' := hV.primeIdealOf ⟨t, htV⟩ with ht'def`.

Establish `hft' : hV.fromSpec t' = t` using `hV.fromSpec_primeIdealOf _`. Establish `ha' : a ∉ t'.asIdeal` using `(affineOpen_fromSpec_mem_basicOpen_iff hV a t').mp (by rw [hft']; exact htV₀)`. Establish `hc' : ∀ c ∈ I, c ∈ t'.asIdeal` using `fun c hc => by`. Assume the negation of the conclusion as `hnc`. Conclude with `htI c hc (hft' ▸ (affineOpen_fromSpec_mem_basicOpen_iff hV c t').mpr hnc)`.

Establish `hZ` using `hmain t' ha' hc'`. Establish `heq : ((X.basicOpen b : X.Opens) : Set X) ∩ f ⁻¹' {t} = hW.fromSpec '' {r : PrimeSpectrum Γ(X, W) | r.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = t'.asIdeal ∧ b ∉ r.asIdeal}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxU, hxt⟩`.

Establish `hxW : x ∈ W` using `X.basicOpen_le b hxU`. Establish `hxt' : f x = t` using `hxt`. Use `⟨hW.primeIdealOf ⟨x, hxW⟩, ⟨?_, ?_⟩, hW.fromSpec_primeIdealOf _⟩` and prove the remaining obligations. Rewrite using `[hcomap x hxW (hWV hxW), ht'def]`. Use `congr 2`.

Conclude with `Subtype.ext hxt'`. Conclude with `(affineOpen_fromSpec_mem_basicOpen_iff hW b _).mp (by rw [hW.fromSpec_primeIdealOf]; exact hxU)`. Introduce and unpack `⟨r, ⟨hr1, hr2⟩, rfl⟩`. Use `⟨(affineOpen_fromSpec_mem_basicOpen_iff hW b r).mpr hr2, ?_⟩` and prove the remaining obligations. Use `show f (hW.fromSpec r) = t`.

Establish `: Spec.map (f.appLE V W hWV) r = t'` using `PrimeSpectrum.ext hr1`. Rewrite using `[hfx, this, hft']`. Rewrite using `[heq]`. Conclude with `hZ.image _ (Scheme.Hom.continuous _).continuousOn`.
-/
theorem exists_open_nbhd_section_fibre_isPreirreducible : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X),
    Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (U : X.Opens) (V₀ V : S.Opens) (I : Finset Γ(S, V)),
      V₀ ≤ V ∧ s ∈ V₀ ∧ e s ∈ U ∧ (∀ c ∈ I, s ∉ S.basicOpen c) ∧
      ∀ t ∈ V₀, (∀ c ∈ I, t ∉ S.basicOpen c) → IsPreirreducible ((U : Set X) ∩ f ⁻¹' {t}) := by
  intro X S f e hf hef s
  obtain ⟨V, W, hWV, hV, hW, hes, hirr⟩ := GlobalTheory.T.exists_affine_chart_preirreducible_fiber' X S f e hf hef s
  have hfes : f (e s) = s := by rw [← Scheme.Hom.comp_apply, hef]; rfl
  have hsV : s ∈ V := by have h := hWV hes; rwa [Scheme.Hom.mem_preimage, hfes] at h
  letI : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  have hsm : Algebra.Smooth Γ(S, V) Γ(X, W) :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.appLE @Smooth f hf ⟨V, hV⟩ ⟨W, hW⟩ hWV)

  have hcomap : ∀ (x : X) (hxW : x ∈ W) (hxV : f x ∈ V),
      (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) =
        (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal := fun x hxW hxV =>
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hxW)
  have hfx : ∀ r : Spec Γ(X, W), f (hW.fromSpec r) =
      hV.fromSpec (Spec.map (f.appLE V W hWV) r) := fun r => by
    show (hW.fromSpec ≫ f) r = (Spec.map (f.appLE V W hWV) ≫ hV.fromSpec) r
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV]
  set q := hW.primeIdealOf ⟨e s, hes⟩ with hqdef
  set p₀ := hV.primeIdealOf ⟨s, hsV⟩ with hp₀def
  have hq : q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = p₀.asIdeal := by
    rw [hqdef, hcomap (e s) hes (hWV hes)]
    congr 2; exact Subtype.ext hfes
  let Ω := AlgebraicClosure p₀.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap Γ(S, V) Ω) = p₀.asIdeal := by
    rw [IsScalarTower.algebraMap_eq Γ(S, V) p₀.asIdeal.ResidueField Ω, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap p₀.asIdeal.ResidueField Ω).injective]
    exact Ideal.ker_algebraMap_residueField _
  have hpt : (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) ≫ hV.fromSpec)
      (IsLocalRing.closedPoint Ω) = s := by
    have : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω) = p₀ := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap Γ(S, V) Ω) (IsLocalRing.maximalIdeal Ω) = p₀.asIdeal
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
    show hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω)) (IsLocalRing.closedPoint Ω)) = s
    rw [this, hp₀def, hV.fromSpec_primeIdealOf]
  have h1 := hirr Ω _ hpt
  have h2 := GlobalTheory.T.preirreducibleSpace_tensor_of_pullback' X S f V W hWV hV hW Ω rfl h1
  obtain ⟨b, a, I, hb, ha, hI, hmain⟩ := GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth Γ(S, V) Γ(X, W) hsm q Ω (hq.trans hker.symm) h2
  refine ⟨X.basicOpen b, S.basicOpen a, V, I, S.basicOpen_le a, ?_, ?_, ?_, ?_⟩
  · have h := (affineOpen_fromSpec_mem_basicOpen_iff hV a p₀).mpr (by rw [← hq]; exact ha)
    rwa [hp₀def, hV.fromSpec_primeIdealOf] at h
  · have h := (affineOpen_fromSpec_mem_basicOpen_iff hW b q).mpr hb
    rwa [hqdef, hW.fromSpec_primeIdealOf] at h
  · intro c hc hsc
    have h := (affineOpen_fromSpec_mem_basicOpen_iff hV c p₀).mp
      (by rw [hp₀def, hV.fromSpec_primeIdealOf]; exact hsc)
    exact h (by rw [← hq]; exact hI c hc)
  · intro t htV₀ htI
    have htV : t ∈ V := S.basicOpen_le a htV₀
    set t' := hV.primeIdealOf ⟨t, htV⟩ with ht'def
    have hft' : hV.fromSpec t' = t := hV.fromSpec_primeIdealOf _
    have ha' : a ∉ t'.asIdeal :=
      (affineOpen_fromSpec_mem_basicOpen_iff hV a t').mp (by rw [hft']; exact htV₀)
    have hc' : ∀ c ∈ I, c ∈ t'.asIdeal := fun c hc => by
      by_contra hnc
      exact htI c hc (hft' ▸ (affineOpen_fromSpec_mem_basicOpen_iff hV c t').mpr hnc)
    have hZ := hmain t' ha' hc'
    have heq : ((X.basicOpen b : X.Opens) : Set X) ∩ f ⁻¹' {t} = hW.fromSpec ''
        {r : PrimeSpectrum Γ(X, W) | r.asIdeal.comap (algebraMap Γ(S, V) Γ(X, W)) = t'.asIdeal ∧
          b ∉ r.asIdeal} := by
      ext x
      constructor
      · rintro ⟨hxU, hxt⟩
        have hxW : x ∈ W := X.basicOpen_le b hxU
        have hxt' : f x = t := hxt
        refine ⟨hW.primeIdealOf ⟨x, hxW⟩, ⟨?_, ?_⟩, hW.fromSpec_primeIdealOf _⟩
        · rw [hcomap x hxW (hWV hxW), ht'def]
          congr 2; exact Subtype.ext hxt'
        · exact (affineOpen_fromSpec_mem_basicOpen_iff hW b _).mp
            (by rw [hW.fromSpec_primeIdealOf]; exact hxU)
      · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
        refine ⟨(affineOpen_fromSpec_mem_basicOpen_iff hW b r).mpr hr2, ?_⟩
        show f (hW.fromSpec r) = t
        have : Spec.map (f.appLE V W hWV) r = t' := PrimeSpectrum.ext hr1
        rw [hfx, this, hft']
    rw [heq]
    exact hZ.image _ (Scheme.Hom.continuous _).continuousOn

end GlobalTheory
