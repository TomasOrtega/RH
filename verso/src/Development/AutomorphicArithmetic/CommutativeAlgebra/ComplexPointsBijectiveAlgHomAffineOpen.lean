import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.TopForm ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi in
/- English proof (translation)
Establish `h` using `congrArg (fun φ => φ a) (GlobalTheory.TopForm.resG_comp_algX p (le_top : V ≤ ⊤))`. Simplify using `only [RingHom.comp_apply] at h`. Rewrite using `[← h]`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, TopCat.Presheaf.germ_res_apply]`. Simplify using `only [algX, GlobalTheory.PD.ffAlg, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Scheme.Hom.appLE]`.

Simplify using `only [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]`. Both sides reduce to the same expression.
-/
private theorem germ_algX {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (V : X.Opens) (hg : genericPoint X ∈ V) (a : ℂ) :
    (X.presheaf.germ V (genericPoint X) hg).hom (algX p V a) = @algebraMap ℂ X.functionField _ _ (ffAlg p) a := by
  have h := congrArg (fun φ => φ a) (GlobalTheory.TopForm.resG_comp_algX p (le_top : V ≤ ⊤))
  simp only [RingHom.comp_apply] at h
  rw [← h]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, TopCat.Presheaf.germ_res_apply]
  simp only [algX, GlobalTheory.PD.ffAlg, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Scheme.Hom.appLE]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  rfl

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue in
/- English proof (translation)
Introduce `X _ p inst hinst V hV hg B hB`. Substitute `hinst` using the available equality. Use `set g := (X.presheaf.germ V (genericPoint X) hg).hom with hgdef`. Establish `ginj : Function.Injective g` using `germ_injective_of_isIntegral X (genericPoint X) hg`. Establish `gB : ∀ f, g f ∈ B` using `fun f => (hB _).2 ⟨f, rfl⟩`.

Set `gr : Γ(X, V) →+* B` to `g.codRestrict B gB`. Establish `grbij : Function.Bijective gr`. Use `⟨fun x y hxy => ginj (congrArg Subtype.val hxy), fun b => ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `(hB b.1).1 b.2`. Conclude with `⟨f, Subtype.ext hf⟩`.

Set `eqv : Γ(X, V) ≃+* B` to `RingEquiv.ofBijective gr grbij`. Establish `eqv_apply : ∀ f, eqv f = ⟨g f, gB f⟩` using `fun f => rfl`. Establish `alg_eq : ∀ a : ℂ, (algebraMap ℂ B a) = eqv (algX p V a)`. Introduce `a`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[eqv_apply]`. Conclude with `(germ_algX p V hg a).symm`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Set `φ : Γ(X, V) →+* ℂ` to `(e : B →+* ℂ).comp (eqv : Γ(X, V) →+* B)`.

Establish `hφ : ∀ a : ℂ, φ (algX p V a) = RingHom.id ℂ a`. Introduce `a`. Express the relevant statement in the definitionally equal form `e (eqv (algX p V a)) = a`. Rewrite using `[← alg_eq]`. Conclude with `e.commutes a`.

Use `⟨CxPts.ofHom hV φ hφ, ⟨CxPts.ofHom_mem hV φ hφ, fun f hf => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[CxPts.ev_ofHom]`. Both sides reduce to the same expression. Introduce and unpack `y ⟨hy, hye⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `GlobalTheory.Points.ext_of_valR hV hy (CxPts.ofHom_mem hV φ hφ)` to reduce the goal to its premises. Introduce `f`. Express the relevant statement in the definitionally equal form `CxPts.ev p (RingHom.id ℂ) V f y = CxPts.ev p (RingHom.id ℂ) V f (CxPts.ofHom hV φ hφ)`. Rewrite using `[CxPts.ev_ofHom, ← hye f (gB f)]`. Both sides reduce to the same expression.

Introduce `y hy`. Set `e0 : B →+* ℂ` to `(CxPts.evHom hy).comp (eqv.symm : B →+* Γ(X, V))`. Establish `he0 : ∀ a : ℂ, e0 (algebraMap ℂ B a) = algebraMap ℂ ℂ a`. Introduce `a`. Express the relevant statement in the definitionally equal form `CxPts.evHom hy (eqv.symm (algebraMap ℂ B a)) = a`.

Rewrite using `[alg_eq, RingEquiv.symm_apply_apply, ← CxPts.ev_eq hy, CxPts.ev_algX hy]`. Both sides reduce to the same expression. Set `e : B →ₐ[ℂ] ℂ` to `{ e0 with commutes' := he0 }`. Use `⟨e, ⟨hy, fun f hf => ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `CxPts.evHom hy (eqv.symm ⟨g f, hf⟩) = _`.

Rewrite using `[show (⟨g f, hf⟩ : B) = eqv f from rfl, RingEquiv.symm_apply_apply, CxPts.ev_eq hy]`. Introduce and unpack `e' ⟨_, he'⟩`. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `b`. Take `⟨f, hf⟩` from `(hB b.1).1 b.2`.

Establish `hb : b = ⟨g f, gB f⟩` using `Subtype.ext hf.symm`. Substitute `hb` using the available equality. Rewrite using `[he' f (gB f)]`. Express the relevant statement in the definitionally equal form `_ = CxPts.evHom hy (eqv.symm (eqv f))`. Rewrite using `[RingEquiv.symm_apply_apply, CxPts.ev_eq hy]`.
-/
theorem UpperTheory.complexPoints_bijective_algHom_affineOpen :
    ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (V : X.Opens), IsAffineOpen V → ∀ (hg : genericPoint X ∈ V) (B : Subalgebra ℂ X.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y) → (∀ e : B →ₐ[ℂ] ℂ, ∃! y : CxPts p (RingHom.id ℂ), UpperTheory.A.Mt p V hg B e y) ∧ (∀ y ∈ CxPts.ptsIn p (RingHom.id ℂ) V, ∃! e : B →ₐ[ℂ] ℂ, UpperTheory.A.Mt p V hg B e y) := by
  intro X _ p inst hinst V hV hg B hB
  subst hinst
  set g := (X.presheaf.germ V (genericPoint X) hg).hom with hgdef
  have ginj : Function.Injective g := germ_injective_of_isIntegral X (genericPoint X) hg
  have gB : ∀ f, g f ∈ B := fun f => (hB _).2 ⟨f, rfl⟩
  let gr : Γ(X, V) →+* B := g.codRestrict B gB
  have grbij : Function.Bijective gr := by
    refine ⟨fun x y hxy => ginj (congrArg Subtype.val hxy), fun b => ?_⟩
    obtain ⟨f, hf⟩ := (hB b.1).1 b.2
    exact ⟨f, Subtype.ext hf⟩
  let eqv : Γ(X, V) ≃+* B := RingEquiv.ofBijective gr grbij
  have eqv_apply : ∀ f, eqv f = ⟨g f, gB f⟩ := fun f => rfl
  have alg_eq : ∀ a : ℂ, (algebraMap ℂ B a) = eqv (algX p V a) := by
    intro a
    apply Subtype.ext
    rw [eqv_apply]
    exact (germ_algX p V hg a).symm
  constructor
  · intro e
    let φ : Γ(X, V) →+* ℂ := (e : B →+* ℂ).comp (eqv : Γ(X, V) →+* B)
    have hφ : ∀ a : ℂ, φ (algX p V a) = RingHom.id ℂ a := by
      intro a
      change e (eqv (algX p V a)) = a
      rw [← alg_eq]
      exact e.commutes a
    refine ⟨CxPts.ofHom hV φ hφ, ⟨CxPts.ofHom_mem hV φ hφ, fun f hf => ?_⟩, ?_⟩
    · rw [CxPts.ev_ofHom]
      rfl
    · rintro y ⟨hy, hye⟩
      apply Subtype.ext
      apply GlobalTheory.Points.ext_of_valR hV hy (CxPts.ofHom_mem hV φ hφ)
      intro f
      change CxPts.ev p (RingHom.id ℂ) V f y = CxPts.ev p (RingHom.id ℂ) V f (CxPts.ofHom hV φ hφ)
      rw [CxPts.ev_ofHom, ← hye f (gB f)]
      rfl
  · intro y hy
    let e0 : B →+* ℂ := (CxPts.evHom hy).comp (eqv.symm : B →+* Γ(X, V))
    have he0 : ∀ a : ℂ, e0 (algebraMap ℂ B a) = algebraMap ℂ ℂ a := by
      intro a
      change CxPts.evHom hy (eqv.symm (algebraMap ℂ B a)) = a
      rw [alg_eq, RingEquiv.symm_apply_apply, ← CxPts.ev_eq hy, CxPts.ev_algX hy]
      rfl
    let e : B →ₐ[ℂ] ℂ := { e0 with commutes' := he0 }
    refine ⟨e, ⟨hy, fun f hf => ?_⟩, ?_⟩
    · change CxPts.evHom hy (eqv.symm ⟨g f, hf⟩) = _
      rw [show (⟨g f, hf⟩ : B) = eqv f from rfl, RingEquiv.symm_apply_apply, CxPts.ev_eq hy]
    · rintro e' ⟨_, he'⟩
      apply AlgHom.ext
      intro b
      obtain ⟨f, hf⟩ := (hB b.1).1 b.2
      have hb : b = ⟨g f, gB f⟩ := Subtype.ext hf.symm
      subst hb
      rw [he' f (gB f)]
      change _ = CxPts.evHom hy (eqv.symm (eqv f))
      rw [RingEquiv.symm_apply_apply, CxPts.ev_eq hy]
