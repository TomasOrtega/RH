import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.AffineOpenAgree

/- English proof (translation)
Establish `h0 : (⊤ : N.toScheme.Opens) ≤ N.ι ⁻¹ᵁ N` using `by simp`. Establish `e1 : N.topIso.inv = N.ι.app N ≫ N.toScheme.presheaf.map (homOfLE h0).op`. Rewrite using `[Scheme.Opens.topIso_inv, Scheme.Opens.ι_app]`. Express the relevant statement in the definitionally equal form `_ = X.presheaf.map _ ≫ X.presheaf.map _`. Conclude with `(congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)`.

Establish `e2` using `c.naturality (homOfLE h0).op`. Rewrite using `[e1, Scheme.Hom.comp_app]`. Use `(Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_).symm |>.symm` and prove the remaining obligations. Use `congrArg (N.ι.app N ≫ ·) ?_` and prove the remaining obligations. Use `Eq.trans ?_ e2.symm` and prove the remaining obligations.

Both sides reduce to the same expression.
-/
theorem app_restrict_eq (X W : Scheme.{0}) (N : X.Opens) (c : W ⟶ N.toScheme) (hc : ⊤ ≤ (c ≫ N.ι) ⁻¹ᵁ N) :
    (c ≫ N.ι).app N ≫ W.presheaf.map (homOfLE hc).op = N.topIso.inv ≫ c.appTop := by
  have h0 : (⊤ : N.toScheme.Opens) ≤ N.ι ⁻¹ᵁ N := by simp
  have e1 : N.topIso.inv = N.ι.app N ≫ N.toScheme.presheaf.map (homOfLE h0).op := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_app]
    change _ = X.presheaf.map _ ≫ X.presheaf.map _
    exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)
  have e2 := c.naturality (homOfLE h0).op
  rw [e1, Scheme.Hom.comp_app]
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_).symm |>.symm
  refine congrArg (N.ι.app N ≫ ·) ?_
  refine Eq.trans ?_ e2.symm
  rfl

/- English proof (translation)
Establish `e` using `c.naturality (homOfLE (le_top : N ≤ ⊤)).op`. Establish `e'` using `congrArg (fun f => (f ≫ W.presheaf.map (homOfLE hc).op).hom (sm.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))) e`. Simplify using `only [Category.assoc, ← Functor.map_comp] at e'`. Simplify using `only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]`. Use `(e'.trans ?_)` and prove the remaining obligations.

Rewrite using `[Scheme.Hom.comp_appTop]`. Establish `: ((TopologicalSpace.Opens.map c.base).map (homOfLE (le_top : N ≤ ⊤)).op.unop).op ≫ (homOfLE hc).op = 𝟙 _` using `Subsingleton.elim _ _`. Rewrite using `[this]`. Use `erw [W.presheaf.map_id, Category.comp_id]`. Both sides reduce to the same expression.
-/
theorem cst_pull {R : Type} [CommRing R] {X W : Scheme.{0}} (sm : X ⟶ Spec (CommRingCat.of R)) (N : X.Opens)
    (c : W ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ N) (x : R) :
    (W.presheaf.map (homOfLE hc).op).hom ((c.app N).hom (GlobalTheory.AbLaw.cst sm N x)) =
      (c ≫ sm).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := by
  have e := c.naturality (homOfLE (le_top : N ≤ ⊤)).op
  have e' := congrArg (fun f => (f ≫ W.presheaf.map (homOfLE hc).op).hom (sm.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))) e
  simp only [Category.assoc, ← Functor.map_comp] at e'
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]
  refine (e'.trans ?_)
  rw [Scheme.Hom.comp_appTop]
  have : ((TopologicalSpace.Opens.map c.base).map (homOfLE (le_top : N ≤ ⊤)).op.unop).op ≫ (homOfLE hc).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  erw [W.presheaf.map_id, Category.comp_id]
  rfl

end GlobalTheory.AffineOpenAgree

namespace GlobalTheory
open AffineOpenAgree

/- English proof (translation)
Establish `hφ : ∀ g : Γ(X, N), (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom g) = (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom g)`. Set `φa : Γ(X, N) →+* Γ(W, ⊤)` to `(W.presheaf.map (homOfLE ha).op).hom.comp (a.app N).hom`. Set `φb : Γ(X, N) →+* Γ(W, ⊤)` to `(W.presheaf.map (homOfLE hb).op).hom.comp (b.app N).hom`. Establish `hc : φa.comp (GlobalTheory.AbLaw.cst sm N) = φb.comp (GlobalTheory.AbLaw.cst sm N)`. Use extensionality with `x`.

Simplify using `only [RingHom.comp_apply, φa, φb]`. Rewrite using `[cst_pull sm N a ha, cst_pull sm N b hb, hab]`. Establish `hrr : (⇑φa ∘ r) = (⇑φb ∘ r)` using `funext hr`. Establish `hev : ∀ P : MvPolynomial (Fin m) R, φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) = φb (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P)`. Introduce `P`.

Rewrite using `[MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hc, hrr]`. Introduce `g`. Take `⟨P, Q, hQ, hg⟩` from `hgen g`. Establish `h1` using `congrArg φa hg`. Establish `h2` using `congrArg φb hg`.

Rewrite `h1`, `h2` using `[map_mul]`. Establish `hu : IsUnit (φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q))` using `hQ.map φa`. Express the relevant statement in the definitionally equal form `φa g = φb g`. Use `hu.mul_left_injective ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[h1, hev P, ← h2, ← hev Q]`. Use `haveI : IsAffine N := hN`. Establish `hra : Set.range a ⊆ Set.range N.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`.

Conclude with `ha trivial`. Establish `hrb : Set.range b ⊆ Set.range N.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `hb trivial`.

Take `⟨a', rfl⟩ : ∃ a', a' ≫ N.ι = a` from `⟨_, IsOpenImmersion.lift_fac N.ι a hra⟩`. Take `⟨b', rfl⟩ : ∃ b', b' ≫ N.ι = b` from `⟨_, IsOpenImmersion.lift_fac N.ι b hrb⟩`. Use `congrArg (· ≫ N.ι) (ext_of_isAffine ?_)` and prove the remaining obligations. Use extensionality with `x`. Establish `ea` using `congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N a' ha)`.

Establish `eb` using `congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N b' hb)`. Establish `key` using `ea.symm.trans ((hφ _).trans eb)`. Simplify using `only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] at key`. Conclude with `key`.
-/
theorem eq_of_agree_on_generators (R : Type) [CommRing R] (X W : Scheme.{0}) (sm : X ⟶ Spec (CommRingCat.of R))
    (N : X.Opens) (hN : IsAffineOpen N) (m : ℕ) (r : Fin m → Γ(X, N))
    (hgen : ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q) ∧
        g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P)
    (a b : W ⟶ X) (hab : a ≫ sm = b ≫ sm) (ha : ⊤ ≤ a ⁻¹ᵁ N) (hb : ⊤ ≤ b ⁻¹ᵁ N)
    (hr : ∀ l, (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom (r l)) =
      (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom (r l))) : a = b := by

  have hφ : ∀ g : Γ(X, N), (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom g) =
      (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom g) := by
    let φa : Γ(X, N) →+* Γ(W, ⊤) := (W.presheaf.map (homOfLE ha).op).hom.comp (a.app N).hom
    let φb : Γ(X, N) →+* Γ(W, ⊤) := (W.presheaf.map (homOfLE hb).op).hom.comp (b.app N).hom
    have hc : φa.comp (GlobalTheory.AbLaw.cst sm N) = φb.comp (GlobalTheory.AbLaw.cst sm N) := by
      ext x
      simp only [RingHom.comp_apply, φa, φb]
      rw [cst_pull sm N a ha, cst_pull sm N b hb, hab]
    have hrr : (⇑φa ∘ r) = (⇑φb ∘ r) := funext hr
    have hev : ∀ P : MvPolynomial (Fin m) R, φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) =
        φb (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) := by
      intro P
      rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hc, hrr]
    intro g
    obtain ⟨P, Q, hQ, hg⟩ := hgen g
    have h1 := congrArg φa hg
    have h2 := congrArg φb hg
    rw [map_mul] at h1 h2
    have hu : IsUnit (φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q)) := hQ.map φa
    change φa g = φb g
    refine hu.mul_left_injective ?_
    simp only
    rw [h1, hev P, ← h2, ← hev Q]
  haveI : IsAffine N := hN
  have hra : Set.range a ⊆ Set.range N.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact ha trivial
  have hrb : Set.range b ⊆ Set.range N.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact hb trivial
  obtain ⟨a', rfl⟩ : ∃ a', a' ≫ N.ι = a := ⟨_, IsOpenImmersion.lift_fac N.ι a hra⟩
  obtain ⟨b', rfl⟩ : ∃ b', b' ≫ N.ι = b := ⟨_, IsOpenImmersion.lift_fac N.ι b hrb⟩
  refine congrArg (· ≫ N.ι) (ext_of_isAffine ?_)
  ext x
  have ea := congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N a' ha)
  have eb := congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N b' hb)
  have key := ea.symm.trans ((hφ _).trans eb)
  simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] at key
  exact key

end GlobalTheory
