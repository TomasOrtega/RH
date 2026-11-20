import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.SpecLimPf
open LateralTheory.E.LevelsGenPf

def gam {T : Scheme.{0}} {R : Type} [CommRing R] (x : T ⟶ Spec (CommRingCat.of R)) : R →+* Γ(T, ⊤) :=
  ((ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm x).unop.hom

def uns {T : Scheme.{0}} {R : Type} [CommRing R] (h : R →+* Γ(T, ⊤)) : T ⟶ Spec (CommRingCat.of R) :=
  ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R)) (CommRingCat.ofHom h).op

/- English proof (translation)
Establish `e` using `(ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm_apply_apply (CommRingCat.ofHom h).op`. Simplify using `only [gam, uns]`. Use `erw [e]`. Both sides reduce to the same expression.
-/
theorem gam_uns {T : Scheme.{0}} {R : Type} [CommRing R] (h : R →+* Γ(T, ⊤)) : gam (uns h) = h := by
  have e := (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm_apply_apply (CommRingCat.ofHom h).op
  simp only [gam, uns]
  erw [e]
  rfl

/- English proof (translation)
Apply `(ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm.injective` to reduce the goal to its premises. Apply `Opposite.unop_injective` to reduce the goal to its premises. Conclude with `CommRingCat.hom_ext h`.
-/
theorem gam_inj {T : Scheme.{0}} {R : Type} [CommRing R] {x y : T ⟶ Spec (CommRingCat.of R)}
    (h : gam x = gam y) : x = y := by
  apply (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm.injective
  apply Opposite.unop_injective
  exact CommRingCat.hom_ext h

/- English proof (translation)
Use `ΓSpec.adjunction.homEquiv_naturality_right_symm x (CommRingCat.ofHom f).op` as an intermediate fact. Simplify using `only [gam]`. Use `erw [this]`. Both sides reduce to the same expression.
-/
theorem gam_comp {T : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (x : T ⟶ Spec (CommRingCat.of S)) : gam (x ≫ Spec.map (CommRingCat.ofHom f)) = (gam x).comp f := by
  have := ΓSpec.adjunction.homEquiv_naturality_right_symm x (CommRingCat.ofHom f).op
  simp only [gam]
  erw [this]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cone_app_none {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (T : Scheme.{0}) (x : T ⟶ Spec (CommRingCat.of B)) :
    ((coneOf φ χ l hl).π.app none).app (op T) x = x ≫ Spec.map (CommRingCat.ofHom χ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cone_app_some {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (T : Scheme.{0}) (x : T ⟶ Spec (CommRingCat.of B)) (i : ι) :
    ((coneOf φ χ l hl).π.app (some i)).app (op T) x = x ≫ Spec.map (CommRingCat.ofHom (l i)) := rfl

/- English proof (translation)
Introduce `A A' B _ _ _ φ χ n l hl hcop`. Use `⟨evaluationJointlyReflectsLimits _ fun k => ?_⟩` and prove the remaining obligations. Take `⟨T⟩` from `k`. Set `F` to `WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A))) (fun _ : Fin (n + 1) => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))`. Establish `key : ∀ (s : Cone (F ⋙ (evaluation _ _).obj (op T))) (p : s.pt), ∀ i, (gam (s.π.app (some i) p)).comp φ = gam (s.π.app none p)`.

Introduce `s p i`. Establish `h : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) = (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) ≫ Spec.map (CommRingCat.ofHom φ)` using `(types_congr_hom (s.w (WidePullbackShape.Hom.term i)) p).symm`. Rewrite using `[h]`. Conclude with `(gam_comp φ _).symm`. Use `IsLimit.mk (fun s => TypeCat.ofHom fun p => uns (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)).exists.choose) ?_ ?_` and prove the remaining obligations.

Introduce `s j`. Use extensionality with `p`. Establish `hs` using `(hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)).exists.choose_spec`. Break down `j with _ | i` into its components or cases. Apply `gam_inj` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `gam (uns _ ≫ Spec.map (CommRingCat.ofHom χ)) = _`. Rewrite using `[gam_comp, gam_uns, hs.2]`. Both sides reduce to the same expression. Apply `gam_inj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `gam (uns _ ≫ Spec.map (CommRingCat.ofHom (l i))) = _`.

Rewrite using `[gam_comp, gam_uns, hs.1 i]`. Both sides reduce to the same expression. Introduce `s m hm`. Use extensionality with `p`. Establish `H` using `hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)`.

Express the relevant statement in the definitionally equal form `(m p : T ⟶ Spec (CommRingCat.of B)) = uns _`. Apply `gam_inj` to reduce the goal to its premises. Rewrite using `[gam_uns]`. Use `H.unique ⟨fun i => ?_, ?_⟩ H.exists.choose_spec` and prove the remaining obligations. Establish `e : (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) = (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom (l i))` using `(types_congr_hom (hm (some i)) p).symm`.

Express the relevant statement in the definitionally equal form `_ = gam (s.π.app (some i) p)`. Rewrite using `[e]`. Conclude with `(gam_comp _ _).symm`. Establish `e : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) = (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom χ)` using `(types_congr_hom (hm none) p).symm`. Rewrite using `[e]`.

Conclude with `(gam_comp _ _).symm`.
-/
theorem SpecLim_of : SpecLim := by
  intro A A' B _ _ _ φ χ n l hl hcop
  refine ⟨evaluationJointlyReflectsLimits _ fun k => ?_⟩
  obtain ⟨T⟩ := k

  let F := WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : Fin (n + 1) => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))
  have key : ∀ (s : Cone (F ⋙ (evaluation _ _).obj (op T))) (p : s.pt),
      ∀ i, (gam (s.π.app (some i) p)).comp φ = gam (s.π.app none p) := by
    intro s p i
    have h : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) =
        (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) ≫ Spec.map (CommRingCat.ofHom φ) :=
      (types_congr_hom (s.w (WidePullbackShape.Hom.term i)) p).symm
    rw [h]
    exact (gam_comp φ _).symm
  refine IsLimit.mk (fun s => TypeCat.ofHom fun p => uns (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p))
      (key s p)).exists.choose) ?_ ?_
  · intro s j
    ext p
    have hs := (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)).exists.choose_spec
    rcases j with _ | i
    · apply gam_inj
      change gam (uns _ ≫ Spec.map (CommRingCat.ofHom χ)) = _
      rw [gam_comp, gam_uns, hs.2]
      rfl
    · apply gam_inj
      change gam (uns _ ≫ Spec.map (CommRingCat.ofHom (l i))) = _
      rw [gam_comp, gam_uns, hs.1 i]
      rfl
  · intro s m hm
    ext p
    have H := hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)
    change (m p : T ⟶ Spec (CommRingCat.of B)) = uns _
    apply gam_inj
    rw [gam_uns]
    refine H.unique ⟨fun i => ?_, ?_⟩ H.exists.choose_spec
    · have e : (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) =
          (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom (l i)) :=
        (types_congr_hom (hm (some i)) p).symm
      change _ = gam (s.π.app (some i) p)
      rw [e]
      exact (gam_comp _ _).symm
    · have e : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) =
          (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom χ) :=
        (types_congr_hom (hm none) p).symm
      rw [e]
      exact (gam_comp _ _).symm

end LateralTheory.E.SpecLimPf
