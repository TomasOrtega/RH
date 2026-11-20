import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb.LX

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {N : ℕ}

/- English proof (translation)
Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hx : z x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f` using `h (Set.mem_univ x)`. Rewrite `hx` using `[← Proj.opensRange_awayι _ f hf hd]`. Conclude with `hx`.
-/
theorem range_sub_awayι {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    Set.range z ⊆ Set.range (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd) := by
  rintro _ ⟨x, rfl⟩
  have hx : z x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f := h (Set.mem_univ x)
  rw [← Proj.opensRange_awayι _ f hf hd] at hx
  exact hx

def liftA {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f →+* A :=
  (Spec.preimage (IsOpenImmersion.lift (Proj.awayι _ f hf hd) z (range_sub_awayι z hf hd h))).hom

/- English proof (translation)
Unfold `liftA`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]`.
-/
theorem liftA_spec {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z := by
  unfold liftA
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

/- English proof (translation)
Establish `h1 : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (liftA z hf hd h))`. Rewrite using `[← cancel_mono (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd), hφ, liftA_spec]`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`.
-/
theorem liftA_unique {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f)
    (φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f →+* A)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι _ f hf hd = z) : φ = liftA z hf hd h := by
  have h1 : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (liftA z hf hd h)) := by
    rw [← cancel_mono (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd), hφ, liftA_spec]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

/- English proof (translation)
Use `symm`. Apply `liftA_unique` to reduce the goal to its premises. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, liftA_spec]`.
-/
theorem liftA_comp {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A') (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom ρ) ≫ z) ⁻¹ᵁ Proj.basicOpen _ f) :
    liftA (Spec.map (CommRingCat.ofHom ρ) ≫ z) hf hd h' = ρ.comp (liftA z hf hd h) := by
  symm
  apply liftA_unique
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, liftA_spec]

/- English proof (translation)
Apply `liftA_unique` to reduce the goal to its premises. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]`. Conclude with `liftA_spec z hxd hdd h'`.
-/
theorem liftA_awayMap {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K} {d d' : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d') (hx : x = f * g)
    (hxd : x ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (d + d')) (hdd : 0 < d + d')
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ x) :
    (liftA z hxd hdd h').comp (HomogeneousLocalization.awayMap _ hg hx) = liftA z hf hd h := by
  apply liftA_unique
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]
  exact liftA_spec z hxd hdd h'

/- English proof (translation)
Take `⟨w, hw⟩ : ∃ w, w = Spec.map φ ≫ (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd).inv` from `⟨_, rfl⟩`. Establish `e1 : Spec.map φ ≫ Proj.awayι _ f hf hd = w ≫ (Proj.basicOpen _ f).ι`. Rewrite using `[hw, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]`. Establish `e2 : w ≫ Proj.basicOpenToSpec _ f = Spec.map φ`. Rewrite using `[hw, ← Proj.basicOpenIsoSpec_hom _ f hf hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]`.

Establish `e3 : ∀ (z : Spec A ⟶ PSpace K N) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hz : z = w ≫ (Proj.basicOpen _ f).ι), z.appLE (Proj.basicOpen _ f) ⊤ h = (Proj.basicOpen _ f).topIso.inv ≫ w.appTop`. Introduce `z h hz`. Substitute `hz` using the available equality. Rewrite using `[← Scheme.Hom.appLE_comp_appLE w _ _ ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]`. Use `congr 1`.

Rewrite using `[e3 _ h e1]`. Establish `e4` using `Scheme.ΓSpecIso_naturality φ`. Rewrite `e4` using `[← e2, Scheme.Hom.comp_appTop]`. Establish `e5` using `Proj.basicOpenToSpec_app_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f`. Express the relevant statement in the definitionally equal form `(Proj.basicOpenToSpec _ f).appTop = _ at e5`.

Rewrite `e4` using `[e5]`. Simplify using `only [Category.assoc] at e4`. Simplify `(cancel_epi _).1 e4` using `only [Category.assoc]`.
-/
theorem awayToSection_appLE {A : CommRingCat.{0}}
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d)
    (φ : CommRingCat.of (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) ⟶ A)
    (h : ⊤ ≤ (Spec.map φ ≫ Proj.awayι _ f hf hd) ⁻¹ᵁ Proj.basicOpen _ f) :
    Proj.awayToSection _ f ≫ (Spec.map φ ≫ Proj.awayι _ f hf hd).appLE (Proj.basicOpen _ f) ⊤ h ≫
      (Scheme.ΓSpecIso A).hom = φ := by
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.map φ ≫
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd).inv := ⟨_, rfl⟩
  have e1 : Spec.map φ ≫ Proj.awayι _ f hf hd = w ≫ (Proj.basicOpen _ f).ι := by
    rw [hw, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have e2 : w ≫ Proj.basicOpenToSpec _ f = Spec.map φ := by
    rw [hw, ← Proj.basicOpenIsoSpec_hom _ f hf hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have e3 : ∀ (z : Spec A ⟶ PSpace K N) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hz : z = w ≫ (Proj.basicOpen _ f).ι),
      z.appLE (Proj.basicOpen _ f) ⊤ h = (Proj.basicOpen _ f).topIso.inv ≫ w.appTop := by
    intro z h hz
    subst hz
    rw [← Scheme.Hom.appLE_comp_appLE w _ _ ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [e3 _ h e1]
  have e4 := Scheme.ΓSpecIso_naturality φ
  rw [← e2, Scheme.Hom.comp_appTop] at e4
  have e5 := Proj.basicOpenToSpec_app_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f
  change (Proj.basicOpenToSpec _ f).appTop = _ at e5
  rw [e5] at e4
  simp only [Category.assoc] at e4
  simpa only [Category.assoc] using (cancel_epi _).1 e4

/- English proof (translation)
Establish `key : ∀ (z' : Spec (CommRingCat.of A) ⟶ PSpace K N) (h' : ⊤ ≤ z' ⁻¹ᵁ Proj.basicOpen _ f) (hz : Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z'), Proj.awayToSection _ f ≫ z'.appLE (Proj.basicOpen _ f) ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom = Com …`. Introduce `z' h' hz`. Substitute `hz` using the available equality. Conclude with `awayToSection_appLE hf hd _ h'`. Conclude with `congrArg (fun ψ => CommRingCat.Hom.hom ψ a) (key z h (liftA_spec z hf hd h))`.
-/
theorem liftA_eval {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    GlobalTheory.Cris.evalAt z (Proj.basicOpen _ f) h ((Proj.awayToSection _ f).hom a) = liftA z hf hd h a := by
  have key : ∀ (z' : Spec (CommRingCat.of A) ⟶ PSpace K N) (h' : ⊤ ≤ z' ⁻¹ᵁ Proj.basicOpen _ f)
      (hz : Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z'),
      Proj.awayToSection _ f ≫ z'.appLE (Proj.basicOpen _ f) ⊤ h' ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom (liftA z hf hd h) := by
    intro z' h' hz
    subst hz
    exact awayToSection_appLE hf hd _ h'
  exact congrArg (fun ψ => CommRingCat.Hom.hom ψ a) (key z h (liftA_spec z hf hd h))

/- English proof (translation)
Rewrite using `[Proj.basicOpen_mul]`. Introduce `p hp`. Conclude with `⟨hf hp, hg hp⟩`.
-/
theorem le_basicOpen_mul {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g : MvPolynomial (Fin (N + 1)) K}
    (hf : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hg : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ g) :
    ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (f * g) := by
  rw [Proj.basicOpen_mul]
  intro p hp
  exact ⟨hf hp, hg hp⟩

/- English proof (translation)
Rewrite using `[← liftA_eval]`. Establish `e : Proj.awayToSection _ f ≫ z.appLE (Proj.basicOpen _ f) ⊤ h = CommRingCat.ofHom (HomogeneousLocalization.awayMap _ hg hx) ≫ Proj.awayToSection _ x ≫ z.appLE (Proj.basicOpen _ x) ⊤ h'`. Rewrite using `[← Category.assoc, Proj.awayMap_awayToSection, Category.assoc, Scheme.Hom.map_appLE]`. Conclude with `congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (CommRingCat.Hom.hom ψ a)) e`.
-/
theorem liftA_eval_mul {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K} {d' n : ℕ}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d') (hx : x = f * g)
    (hxd : x ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K n) (hn : 0 < n)
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ x)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    GlobalTheory.Cris.evalAt z (Proj.basicOpen _ f) h ((Proj.awayToSection _ f).hom a) =
      liftA z hxd hn h' (HomogeneousLocalization.awayMap _ hg hx a) := by
  rw [← liftA_eval]
  have e : Proj.awayToSection _ f ≫ z.appLE (Proj.basicOpen _ f) ⊤ h =
      CommRingCat.ofHom (HomogeneousLocalization.awayMap _ hg hx) ≫ Proj.awayToSection _ x ≫
        z.appLE (Proj.basicOpen _ x) ⊤ h' := by
    rw [← Category.assoc, Proj.awayMap_awayToSection, Category.assoc, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (CommRingCat.Hom.hom ψ a)) e

def yx {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1))
    (k : Fin m) : ChartR K N j :=
  HomogeneousLocalization.Away.mk _ (X_mem K N j) e (y k)
    (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k))

/- English proof (translation)
Establish `hyk` using `(MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)`. Establish `hxd : MvPolynomial.X j * y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e)` using `SetLike.mul_mem_graded (X_mem K N j) hyk`. Establish `hx` using `le_basicOpen_mul z hj hk`. Rewrite using `[← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx, RingHom.comp_apply]`. Apply `IsUnit.map` to reduce the goal to its premises.

Establish `hX : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K) ^ (1 + e) ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • (1 + e))`. Simplify using `using SetLike.pow_mem_graded (1 + e) (X_mem K N j)`. Use `IsUnit.of_mul_eq_one (HomogeneousLocalization.Away.mk _ hxd 1 _ hX) ?_` and prove the remaining obligations. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Unfold `yx`.

Rewrite using `[HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff]`. Apply `Localization.r_of_eq` to reduce the goal to its premises. Simplify using `only [Submonoid.coe_mul, Submonoid.coe_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem liftA_yx_isUnit {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1)) (k : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hk : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (y k)) :
    IsUnit (liftA z (X_mem K N j) one_pos hj (yx y hy j k)) := by
  have hyk := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have hxd : MvPolynomial.X j * y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e) :=
    SetLike.mul_mem_graded (X_mem K N j) hyk
  have hx := le_basicOpen_mul z hj hk
  rw [← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx, RingHom.comp_apply]
  apply IsUnit.map
  have hX : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K) ^ (1 + e) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • (1 + e)) := by
    simpa using SetLike.pow_mem_graded (1 + e) (X_mem K N j)
  refine IsUnit.of_mul_eq_one (HomogeneousLocalization.Away.mk _ hxd 1 _ hX) ?_
  apply HomogeneousLocalization.val_injective
  unfold yx
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, Submonoid.coe_one]
  ring

/- English proof (translation)
Establish `hxd : (MvPolynomial.X j * MvPolynomial.X j' : MvPolynomial (Fin (N + 1)) K) ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + 1)` using `SetLike.mul_mem_graded (X_mem K N j) (X_mem K N j')`. Establish `hx` using `le_basicOpen_mul z hj hj'`. Rewrite using `[← liftA_awayMap z (X_mem K N j) one_pos (X_mem K N j') rfl hxd (by omega) hj hx, ← liftA_awayMap z (X_mem K N j') one_pos (X_mem K N j) (mul_comm _ _) hxd (by omega) hj' hx]`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← map_pow, ← map_mul]`.

Use `congr 1`. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Unfold `yx ratio`. Rewrite using `[HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.va …`. Apply `Localization.r_of_eq` to reduce the goal to its premises.

Simplify using `only [Submonoid.coe_mul, SubmonoidClass.coe_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem liftA_yx_change {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j j' : Fin (N + 1)) (k : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hj' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j')) :
    liftA z (X_mem K N j) one_pos hj (yx y hy j k) =
      liftA z (X_mem K N j') one_pos hj' (yx y hy j' k) * liftA z (X_mem K N j) one_pos hj (ratio K N j j') ^ e := by
  have hxd : (MvPolynomial.X j * MvPolynomial.X j' : MvPolynomial (Fin (N + 1)) K) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + 1) :=
    SetLike.mul_mem_graded (X_mem K N j) (X_mem K N j')
  have hx := le_basicOpen_mul z hj hj'
  rw [← liftA_awayMap z (X_mem K N j) one_pos (X_mem K N j') rfl hxd (by omega) hj hx,
    ← liftA_awayMap z (X_mem K N j') one_pos (X_mem K N j) (mul_comm _ _) hxd (by omega) hj' hx]
  simp only [RingHom.comp_apply]
  rw [← map_pow, ← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  unfold yx ratio
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

/- English proof (translation)
Establish `hyk` using `(MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')`. Establish `hxd : MvPolynomial.X j * y k' ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e)` using `SetLike.mul_mem_graded (X_mem K N j) hyk`. Establish `hx` using `le_basicOpen_mul z hj hk'`. Rewrite using `[liftA_eval_mul z (X_mem K N j) (mul_comm _ _) hxd (by omega) hk' hx, ← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx]`. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[← map_mul]`. Use `congr 1`. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Unfold `yx`. Rewrite using `[HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, Localization.mk_mul, Locali …`.

Apply `Localization.r_of_eq` to reduce the goal to its premises. Simplify using `only [Submonoid.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem liftA_yx_quot {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1)) (k k' : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hk' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (y k')) :
    liftA z (X_mem K N j) one_pos hj (yx y hy j k) =
      liftA z (X_mem K N j) one_pos hj (yx y hy j k') *
        GlobalTheory.Cris.evalAt z (Proj.basicOpen _ (y k')) hk'
          ((Proj.awayToSection _ (y k')).hom
            (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')) 1 (y k)
              (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)))) := by
  have hyk := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hxd : MvPolynomial.X j * y k' ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e) :=
    SetLike.mul_mem_graded (X_mem K N j) hyk
  have hx := le_basicOpen_mul z hj hk'
  rw [liftA_eval_mul z (X_mem K N j) (mul_comm _ _) hxd (by omega) hk' hx,
    ← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx]
  simp only [RingHom.comp_apply]
  rw [← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  unfold yx
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul]
  ring

end CrystallineSemistableComparison.Pb.LX
