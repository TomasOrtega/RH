import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

section

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of R)) [Algebra R Γ(X, ⊤)]

/- English proof (translation)
Rewrite using `[← GlobalTheory.map_restrictGlobal (homOfLE (le_top : W ≤ ⊤)) (algebraMap R Γ(X, ⊤) r), GlobalTheory.restrictGlobal_top, hs]`. Both sides reduce to the same expression.
-/
theorem secMap_eq_restrictGlobal
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    (W : X.Opens) (r : R) :
    (GlobalTheory.CechDR.secMap s W).hom r = GlobalTheory.restrictGlobal X W (algebraMap R Γ(X, ⊤) r) := by
  rw [← GlobalTheory.map_restrictGlobal (homOfLE (le_top : W ≤ ⊤)) (algebraMap R Γ(X, ⊤) r),
    GlobalTheory.restrictGlobal_top, hs]
  rfl

def secRes (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W ≤ U) : GlobalTheory.CechDR.Sec s U →ₗ[R] GlobalTheory.sectionsOn (GlobalTheory.structureModule X) W where
  toFun x := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (X.presheaf.map (homOfLE h).op (x : Γ(X, U)))
  map_add' x y := map_add (X.presheaf.map (homOfLE h).op).hom (x : Γ(X, U)) (y : Γ(X, U))
  map_smul' r x := by
    apply (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective
    rw [RingHom.id_apply, GlobalTheory.sectionsOn.toΓ_smul, ← secMap_eq_restrictGlobal s hs W r]
    have e : (GlobalTheory.CechDR.secMap s W).hom r =
        X.presheaf.map (homOfLE h).op ((GlobalTheory.CechDR.secMap s U).hom r) :=
      (congrArg (fun q ↦ q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (s.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)).symm
    have key : ∀ y : Γ(X, U), X.presheaf.map (homOfLE h).op ((GlobalTheory.CechDR.secMap s U).hom r * y) =
        (GlobalTheory.CechDR.secMap s W).hom r * X.presheaf.map (homOfLE h).op y := fun y ↦ by
      rw [e]
      exact map_mul (X.presheaf.map (homOfLE h).op).hom _ y
    exact key x

/- English proof (translation)
The claim follows from `AddEquiv.apply_symm_apply _ _`.
-/
private theorem sectionsOn_toΓ_secRes_eq_presheaf_map
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W ≤ U) (x : GlobalTheory.CechDR.Sec s U) :
    GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W (secRes s hs h x) =
      X.presheaf.map (homOfLE h).op (x : Γ(X, U)) :=
  AddEquiv.apply_symm_apply _ _

/- English proof (translation)
Substitute `h` using the available equality. Establish `key : ∀ x : GlobalTheory.CechDR.Sec s W, secRes s hs (le_refl W) x = (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (x : Γ(X, W))`. Introduce `x`. Establish `hx : X.presheaf.map (homOfLE (le_refl W)).op (x : Γ(X, W)) = (x : Γ(X, W))`. Express the relevant statement in the definitionally equal form `(X.presheaf.map (𝟙 (op W))) (x : Γ(X, W)) = x`.

Rewrite using `[X.presheaf.map_id]`. Both sides reduce to the same expression. Conclude with `congrArg (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm hx`. Use `⟨fun x y hxy => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite `hxy` using `[key, key]`.

Conclude with `(GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm.injective hxy`. Use `⟨(show GlobalTheory.CechDR.Sec s W from GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W y), ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Conclude with `(GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm_apply_apply y`.
-/
theorem secRes_bijective
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W = U) : Function.Bijective (secRes s hs h.le) := by
  subst h
  have key : ∀ x : GlobalTheory.CechDR.Sec s W, secRes s hs (le_refl W) x =
      (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (x : Γ(X, W)) := by
    intro x
    have hx : X.presheaf.map (homOfLE (le_refl W)).op (x : Γ(X, W)) = (x : Γ(X, W)) := by
      change (X.presheaf.map (𝟙 (op W))) (x : Γ(X, W)) = x
      rw [X.presheaf.map_id]
      rfl
    exact congrArg (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm hx
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · rw [key, key] at hxy
    exact (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm.injective hxy
  · refine ⟨(show GlobalTheory.CechDR.Sec s W from GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W y), ?_⟩
    rw [key]
    exact (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm_apply_apply y

/- English proof (translation)
The claim follows from `GlobalTheory.WithAction.toBase_linearMap _ _ R _ _ y`.
-/
private theorem sectionsOn_toΓ_res_eq_presheaf_map {U V : X.Opens} (h : V ≤ U)
    (y : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) U) :
    GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) V (GlobalTheory.sectionsOn.res R (GlobalTheory.structureModule X) h y) =
      (GlobalTheory.structureModule X).presheaf.map (homOfLE h).op (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) U y) :=
  GlobalTheory.WithAction.toBase_linearMap _ _ R _ _ y

/- English proof (translation)
Apply `(GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective` to reduce the goal to its premises. Rewrite using `[sectionsOn_toΓ_secRes_eq_presheaf_map, sectionsOn_toΓ_res_eq_presheaf_map, sectionsOn_toΓ_secRes_eq_presheaf_map]`. Express the relevant statement in the definitionally equal form `(X.presheaf.map (homOfLE b).op) ((X.presheaf.map (homOfLE a).op) (x : Γ(X, U))) = (X.presheaf.map (homOfLE d).op) ((X.presheaf.map (homOfLE c).op) (x : Γ(X, U)))`. Establish `h1 : X.presheaf.map (homOfLE a).op ≫ X.presheaf.map (homOfLE b).op = X.presheaf.map (homOfLE c).op ≫ X.presheaf.map (homOfLE d).op`. Rewrite using `[← Functor.map_comp, ← Functor.map_comp]`.

Both sides reduce to the same expression. Conclude with `congrArg (fun f : X.presheaf.obj (op U) ⟶ X.presheaf.obj (op W) => f (x : Γ(X, U))) h1`.
-/
theorem secRes_square
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U V V' W : X.Opens} (a : V ≤ U) (b : W ≤ V) (c : V' ≤ U) (d : W ≤ V') (x : GlobalTheory.CechDR.Sec s U) :
    secRes s hs b (GlobalTheory.CechDR.Sec.res s a x) =
      GlobalTheory.sectionsOn.res R (GlobalTheory.structureModule X) d (secRes s hs c x) := by
  apply (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective
  rw [sectionsOn_toΓ_secRes_eq_presheaf_map, sectionsOn_toΓ_res_eq_presheaf_map, sectionsOn_toΓ_secRes_eq_presheaf_map]
  change (X.presheaf.map (homOfLE b).op) ((X.presheaf.map (homOfLE a).op) (x : Γ(X, U))) =
    (X.presheaf.map (homOfLE d).op) ((X.presheaf.map (homOfLE c).op) (x : Γ(X, U)))
  have h1 : X.presheaf.map (homOfLE a).op ≫ X.presheaf.map (homOfLE b).op =
      X.presheaf.map (homOfLE c).op ≫ X.presheaf.map (homOfLE d).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (fun f : X.presheaf.obj (op U) ⟶ X.presheaf.obj (op W) => f (x : Γ(X, U))) h1

end

section

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of R)) [Algebra R Γ(X, ⊤)]
  {P : Type} [SemilatticeInf P] (S : MainStatements.Hodge.Sys X P) {κ : Type} (e : κ → P)

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => exact absurd ht Finset.not_nonempty_empty`. Consider the case `insert a s ha ih`. Distinguish the cases in `hs : s.Nonempty`. Rewrite using `[Finset.inf'_insert hs, S.map_inf, ih hs, Finset.iInf_insert]`.

Simplify using `only [top_inf_eq]`. Take `rfl : s = ∅` from `Finset.not_nonempty_iff_eq_empty.mp hs`. Simplify using the standard rewrite rules.
-/
theorem sys_inf' (t : Finset κ) (ht : t.Nonempty) :
    (S.u (t.inf' ht e)).1 = ⊤ ⊓ ⨅ i ∈ t, (S.u (e i)).1 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · rw [Finset.inf'_insert hs, S.map_inf, ih hs, Finset.iInf_insert]
      simp only [top_inf_eq]
    · obtain rfl : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp

variable (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))

def sysVertex (t : Finset κ) :
    (cubeOf e (toMod (MainStatements.Hodge.OSys s S))).obj t →ₗ[R]
      (GlobalTheory.cechCube R (GlobalTheory.structureModule X) ⊤ fun i ↦ (S.u (e i)).1).obj t :=
  if ht : t.Nonempty then
    (secRes s hs (sys_inf' S e t ht).ge) ∘ₗ
      LinearMap.proj (R := R) (φ := fun h : PLift t.Nonempty ↦
        ((toMod (MainStatements.Hodge.OSys s S)).obj (op (t.inf' h.down e)) : Type)) ⟨ht⟩
  else 0

/- English proof (translation)
Unfold `sysVertex`. Rewrite using `[dif_pos ht]`. Both sides reduce to the same expression.
-/
theorem sysVertex_apply (t : Finset κ) (ht : t.Nonempty) (x : (cubeOf e (toMod (MainStatements.Hodge.OSys s S))).obj t) :
    sysVertex s S e hs t x = secRes s hs (sys_inf' S e t ht).ge (x ⟨ht⟩) := by
  unfold sysVertex
  rw [dif_pos ht]
  rfl

/- English proof (translation)
Unfold `sysVertex`. Rewrite using `[dif_neg ht]`.
-/
theorem sysVertex_of_not_nonempty (t : Finset κ) (ht : ¬ t.Nonempty) : sysVertex s S e hs t = 0 := by
  unfold sysVertex
  rw [dif_neg ht]

/- English proof (translation)
Establish `hf : ⇑(sysVertex s S e hs t) = (secRes s hs (sys_inf' S e t ht).ge) ∘ (fun x => x ⟨ht⟩)`. Use function extensionality and compare the values at `fun x => sysVertex_apply s S e hs t ht x`. Rewrite using `[hf]`. Use `(secRes_bijective s hs (sys_inf' S e t ht).symm).comp ⟨fun x y hxy => ?_, fun y => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `h`.

Take `⟨h⟩` from `h`. Conclude with `hxy`. Conclude with `⟨fun _ => y, rfl⟩`.
-/
theorem sysVertex_bijective (t : Finset κ) (ht : t.Nonempty) : Function.Bijective (sysVertex s S e hs t) := by
  have hf : ⇑(sysVertex s S e hs t) = (secRes s hs (sys_inf' S e t ht).ge) ∘ (fun x => x ⟨ht⟩) :=
    funext fun x => sysVertex_apply s S e hs t ht x
  rw [hf]
  refine (secRes_bijective s hs (sys_inf' S e t ht).symm).comp ⟨fun x y hxy => ?_, fun y => ?_⟩
  · funext h
    obtain ⟨h⟩ := h
    exact hxy
  · exact ⟨fun _ => y, rfl⟩

def sysCube : cubeOf e (toMod (MainStatements.Hodge.OSys s S)) ⟶
    GlobalTheory.cechCube R (GlobalTheory.structureModule X) ⊤ fun i ↦ (S.u (e i)).1 :=
  GlobalTheory.Cube.homMk (sysVertex s S e hs) fun {t t'} h x ↦ by
    by_cases ht : t.Nonempty
    · have ht' : t'.Nonempty := ht.mono h
      rw [sysVertex_apply s S e hs t' ht', sysVertex_apply s S e hs t ht]
      have e1 := cubeRes_apply e (toMod (MainStatements.Hodge.OSys s S)) h x ht ⟨ht'⟩
      refine (congrArg (secRes s hs (sys_inf' S e t' ht').ge) e1).trans ?_
      exact secRes_square s hs _ _ _ _ (x ⟨ht⟩)
    · rw [sysVertex_of_not_nonempty s S e hs t ht, LinearMap.zero_apply, map_zero]
      by_cases ht' : t'.Nonempty
      · rw [sysVertex_apply s S e hs t' ht']
        have e1 := cubeRes_empty e (toMod (MainStatements.Hodge.OSys s S)) h x ht ⟨ht'⟩
        exact (congrArg (secRes s hs (sys_inf' S e t' ht').ge) e1).trans (map_zero _)
      · rw [sysVertex_of_not_nonempty s S e hs t' ht', LinearMap.zero_apply]

/- English proof (translation)
Apply `GlobalTheory.isIso_cechComplexMap` to reduce the goal to its premises. Introduce `t ht`. Rewrite using `[sysCube, GlobalTheory.Cube.homMk_app, ModuleCat.hom_ofHom]`. Conclude with `sysVertex_bijective s S e hs t ht`.
-/
theorem isIso_sysCube [LinearOrder κ] : IsIso (GlobalTheory.cechComplexMap (sysCube s S e hs)) := by
  apply GlobalTheory.isIso_cechComplexMap
  intro t ht
  rw [sysCube, GlobalTheory.Cube.homMk_app, ModuleCat.hom_ofHom]
  exact sysVertex_bijective s S e hs t ht

end

/- English proof (translation)
Introduce `R _ X s P _ S κ _ e n`. Use `letI := GlobalTheory.algebraΓOfHom s`. Establish `hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)` using `fun r => rfl`. Use `haveI := isIso_sysCube s S e hs`. Conclude with `⟨((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso (asIso (GlobalTheory.cechComplexMap (sysCube s S e hs)))).toLinearEquiv⟩`.
-/
theorem cech_OSys_homology_equiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) := by
  intro R _ X s P _ S κ _ e n
  letI := GlobalTheory.algebraΓOfHom s
  have hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) :=
    fun r => rfl
  haveI := isIso_sysCube s S e hs
  exact ⟨((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (asIso (GlobalTheory.cechComplexMap (sysCube s S e hs)))).toLinearEquiv⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve
