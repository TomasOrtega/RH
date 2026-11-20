import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory

namespace TopForm

open LB

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}

/- English proof (translation)
Set `_ : Algebra k A` to `α.toAlgebra`. Use `set I := Ideal.span (Set.range f) with hI`. Establish `_ : Algebra.FormallyUnramified k (A ⧸ I)` using `RingHom.formallyUnramified_algebraMap.1 hu`. Establish `hsurj : Function.Surjective (algebraMap A (A ⧸ I))` using `Ideal.Quotient.mk_surjective`. Set `v : Fin D → TensorProduct A (A ⧸ I) Ω[A⁄k]` to `fun i => TensorProduct.tmul A (1 : A ⧸ I) (KaehlerDifferential.D k A (f i))`.

Set `S : Submodule (A ⧸ I) (TensorProduct A (A ⧸ I) Ω[A⁄k])` to `Submodule.span (A ⧸ I) (Set.range v)`. Establish `hmem : ∀ x ∈ I, TensorProduct.tmul A (1 : A ⧸ I) (KaehlerDifferential.D k A x) ∈ S`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨j, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, TensorProduct.tmul_add]`.

Conclude with `S.add_mem hx hy`. Consider the case `smul a x hx' hx`. Rewrite using `[smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul]`. Establish `h0 : x • (TensorProduct.tmul A (1 : A ⧸ I) (KaehlerDifferential.D k A a)) = 0`. Rewrite using `[TensorProduct.smul_tmul', Algebra.smul_def, mul_one, show algebraMap A (A ⧸ I) x = 0 from (Ideal.Quotient.eq_zero_iff_mem (I := I)).2 hx', TensorProduct.zero_tmul]`.

Rewrite using `[h0, add_zero]`. Conclude with `S.smul_of_tower_mem a hx`. Establish `hS : S = ⊤`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `(KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k A (A ⧸ I) hsurj z).1 (Subsingleton.elim _ _)`.

Take `⟨⟨x, hx⟩, rfl⟩` from `Ideal.toCotangent_surjective _ y`. Rewrite using `[KaehlerDifferential.kerCotangentToTensor_toCotangent]`. Conclude with `hmem x ((Ideal.Quotient.eq_zero_iff_mem (I := I)).1 (RingHom.mem_ker.1 hx))`. Establish `hW : Submodule.span (A ⧸ I) {exteriorPower.ιMulti (A ⧸ I) D v} = ⊤`. Rewrite using `[eq_top_iff, ← exteriorPower.ιMulti_span_of_span (R := A ⧸ I) (n := D) (M := TensorProduct A (A ⧸ I) Ω[A⁄k]) (s := Set.range v) hS, Submodule.span_le]`.

Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `choose σ hσ using fun i => ha ⟨i, rfl⟩`. Establish `ha' : a = v ∘ σ` using `funext fun i => (hσ i).symm`. Substitute `ha'` using the available equality. Distinguish the cases in `hinj : Function.Injective σ`.

Set `e` to `Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj)`. Establish `hp` using `(exteriorPower.ιMulti (A ⧸ I) D (M := TensorProduct A (A ⧸ I) Ω[A⁄k])).map_perm v e`. Express the relevant statement in the definitionally equal form `exteriorPower.ιMulti (A ⧸ I) D (v ∘ ⇑e) ∈ _`. Rewrite using `[hp, Units.smul_def]`. Conclude with `SetLike.mem_coe.2 (zsmul_mem (Submodule.mem_span_singleton_self _) _)`.

Establish `hn : ¬ Function.Injective (v ∘ σ)` using `fun h => hinj h.of_comp`. Rewrite using `[(exteriorPower.ιMulti (A ⧸ I) D).map_eq_zero_of_not_injective _ hn]`. Conclude with `SetLike.mem_coe.2 (Submodule.zero_mem _)`. Set `ψ` to `exteriorPowerMapOver (A ⧸ I) D (TensorProduct.mk A (A ⧸ I) Ω[A⁄k] 1)`. Establish `hgen : IsFreeGen (A ⧸ I) (ψ ω)` using `hω.of_isBaseChange (isBaseChange_exteriorPower (TensorProduct.isBaseChange A Ω[A⁄k] (A ⧸ I)) D)`.

Establish `hψJ : ψ (J • ω) = (Ideal.Quotient.mk I J) • ψ ω`. Rewrite using `[map_smul, ← algebraMap_smul (A ⧸ I) J (ψ ω)]`. Both sides reduce to the same expression. Establish `hψd : ψ (dForm α f) = exteriorPower.ιMulti (A ⧸ I) D v`. Rewrite using `[dForm_eq]`.

Conclude with `exteriorPowerMapOver_ιMulti (TensorProduct.mk A (A ⧸ I) Ω[A⁄k] 1) (fun i => dFun α (f i))`. Establish `hmemω : ψ ω ∈ Submodule.span (A ⧸ I) {exteriorPower.ιMulti (A ⧸ I) D v}` using `hW ▸ Submodule.mem_top`. Take `⟨c, hcoef⟩` from `Submodule.mem_span_singleton.1 hmemω`. Rewrite `hcoef` using `[← hψd, ← hJ, hψJ, smul_smul]`. Establish `h1 : c * Ideal.Quotient.mk I J = 1` using `hgen.1 (hcoef.trans (one_smul _ _).symm)`.

Conclude with `isUnit_iff_exists_inv.2 ⟨c, by rw [mul_comm]; exact h1⟩`.
-/
theorem isUnit_mk_of_formallyUnramified {k A : Type*} [CommRing k] [CommRing A] {α : k →+* A}
    {D : ℕ} {ω : Forms α D} (hω : IsFreeGen A ω) (f : Fin D → A) {J : A} (hJ : J • ω = dForm α f)
    (hu : ((Ideal.Quotient.mk (Ideal.span (Set.range f))).comp α).FormallyUnramified) :
    IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range f)) J) := by
  classical
  let _ : Algebra k A := α.toAlgebra
  set I := Ideal.span (Set.range f) with hI
  have _ : Algebra.FormallyUnramified k (A ⧸ I) := RingHom.formallyUnramified_algebraMap.1 hu
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  let v : Fin D → TensorProduct A (A ⧸ I) Ω[A⁄k] := fun i => TensorProduct.tmul A (1 : A ⧸ I) (KaehlerDifferential.D k A (f i))
  let S : Submodule (A ⧸ I) (TensorProduct A (A ⧸ I) Ω[A⁄k]) := Submodule.span (A ⧸ I) (Set.range v)
  have hmem : ∀ x ∈ I, TensorProduct.tmul A (1 : A ⧸ I) (KaehlerDifferential.D k A x) ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, TensorProduct.tmul_add]
      exact S.add_mem hx hy
    | smul a x hx' hx =>
      rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul]
      have h0 : x • (TensorProduct.tmul A (1 : A ⧸ I) (KaehlerDifferential.D k A a)) = 0 := by
        rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
          show algebraMap A (A ⧸ I) x = 0 from (Ideal.Quotient.eq_zero_iff_mem (I := I)).2 hx', TensorProduct.zero_tmul]
      rw [h0, add_zero]
      exact S.smul_of_tower_mem a hx
  have hS : S = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k A (A ⧸ I) hsurj z).1
      (Subsingleton.elim _ _)
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    exact hmem x ((Ideal.Quotient.eq_zero_iff_mem (I := I)).1 (RingHom.mem_ker.1 hx))
  have hW : Submodule.span (A ⧸ I) {exteriorPower.ιMulti (A ⧸ I) D v} = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span (R := A ⧸ I) (n := D) (M := TensorProduct A (A ⧸ I) Ω[A⁄k]) (s := Set.range v) hS,
      Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    choose σ hσ using fun i => ha ⟨i, rfl⟩
    have ha' : a = v ∘ σ := funext fun i => (hσ i).symm
    subst ha'
    by_cases hinj : Function.Injective σ
    · let e := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj)
      have hp := (exteriorPower.ιMulti (A ⧸ I) D (M := TensorProduct A (A ⧸ I) Ω[A⁄k])).map_perm v e
      change exteriorPower.ιMulti (A ⧸ I) D (v ∘ ⇑e) ∈ _
      rw [hp, Units.smul_def]
      exact SetLike.mem_coe.2 (zsmul_mem (Submodule.mem_span_singleton_self _) _)
    · have hn : ¬ Function.Injective (v ∘ σ) := fun h => hinj h.of_comp
      rw [(exteriorPower.ιMulti (A ⧸ I) D).map_eq_zero_of_not_injective _ hn]
      exact SetLike.mem_coe.2 (Submodule.zero_mem _)
  let ψ := exteriorPowerMapOver (A ⧸ I) D (TensorProduct.mk A (A ⧸ I) Ω[A⁄k] 1)
  have hgen : IsFreeGen (A ⧸ I) (ψ ω) :=
    hω.of_isBaseChange (isBaseChange_exteriorPower (TensorProduct.isBaseChange A Ω[A⁄k] (A ⧸ I)) D)
  have hψJ : ψ (J • ω) = (Ideal.Quotient.mk I J) • ψ ω := by
    rw [map_smul, ← algebraMap_smul (A ⧸ I) J (ψ ω)]
    rfl
  have hψd : ψ (dForm α f) = exteriorPower.ιMulti (A ⧸ I) D v := by
    rw [dForm_eq]
    exact exteriorPowerMapOver_ιMulti (TensorProduct.mk A (A ⧸ I) Ω[A⁄k] 1) (fun i => dFun α (f i))
  have hmemω : ψ ω ∈ Submodule.span (A ⧸ I) {exteriorPower.ιMulti (A ⧸ I) D v} := hW ▸ Submodule.mem_top
  obtain ⟨c, hcoef⟩ := Submodule.mem_span_singleton.1 hmemω
  rw [← hψd, ← hJ, hψJ, smul_smul] at hcoef
  have h1 : c * Ideal.Quotient.mk I J = 1 := hgen.1 (hcoef.trans (one_smul _ _).symm)
  exact isUnit_iff_exists_inv.2 ⟨c, by rw [mul_comm]; exact h1⟩

variable (p) in

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [algX, RingHom.comp_apply, resG]`. Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp]`. Conclude with `congrArg (fun φ : Γ(Sp k, ⊤) ⟶ Γ(Y, V) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) (Scheme.Hom.appLE_map p _ (homOfLE h).op)`.
-/
theorem resG_comp_algX {U V : Y.Opens} (h : V ≤ U) : (resG Y h).comp (algX p U) = algX p V := by
  ext a
  simp only [algX, RingHom.comp_apply, resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  exact congrArg (fun φ : Γ(Sp k, ⊤) ⟶ Γ(Y, V) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a))
    (Scheme.Hom.appLE_map p _ (homOfLE h).op)

variable (p D) in

abbrev FormsOn (U : Y.Opens) : Type := Forms (algX p U) D

variable (p) in

abbrev dOn {U : Y.Opens} (f : Fin D → Γ(Y, U)) : FormsOn p D U := dForm (algX p U) f

def resForm {U V : Y.Opens} (h : V ≤ U) : FormsOn p D U →ₛₗ[resG Y h] FormsOn p D V :=
  formMap D (resG Y h) (resG_comp_algX p h)

/- English proof (translation)
The claim follows from `formMap_dForm _ _ f`.
-/
@[simp] theorem resForm_dOn {U V : Y.Opens} (h : V ≤ U) (f : Fin D → Γ(Y, U)) :
    resForm h (dOn p f) = dOn p fun i => resG Y h (f i) := formMap_dForm _ _ f

/- English proof (translation)
The claim follows from `formMap_formMap (resG Y h₁) (resG Y h₂) (resG Y (h₂.trans h₁)) (by rw [resG, resG, resG, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl) (resG_comp_algX p h₁) (resG_comp_algX p h₂) (resG_comp_algX p _) η`.
-/
@[simp] theorem resForm_resForm {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (η : FormsOn p D U) :
    resForm h₂ (resForm h₁ η) = resForm (h₂.trans h₁) η := formMap_formMap (resG Y h₁) (resG Y h₂) (resG Y (h₂.trans h₁))
    (by rw [resG, resG, resG, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    (resG_comp_algX p h₁) (resG_comp_algX p h₂) (resG_comp_algX p _) η

/- English proof (translation)
Use `formMap_of_eq_id (resG Y h) ?_ (resG_comp_algX p h) η` and prove the remaining obligations. Use extensionality with `a`. Simplify using `[resG]`.
-/
@[simp] theorem resForm_self {U : Y.Opens} (h : U ≤ U) (η : FormsOn p D U) : resForm h η = η := by
  refine formMap_of_eq_id (resG Y h) ?_ (resG_comp_algX p h) η
  ext a
  simp [resG]

/- English proof (translation)
The claim follows from `LinearMap.map_smulₛₗ _ _ _`.
-/
theorem resForm_smul {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) (η : FormsOn p D U) :
    resForm h (a • η) = resG Y h a • resForm h η := LinearMap.map_smulₛₗ _ _ _

/- English proof (translation)
Use `Scheme.Hom.etale_appLE (𝟙 Y) hU hV (show V ≤ (𝟙 Y) ⁻¹ᵁ U from h)` as an intermediate fact. Simplify using `only [Scheme.Hom.appLE, Scheme.Hom.id_app] at this`. Conclude with `this`.
-/
theorem etale_resG {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    (resG Y h).Etale := by
  have := Scheme.Hom.etale_appLE (𝟙 Y) hU hV (show V ≤ (𝟙 Y) ⁻¹ᵁ U from h)
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at this
  exact this

/- English proof (translation)
Introduce `_ hx` and use `⟨h hx, h' hx⟩`.
-/
theorem le_preimage_inf {T : Scheme.{0}} {y : T ⟶ Y} {U U' : Y.Opens} {W : T.Opens}
    (h : W ≤ y ⁻¹ᵁ U) (h' : W ≤ y ⁻¹ᵁ U') : W ≤ y ⁻¹ᵁ (U ⊓ U') := fun _ hx => ⟨h hx, h' hx⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.2`. Conclude with `Opens.mem_iSup.2 ⟨⟨W, hW, hWV⟩, hxW⟩`.
-/
theorem le_iSup_affine (V : Y.Opens) :
    V ≤ ⨆ W : {W : Y.Opens // IsAffineOpen W ∧ W ≤ V}, W.1 := by
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWV⟩, hxW⟩

/- English proof (translation)
The claim follows from `Y.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // IsAffineOpen W ∧ W ≤ V} => W.1) V (fun W => homOfLE W.2.2) (le_iSup_affine V) a b fun W => h W.1 W.2.1 W.2.2`.
-/
theorem fun_ext_affine {V : Y.Opens} {a b : Γ(Y, V)}
    (h : ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ V, resG Y hW a = resG Y hW b) : a = b := Y.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // IsAffineOpen W ∧ W ≤ V} => W.1) V
    (fun W => homOfLE W.2.2) (le_iSup_affine V) a b fun W => h W.1 W.2.1 W.2.2

structure IsFrame {U : Y.Opens} (ω : FormsOn p D U) : Prop where

  affine : IsAffineOpen U

  gen : IsFreeGen Γ(Y, U) ω

namespace IsFrame

variable {U U' U'' V W : Y.Opens} {ω : FormsOn p D U} {ω' : FormsOn p D U'} {ω'' : FormsOn p D U''}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hW, IsFreeGen.formMap (etale_resG hω.affine hW h) _ hω.gen⟩`.
-/
theorem res (hω : IsFrame ω) (hW : IsAffineOpen W) (h : W ≤ U) : IsFrame (resForm h ω) := ⟨hW, IsFreeGen.formMap (etale_resG hω.affine hW h) _ hω.gen⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Y.presheaf.map (homOfLE h).op ≫ Y.presheaf.map (homOfLE h').op).hom a = _`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression.
-/
private theorem resG_resG_divisors {U V W : Y.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(Y, U)) :
    resG Y h' (resG Y h a) = resG Y (h'.trans h) a := by
  change (Y.presheaf.map (homOfLE h).op ≫ Y.presheaf.map (homOfLE h').op).hom a = _
  rw [← Functor.map_comp]
  rfl

/- English proof (translation)
Set `I` to `{W : Y.Opens // IsAffineOpen W ∧ W ≤ V}`. Set `sf : ∀ W : I, Γ(Y, W.1)` to `fun W => (hω.res W.2.1 (W.2.2.trans h)).gen.repr (resForm W.2.2 η)`. Establish `hsf : ∀ W : I, sf W • resForm (W.2.2.trans h) ω = resForm W.2.2 η` using `fun W => (hω.res W.2.1 (W.2.2.trans h)).gen.repr_smul _`. Establish `key : ∀ (W : I) (W' : Y.Opens) (e : W' ≤ W.1), resG Y e (sf W) • resForm ((e.trans W.2.2).trans h) ω = resForm (e.trans W.2.2) η`. Introduce `W W' e`.

Rewrite using `[← resForm_resForm W.2.2 e, ← hsf W, resForm_smul, resForm_resForm]`. Take `⟨c, hc, -⟩` from `Y.sheaf.existsUnique_gluing' (fun W : I => W.1) V (fun W => homOfLE W.2.2) (le_iSup_affine V) sf (by`. Introduce `W₁ W₂`. Use `fun_ext_affine fun W' hW' e => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resG Y e (resG Y inf_le_left (sf W₁)) = resG Y e (resG Y inf_le_right (sf W₂))`.

Rewrite using `[resG_resG_divisors, resG_resG_divisors]`. Conclude with `(hω.res hW' _).gen.1 ((key W₁ W' (e.trans inf_le_left)).trans (key W₂ W' (e.trans inf_le_right)).symm))`. Use `⟨c, fun W hW e => ?_⟩` and prove the remaining obligations. Rewrite using `[show resG Y e c = sf ⟨W, hW, e⟩ from hc ⟨W, hW, e⟩]`. Conclude with `(hsf ⟨W, hW, e⟩).symm`.
-/
theorem exists_coeff (hω : IsFrame ω) (h : V ≤ U) (η : FormsOn p D V) :
    ∃ c : Γ(Y, V), ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ V,
      resForm hW η = resG Y hW c • resForm (hW.trans h) ω := by
  let I := {W : Y.Opens // IsAffineOpen W ∧ W ≤ V}
  let sf : ∀ W : I, Γ(Y, W.1) := fun W => (hω.res W.2.1 (W.2.2.trans h)).gen.repr (resForm W.2.2 η)
  have hsf : ∀ W : I, sf W • resForm (W.2.2.trans h) ω = resForm W.2.2 η := fun W =>
    (hω.res W.2.1 (W.2.2.trans h)).gen.repr_smul _
  have key : ∀ (W : I) (W' : Y.Opens) (e : W' ≤ W.1),
      resG Y e (sf W) • resForm ((e.trans W.2.2).trans h) ω = resForm (e.trans W.2.2) η := by
    intro W W' e
    rw [← resForm_resForm W.2.2 e, ← hsf W, resForm_smul, resForm_resForm]
  obtain ⟨c, hc, -⟩ := Y.sheaf.existsUnique_gluing' (fun W : I => W.1) V (fun W => homOfLE W.2.2)
    (le_iSup_affine V) sf (by
      intro W₁ W₂
      refine fun_ext_affine fun W' hW' e => ?_
      change resG Y e (resG Y inf_le_left (sf W₁)) = resG Y e (resG Y inf_le_right (sf W₂))
      rw [resG_resG_divisors, resG_resG_divisors]
      exact (hω.res hW' _).gen.1 ((key W₁ W' (e.trans inf_le_left)).trans (key W₂ W' (e.trans inf_le_right)).symm))
  refine ⟨c, fun W hW e => ?_⟩
  rw [show resG Y e c = sf ⟨W, hW, e⟩ from hc ⟨W, hW, e⟩]
  exact (hsf ⟨W, hW, e⟩).symm

/- English proof (translation)
The claim follows from `fun_ext_affine fun W hW e => (hω.res hW (e.trans h)).gen.1 ((hc W hW e).symm.trans (hc' W hW e))`.
-/
theorem coeff_unique (hω : IsFrame ω) (h : V ≤ U) {η : FormsOn p D V} {c c' : Γ(Y, V)}
    (hc : ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ V,
      resForm hW η = resG Y hW c • resForm (hW.trans h) ω)
    (hc' : ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ V,
      resForm hW η = resG Y hW c' • resForm (hW.trans h) ω) : c = c' := fun_ext_affine fun W hW e => (hω.res hW (e.trans h)).gen.1 ((hc W hW e).symm.trans (hc' W hW e))

def coeff (hω : IsFrame ω) (h : V ≤ U) : FormsOn p D V →ₗ[Γ(Y, V)] Γ(Y, V) where
  toFun η := (hω.exists_coeff h η).choose
  map_add' η η' := hω.coeff_unique h (hω.exists_coeff h _).choose_spec fun W hW e => by
    rw [map_add, map_add, add_smul, ← (hω.exists_coeff h η).choose_spec W hW e,
      ← (hω.exists_coeff h η').choose_spec W hW e]
  map_smul' a η := hω.coeff_unique h (hω.exists_coeff h _).choose_spec fun W hW e => by
    rw [resForm_smul, RingHom.id_apply, smul_eq_mul, map_mul, mul_smul,
      ← (hω.exists_coeff h η).choose_spec W hW e]

/- English proof (translation)
The claim follows from `(hω.exists_coeff h η).choose_spec W hW e`.
-/
theorem resForm_eq_coeff_smul (hω : IsFrame ω) (h : V ≤ U) (η : FormsOn p D V)
    (hW : IsAffineOpen W) (e : W ≤ V) :
    resForm e η = resG Y e (hω.coeff h η) • resForm (e.trans h) ω := (hω.exists_coeff h η).choose_spec W hW e

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rintro rfl; exact fun W hW e => hω.resForm_eq_coeff_smul h η hW e, fun hc => hω.coeff_unique h (fun W hW e => hω.resForm_eq_coeff_smul h η hW e) hc⟩`.
-/
theorem coeff_eq_iff (hω : IsFrame ω) (h : V ≤ U) {η : FormsOn p D V} {c : Γ(Y, V)} :
    hω.coeff h η = c ↔ ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ V,
      resForm hW η = resG Y hW c • resForm (hW.trans h) ω := ⟨by rintro rfl; exact fun W hW e => hω.resForm_eq_coeff_smul h η hW e,
    fun hc => hω.coeff_unique h (fun W hW e => hω.resForm_eq_coeff_smul h η hW e) hc⟩

/- English proof (translation)
Establish `e` using `hω.resForm_eq_coeff_smul h η hV le_rfl`. Rewrite `e` using `[resForm_self, resG_self]`. Conclude with `e.symm`.
-/
theorem coeff_smul_resForm (hω : IsFrame ω) (hV : IsAffineOpen V) (h : V ≤ U)
    (η : FormsOn p D V) : hω.coeff h η • resForm h ω = η := by
  have e := hω.resForm_eq_coeff_smul h η hV le_rfl
  rw [resForm_self, resG_self] at e
  exact e.symm

/- English proof (translation)
Use `((hω.coeff_eq_iff _).2 fun W' hW' e' => ?_).symm` and prove the remaining obligations. Rewrite using `[resForm_resForm, hω.resForm_eq_coeff_smul h η hW' (e'.trans e), resG_resG]`.
-/
@[simp] theorem resG_coeff (hω : IsFrame ω) (h : V ≤ U) (e : W ≤ V) (η : FormsOn p D V) :
    resG Y e (hω.coeff h η) = hω.coeff (e.trans h) (resForm e η) := by
  refine ((hω.coeff_eq_iff _).2 fun W' hW' e' => ?_).symm
  rw [resForm_resForm, hω.resForm_eq_coeff_smul h η hW' (e'.trans e), resG_resG]

/- English proof (translation)
Rewrite using `[hω.coeff_eq_iff]`. Introduce `W hW e`. Rewrite using `[map_one, one_smul, resForm_resForm]`.
-/
@[simp] theorem coeff_self (hω : IsFrame ω) (h : V ≤ U) : hω.coeff h (resForm h ω) = 1 := by
  rw [hω.coeff_eq_iff]
  intro W hW e
  rw [map_one, one_smul, resForm_resForm]

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `(hω.coeff_eq_iff h).2 fun W hW e' => by rw [resForm_smul, resForm_resForm]`.
-/
theorem coeff_eq_of_eq_smul (hω : IsFrame ω) (h : V ≤ U) {η : FormsOn p D V} {c : Γ(Y, V)}
    (e : η = c • resForm h ω) : hω.coeff h η = c := by
  subst e
  exact (hω.coeff_eq_iff h).2 fun W hW e' => by rw [resForm_smul, resForm_resForm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun η η' e => by rw [← hω.coeff_smul_resForm hV h η, ← hω.coeff_smul_resForm hV h η', e], fun c => ⟨c • resForm h ω, hω.coeff_eq_of_eq_smul h rfl⟩⟩`.
-/
theorem bijective_coeff (hω : IsFrame ω) (hV : IsAffineOpen V) (h : V ≤ U) :
    Function.Bijective (hω.coeff h) := ⟨fun η η' e => by rw [← hω.coeff_smul_resForm hV h η, ← hω.coeff_smul_resForm hV h η', e],
    fun c => ⟨c • resForm h ω, hω.coeff_eq_of_eq_smul h rfl⟩⟩

/- English proof (translation)
Use `(hω.coeff_eq_iff h).2 fun W hW e => ?_` and prove the remaining obligations. Rewrite using `[hω'.resForm_eq_coeff_smul h' η hW e, ← resForm_resForm h' e, hω.resForm_eq_coeff_smul h _ hW e, smul_smul, map_mul]`. Use `congr 1`. Conclude with `mul_comm _ _`.
-/
theorem coeff_change (hω : IsFrame ω) (hω' : IsFrame ω') (h : V ≤ U) (h' : V ≤ U')
    (η : FormsOn p D V) : hω.coeff h η = hω.coeff h (resForm h' ω') * hω'.coeff h' η := by
  refine (hω.coeff_eq_iff h).2 fun W hW e => ?_
  rw [hω'.resForm_eq_coeff_smul h' η hW e, ← resForm_resForm h' e, hω.resForm_eq_coeff_smul h _ hW e,
    smul_smul, map_mul]
  congr 1
  exact mul_comm _ _

def ratio (hω : IsFrame ω) (hω' : IsFrame ω') : Γ(Y, U ⊓ U')ˣ where
  val := hω.coeff inf_le_left (resForm inf_le_right ω')
  inv := hω'.coeff inf_le_right (resForm inf_le_left ω)
  val_inv := by rw [← coeff_change, coeff_self]
  inv_val := by rw [← coeff_change, coeff_self]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `resG Y h (hω.coeff inf_le_left (resForm inf_le_right ω')) = _`. Rewrite using `[hω.resG_coeff inf_le_left h, resForm_resForm]`.
-/
theorem resG_ratio (hω : IsFrame ω) (hω' : IsFrame ω') (h : V ≤ U ⊓ U') :
    resG Y h (hω.ratio hω' : Γ(Y, U ⊓ U')) =
      hω.coeff (h.trans inf_le_left) (resForm (h.trans inf_le_right) ω') := by
  change resG Y h (hω.coeff inf_le_left (resForm inf_le_right ω')) = _
  rw [hω.resG_coeff inf_le_left h, resForm_resForm]

/- English proof (translation)
Rewrite using `[hω.resG_ratio hω' (le_inf h h')]`. Conclude with `(hω.coeff_smul_resForm hW h _).symm`.
-/
theorem resForm_eq_ratio_smul (hω : IsFrame ω) (hω' : IsFrame ω') (hW : IsAffineOpen W)
    (h : W ≤ U) (h' : W ≤ U') :
    resForm h' ω' = resG Y (le_inf h h') (hω.ratio hω' : Γ(Y, U ⊓ U')) • resForm h ω := by
  rw [hω.resG_ratio hω' (le_inf h h')]
  exact (hω.coeff_smul_resForm hW h _).symm

/- English proof (translation)
The claim follows from `Units.ext (by rw [val_res, hω.resG_ratio hω h]; exact hω.coeff_self _)`.
-/
theorem res_ratio_self (hω : IsFrame ω) (h : V ≤ U ⊓ U) : Semi.res h (hω.ratio hω) = 1 := Units.ext (by rw [val_res, hω.resG_ratio hω h]; exact hω.coeff_self _)

/- English proof (translation)
The claim follows from `Units.ext (by rw [Units.val_mul, val_res, val_res, val_res, hω.resG_ratio hω' h₁, hω'.resG_ratio hω'' h₂, hω.resG_ratio hω'' h₃] exact (hω.coeff_change hω' _ _ _).symm)`.
-/
theorem res_ratio_mul (hω : IsFrame ω) (hω' : IsFrame ω') (hω'' : IsFrame ω'')
    (h₁ : V ≤ U ⊓ U') (h₂ : V ≤ U' ⊓ U'') (h₃ : V ≤ U ⊓ U'') :
    Semi.res h₁ (hω.ratio hω') * Semi.res h₂ (hω'.ratio hω'') = Semi.res h₃ (hω.ratio hω'') := Units.ext (by
  rw [Units.val_mul, val_res, val_res, val_res, hω.resG_ratio hω' h₁, hω'.resG_ratio hω'' h₂,
    hω.resG_ratio hω'' h₃]
  exact (hω.coeff_change hω' _ _ _).symm)

end IsFrame

variable (p D) in

/- English proof (translation)
Take `⟨U, hU, V, hV, hx, e, hs⟩` from `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := D) (f := p) x`. Establish `h0 : (resG (Sp k) (le_top : U ≤ ⊤)).IsStandardSmoothOfRelativeDimension 0` using `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 (etale_resG (isAffineOpen_top _) hU le_top)`. Establish `h1` using `(hs.comp h0).comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)`. Simplify using `only [add_zero] at h1`. Establish `e1 : algX p V = ((p.appLE U V e).hom.comp (resG (Sp k) (le_top : U ≤ ⊤))).comp (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.toRingHom`.

Use extensionality with `a`. Conclude with `congrArg (fun φ : Γ(Sp k, ⊤) ⟶ Γ(Y, V) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) (Scheme.Hom.map_appLE p e (homOfLE le_top).op).symm`. Take `⟨ω, hω⟩` from `exists_isFreeGen (e1 ▸ h1)`. Conclude with `⟨V, ω, hx, hV, hω⟩`.
-/
theorem exists_isFrame [SmoothOfRelativeDimension D p] (x : Y) :
    ∃ (U : Y.Opens) (ω : FormsOn p D U), x ∈ U ∧ IsFrame ω := by
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := D) (f := p) x
  have h0 : (resG (Sp k) (le_top : U ≤ ⊤)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 (etale_resG (isAffineOpen_top _) hU le_top)
  have h1 := (hs.comp h0).comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
  simp only [add_zero] at h1
  have e1 : algX p V = ((p.appLE U V e).hom.comp (resG (Sp k) (le_top : U ≤ ⊤))).comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.toRingHom := by
    ext a
    exact congrArg (fun φ : Γ(Sp k, ⊤) ⟶ Γ(Y, V) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a))
      (Scheme.Hom.map_appLE p e (homOfLE le_top).op).symm
  obtain ⟨ω, hω⟩ := exists_isFreeGen (e1 ▸ h1)
  exact ⟨V, ω, hx, hV, hω⟩

end TopForm

open TopForm LB CechPic TangentOrigin

variable {k : Type} [CommRing k] {Y : Scheme.{0}}

structure CanonLB (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] where

  bundle : LB Y

  isLB : bundle.IsLB

  affine : ∀ i, IsAffineOpen (bundle.U i)

  om : ∀ i, FormsOn p D (bundle.U i)

  gen : ∀ i, IsFreeGen Γ(Y, bundle.U i) (om i)

  trans : ∀ i j (W : Y.Opens), IsAffineOpen W → ∀ (hi : W ≤ bundle.U i) (hj : W ≤ bundle.U j),
    resForm hj (om j) =
      resG Y (le_inf hi hj) (bundle.g i j : Γ(Y, bundle.U i ⊓ bundle.U j)) • resForm hi (om i)

namespace CanonLB

variable {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p]

def ofFrames {ι : Type} (U : ι → Y.Opens) (ω : ∀ i, FormsOn p D (U i)) (h : ∀ i, IsFrame (ω i))
    (hU : ⨆ i, U i = ⊤) : CanonLB p D where
  bundle := ⟨ι, U, fun i j => (h i).ratio (h j)⟩
  isLB := ⟨hU, fun i => (h i).res_ratio_self _,
    fun i j l => (h i).res_ratio_mul (h j) (h l) _ _ _⟩
  affine i := (h i).affine
  om := ω
  gen i := (h i).gen
  trans i j _ hW hi hj := (h i).resForm_eq_ratio_smul (h j) hW hi hj

variable (p D) in

def all : CanonLB p D :=
  ofFrames (ι := Σ U : Y.Opens, {ω : FormsOn p D U // IsFrame ω}) (fun a => a.1) (fun a => a.2.1)
    (fun a => a.2.2) (eq_top_iff.2 fun x _ => by
      obtain ⟨U, ω, hx, hω⟩ := exists_isFrame p D x
      exact Opens.mem_iSup.2 ⟨⟨U, ω, hω⟩, hx⟩)

instance nonempty : Nonempty (CanonLB p D) := ⟨all p D⟩

variable (K K' : CanonLB p D) {V W : Y.Opens}

/- English proof (translation)
Assemble the required witnesses or components as `⟨K.affine i, K.gen i⟩`.
-/
theorem isFrame (i : K.bundle.ι) : IsFrame (K.om i) := ⟨K.affine i, K.gen i⟩

/- English proof (translation)
The claim follows from `Units.ext (fun_ext_affine fun W _ e => by rw [(K.isFrame i).resG_ratio (K.isFrame j) e] exact ((K.isFrame i).coeff_eq_of_eq_smul _ (K.trans i j W ‹_› _ _)).symm)`.
-/
theorem g_eq_ratio (i j : K.bundle.ι) : K.bundle.g i j = (K.isFrame i).ratio (K.isFrame j) := Units.ext (fun_ext_affine fun W _ e => by
  rw [(K.isFrame i).resG_ratio (K.isFrame j) e]
  exact ((K.isFrame i).coeff_eq_of_eq_smul _ (K.trans i j W ‹_› _ _)).symm)

def coeff (i : K.bundle.ι) (h : V ≤ K.bundle.U i) : FormsOn p D V →ₗ[Γ(Y, V)] Γ(Y, V) :=
  (K.isFrame i).coeff h

/- English proof (translation)
The claim follows from `(K.isFrame i).coeff_eq_iff h`.
-/
theorem coeff_eq_iff (i : K.bundle.ι) (h : V ≤ K.bundle.U i) {η : FormsOn p D V} {c : Γ(Y, V)} :
    K.coeff i h η = c ↔ ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ V,
      resForm hW η = resG Y hW c • resForm (hW.trans h) (K.om i) := (K.isFrame i).coeff_eq_iff h

/- English proof (translation)
The claim follows from `(K.isFrame i).coeff_smul_resForm hV h η`.
-/
theorem coeff_smul_om (i : K.bundle.ι) (hV : IsAffineOpen V) (h : V ≤ K.bundle.U i)
    (η : FormsOn p D V) : K.coeff i h η • resForm h (K.om i) = η := (K.isFrame i).coeff_smul_resForm hV h η

/- English proof (translation)
The claim follows from `(K.isFrame i).resG_coeff h e η`.
-/
@[simp] theorem resG_coeff (i : K.bundle.ι) (h : V ≤ K.bundle.U i) (e : W ≤ V)
    (η : FormsOn p D V) : resG Y e (K.coeff i h η) = K.coeff i (e.trans h) (resForm e η) := (K.isFrame i).resG_coeff h e η

/- English proof (translation)
The claim follows from `(K.isFrame i).coeff_self h`.
-/
@[simp] theorem coeff_om (i : K.bundle.ι) (h : V ≤ K.bundle.U i) :
    K.coeff i h (resForm h (K.om i)) = 1 := (K.isFrame i).coeff_self h

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(K.isFrame i).coeff hi η = _ * (K.isFrame j).coeff hj η`. Rewrite using `[(K.isFrame i).coeff_change (K.isFrame j) hi hj η, K.g_eq_ratio, (K.isFrame i).resG_ratio (K.isFrame j) (le_inf hi hj)]`.
-/
theorem coeff_change (i j : K.bundle.ι) (hi : V ≤ K.bundle.U i) (hj : V ≤ K.bundle.U j)
    (η : FormsOn p D V) : K.coeff i hi η =
      resG Y (le_inf hi hj) (K.bundle.g i j : Γ(Y, K.bundle.U i ⊓ K.bundle.U j)) *
        K.coeff j hj η := by
  change (K.isFrame i).coeff hi η = _ * (K.isFrame j).coeff hj η
  rw [(K.isFrame i).coeff_change (K.isFrame j) hi hj η, K.g_eq_ratio, (K.isFrame i).resG_ratio (K.isFrame j) (le_inf hi hj)]

def toSec (V : Y.Opens) : FormsOn p D V →ₗ[Γ(Y, V)] Γ(toMod K.bundle, V) where
  toFun η := mkSec (fun i => K.coeff i inf_le_right (resForm inf_le_left η)) fun i j => by
    simp only [resG_coeff, resForm_resForm]
    exact K.coeff_change i j _ _ _
  map_add' η η' := sec_ext fun i => by
    simp only [coord_mkSec, coord_add, map_add]
    rfl
  map_smul' a η := sec_ext fun i => by
    simp only [coord_mkSec, coord_smul, resForm_smul, map_smul, smul_eq_mul, RingHom.id_apply]
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coord_toSec (η : FormsOn p D V) (i : K.bundle.ι) :
    coord (K.toSec V η) i = K.coeff i inf_le_right (resForm inf_le_left η) := rfl

/- English proof (translation)
Rewrite using `[chartEquiv_apply, coord_toSec, K.resG_coeff, resForm_resForm, resForm_self]`.
-/
theorem chartEquiv_toSec (i : K.bundle.ι) (h : V ≤ K.bundle.U i) (η : FormsOn p D V) :
    chartEquiv K.isLB i h (K.toSec V η) = K.coeff i h η := by rw [chartEquiv_apply, coord_toSec, K.resG_coeff, resForm_resForm, resForm_self]

/- English proof (translation)
Use `sec_ext fun j => ?_` and prove the remaining obligations. Simplify using `[coord_toSec]`.
-/
theorem map_toSec (e : W ≤ V) (η : FormsOn p D V) :
    (toMod K.bundle).presheaf.map (homOfLE e).op (K.toSec V η) = K.toSec W (resForm e η) := by
  refine sec_ext fun j => ?_
  simp [coord_toSec]

/- English proof (translation)
Establish `hc : ⇑(chartEquiv K.isLB i h) ∘ ⇑(K.toSec V) = ⇑(K.coeff i h)` using `funext fun η => K.chartEquiv_toSec i h η`. Establish `hb : Function.Bijective (⇑(chartEquiv K.isLB i h) ∘ ⇑(K.toSec V))`. Rewrite using `[hc]`. Conclude with `(K.isFrame i).bijective_coeff hV h`. Conclude with `((chartEquiv K.isLB i h).bijective.of_comp_iff' _).1 hb`.
-/
theorem bijective_toSec (i : K.bundle.ι) (hV : IsAffineOpen V) (h : V ≤ K.bundle.U i) :
    Function.Bijective (K.toSec V) := by
  have hc : ⇑(chartEquiv K.isLB i h) ∘ ⇑(K.toSec V) = ⇑(K.coeff i h) := funext fun η => K.chartEquiv_toSec i h η
  have hb : Function.Bijective (⇑(chartEquiv K.isLB i h) ∘ ⇑(K.toSec V)) := by
    rw [hc]
    exact (K.isFrame i).bijective_coeff hV h
  exact ((chartEquiv K.isLB i h).bijective.of_comp_iff' _).1 hb

/- English proof (translation)
Unfold `chartSec`. Use `sec_ext fun j => ?_` and prove the remaining obligations. Simplify using `only [coord_toSec]`. Use `(K.coeff_eq_iff j _).2 fun W hW e => ?_` and prove the remaining obligations. Rewrite using `[resForm_resForm, K.trans j i W hW (e.trans inf_le_right) (e.trans inf_le_left)]`.

Use `congr 1`. Use `erw [congrFun (coord_mkSec _ _) j]`. Conclude with `(resG_resG _ _ _).symm`.
-/
theorem toSec_om (i : K.bundle.ι) : K.toSec _ (K.om i) = chartSec K.isLB i := by
  unfold chartSec
  refine sec_ext fun j => ?_
  simp only [coord_toSec]
  refine (K.coeff_eq_iff j _).2 fun W hW e => ?_
  rw [resForm_resForm, K.trans j i W hW (e.trans inf_le_right) (e.trans inf_le_left)]
  congr 1
  erw [congrFun (coord_mkSec _ _) j]
  exact (resG_resG _ _ _).symm

def iso : LB.Iso K.bundle K'.bundle := ⟨fun a => (K'.isFrame a.1).ratio (K.isFrame a.2)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem weak_admissible_iso (a : K'.bundle.ι) (b : K.bundle.ι) :
    (K.iso K').s (a, b) = (K'.isFrame a).ratio (K.isFrame b) := rfl

/- English proof (translation)
Use `ext`. Simplify using `only [Units.val_mul]`. Take the linear combination `(↑h⁻¹ : R) * e - (x : R) * (Units.inv_mul h)`.
-/
private theorem units_eq_mul_inv_mul_of_mul_eq {R : Type*} [CommRing R] (x g h y : Rˣ) (e : (x : R) * h = g * y) :
    x = g * h⁻¹ * y := by
  ext
  simp only [Units.val_mul]
  linear_combination (↑h⁻¹ : R) * e - (x : R) * (Units.inv_mul h)

/- English proof (translation)
Simplify using `only [val_res, g_eq_ratio, IsFrame.resG_ratio]`. Rewrite using `[← (K'.isFrame a1).coeff_change (K.isFrame a2), ← (K'.isFrame a1).coeff_change (K'.isFrame b1)]`.
-/
private theorem frame_ratio_res_mul_g_eq_g_mul_ratio_res (K K' : CanonLB p D) (a1 b1 : K'.bundle.ι) (a2 b2 : K.bundle.ι) {O : Y.Opens}
    (hO₁ : O ≤ K'.bundle.U a1 ⊓ K.bundle.U a2) (hO₂ : O ≤ K.bundle.U a2 ⊓ K.bundle.U b2)
    (hO₃ : O ≤ K'.bundle.U a1 ⊓ K'.bundle.U b1) (hO₄ : O ≤ K'.bundle.U b1 ⊓ K.bundle.U b2) :
    (res hO₁ ((K'.isFrame a1).ratio (K.isFrame a2)) : Γ(Y, O)) * (res hO₂ (K.bundle.g a2 b2) : Γ(Y, O)) =
      (res hO₃ (K'.bundle.g a1 b1) : Γ(Y, O)) * (res hO₄ ((K'.isFrame b1).ratio (K.isFrame b2)) : Γ(Y, O)) := by
  simp only [val_res, g_eq_ratio, IsFrame.resG_ratio]
  rw [← (K'.isFrame a1).coeff_change (K.isFrame a2), ← (K'.isFrame a1).coeff_change (K'.isFrame b1)]

/- English proof (translation)
Unfold `LB.Gen.IsGen`. Introduce and unpack `⟨a1, a2⟩ ⟨b1, b2⟩`. Simplify using `only [LB.div]`. Use `units_eq_mul_inv_mul_of_mul_eq _ _ _ _ ?_` and prove the remaining obligations. Conclude with `frame_ratio_res_mul_g_eq_g_mul_ratio_res K K' a1 b1 a2 b2 _ _ _ _`.
-/
theorem iso_isGen : (K.iso K').IsGen := by
  unfold LB.Gen.IsGen
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩
  dsimp only [LB.div]
  refine units_eq_mul_inv_mul_of_mul_eq _ _ _ _ ?_
  exact frame_ratio_res_mul_g_eq_g_mul_ratio_res K K' a1 b1 a2 b2 _ _ _ _

/- English proof (translation)
Assemble the required witnesses or components as `⟨K.iso K', K.iso_isGen K'⟩`.
-/
theorem lbIso : LBIso K.bundle K'.bundle := ⟨K.iso K', K.iso_isGen K'⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(K'.isFrame a).coeff ha η = _ * (K.isFrame b).coeff hb η`. Rewrite using `[(K'.isFrame a).coeff_change (K.isFrame b) ha hb η, (K'.isFrame a).resG_ratio (K.isFrame b) (le_inf ha hb)]`.
-/
theorem coeff_eq_iso_mul (a : K'.bundle.ι) (b : K.bundle.ι) (ha : V ≤ K'.bundle.U a)
    (hb : V ≤ K.bundle.U b) (η : FormsOn p D V) :
    K'.coeff a ha η =
      resG Y (le_inf ha hb) ((K'.isFrame a).ratio (K.isFrame b)).val * K.coeff b hb η := by
  change (K'.isFrame a).coeff ha η = _ * (K.isFrame b).coeff hb η
  rw [(K'.isFrame a).coeff_change (K.isFrame b) ha hb η, (K'.isFrame a).resG_ratio (K.isFrame b) (le_inf ha hb)]

/- English proof (translation)
Use `Y.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // IsAffineOpen W ∧ W ≤ V ∧ ∃ i, W ≤ U i} => W.1) V (fun W => homOfLE W.2.2.1) ?_ a b fun W => h W.1 W.2.2.2.choose W.2.1 W.2.2.1 W.2.2.2.choose_spec` and prove the remaining obligations. Introduce `x hx`. Establish `hxU : x ∈ ⨆ i, U i` using `by rw [hU]; trivial`. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 hxU`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V ⊓ U i from ⟨hx, hi⟩) (V ⊓ U i).2`.

Establish `hWV' : W ≤ V ⊓ U i` using `hWV`. Conclude with `Opens.mem_iSup.2 ⟨⟨W, hW, hWV'.trans inf_le_left, i, hWV'.trans inf_le_right⟩, hxW⟩`.
-/
private theorem eq_of_resG_eq_on_affine_cover {ι : Type} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤) {V : Y.Opens}
    {a b : Γ(Y, V)}
    (h : ∀ (W : Y.Opens) (i : ι), IsAffineOpen W → ∀ (hW : W ≤ V), W ≤ U i → resG Y hW a = resG Y hW b) :
    a = b := by
  refine Y.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // IsAffineOpen W ∧ W ≤ V ∧ ∃ i, W ≤ U i} => W.1) V
    (fun W => homOfLE W.2.2.1) ?_ a b fun W => h W.1 W.2.2.2.choose W.2.1 W.2.2.1 W.2.2.2.choose_spec
  intro x hx
  have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hxU
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V ⊓ U i from ⟨hx, hi⟩) (V ⊓ U i).2
  have hWV' : W ≤ V ⊓ U i := hWV
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWV'.trans inf_le_left, i, hWV'.trans inf_le_right⟩, hxW⟩

/- English proof (translation)
Use `sec_ext fun a => ?_` and prove the remaining obligations. Use `eq_of_resG_eq_on_affine_cover K.bundle.U K.isLB.1 fun W b hW e hb => ?_` and prove the remaining obligations. Rewrite using `[coord_isoOfGen_hom_app K.isLB K'.isLB (K.iso K') (K.iso_isGen K') _ a b e (le_inf (e.trans inf_le_left) hb) (le_inf (e.trans inf_le_right) hb)]`. Rewrite using `[coord_toSec, coord_toSec, K.resG_coeff, K'.resG_coeff, resForm_resForm, resForm_resForm]`. Conclude with `(K.coeff_eq_iso_mul K' a b _ _ _).symm`.
-/
theorem isoOfGen_toSec (η : FormsOn p D V) :
    (isoOfGen K.isLB K'.isLB (K.iso K') (K.iso_isGen K')).hom.app V (K.toSec V η) =
      K'.toSec V η := by
  refine sec_ext fun a => ?_
  refine eq_of_resG_eq_on_affine_cover K.bundle.U K.isLB.1 fun W b hW e hb => ?_
  rw [coord_isoOfGen_hom_app K.isLB K'.isLB (K.iso K') (K.iso_isGen K') _ a b e
    (le_inf (e.trans inf_le_left) hb) (le_inf (e.trans inf_le_right) hb)]
  rw [coord_toSec, coord_toSec, K.resG_coeff, K'.resG_coeff, resForm_resForm, resForm_resForm]
  exact (K.coeff_eq_iso_mul K' a b _ _ _).symm

def jacobian (i : K.bundle.ι) (h : V ≤ K.bundle.U i) (f : Fin D → Γ(Y, V)) : Γ(Y, V) :=
  K.coeff i h (dOn p f)

/- English proof (translation)
The claim follows from `K.coeff_smul_om i hV h (dOn p f)`.
-/
theorem jacobian_smul_om (i : K.bundle.ι) (hV : IsAffineOpen V) (h : V ≤ K.bundle.U i)
    (f : Fin D → Γ(Y, V)) : K.jacobian i h f • resForm h (K.om i) = dOn p f := K.coeff_smul_om i hV h (dOn p f)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `resG Y e (K.coeff i h (dOn p f)) = K.coeff i (e.trans h) (dOn p _)`. Rewrite using `[K.resG_coeff, resForm_dOn]`.
-/
@[simp] theorem resG_jacobian (i : K.bundle.ι) (h : V ≤ K.bundle.U i) (e : W ≤ V)
    (f : Fin D → Γ(Y, V)) :
    resG Y e (K.jacobian i h f) = K.jacobian i (e.trans h) fun a => resG Y e (f a) := by
  change resG Y e (K.coeff i h (dOn p f)) = K.coeff i (e.trans h) (dOn p _)
  rw [K.resG_coeff, resForm_dOn]

/- English proof (translation)
The claim follows from `K.coeff_change i j hi hj (dOn p f)`.
-/
theorem jacobian_change (i j : K.bundle.ι) (hi : V ≤ K.bundle.U i) (hj : V ≤ K.bundle.U j)
    (f : Fin D → Γ(Y, V)) : K.jacobian i hi f =
      resG Y (le_inf hi hj) (K.bundle.g i j : Γ(Y, K.bundle.U i ⊓ K.bundle.U j)) *
        K.jacobian j hj f := K.coeff_change i j hi hj (dOn p f)

/- English proof (translation)
The claim follows from `map_dForm_mul_sub_mem (K.coeff i h) I u f hf`.
-/
theorem jacobian_mul_sub_mem (i : K.bundle.ι) (h : V ≤ K.bundle.U i) (I : Ideal Γ(Y, V))
    (u : Γ(Y, V)) (f : Fin D → Γ(Y, V)) (hf : ∀ a, f a ∈ I) :
    K.jacobian i h (fun a => u * f a) - u ^ D * K.jacobian i h f ∈ I := map_dForm_mul_sub_mem (K.coeff i h) I u f hf

/- English proof (translation)
Use `K.jacobian_mul_sub_mem i h (RingHom.ker ψ) u f hf` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, map_sub, map_mul, map_pow, sub_eq_zero]`. Conclude with `this`.
-/
theorem map_jacobian_mul {R : Type*} [CommRing R] (i : K.bundle.ι) (h : V ≤ K.bundle.U i)
    (ψ : Γ(Y, V) →+* R) (u : Γ(Y, V)) (f : Fin D → Γ(Y, V)) (hf : ∀ a, ψ (f a) = 0) :
    ψ (K.jacobian i h fun a => u * f a) = ψ u ^ D * ψ (K.jacobian i h f) := by
  have := K.jacobian_mul_sub_mem i h (RingHom.ker ψ) u f hf
  rw [RingHom.mem_ker, map_sub, map_mul, map_pow, sub_eq_zero] at this
  exact this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `K.coeff i h (dForm _ f) = m.det * K.coeff i h (dForm _ x)`. Rewrite using `[dForm_eq_det_smul f x m e, map_smul, smul_eq_mul]`.
-/
theorem jacobian_eq_det_mul (i : K.bundle.ι) (h : V ≤ K.bundle.U i) (f x : Fin D → Γ(Y, V))
    (m : Matrix (Fin D) (Fin D) Γ(Y, V))
    (e : ∀ a, dFun (algX p V) (f a) = ∑ b, m a b • dFun (algX p V) (x b)) :
    K.jacobian i h f = m.det * K.jacobian i h x := by
  change K.coeff i h (dForm _ f) = m.det * K.coeff i h (dForm _ x)
  rw [dForm_eq_det_smul f x m e, map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[← K.jacobian_smul_om i hV h x]`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Conclude with `⟨hV, ((K.isFrame i).res hV h).gen.smul_iff.2 hu⟩`. Introduce `hf`.

Conclude with `((K.isFrame i).res hV h).gen.smul_iff.1 hf.gen`.
-/
theorem isUnit_jacobian_iff (i : K.bundle.ι) (hV : IsAffineOpen V) (h : V ≤ K.bundle.U i)
    (x : Fin D → Γ(Y, V)) : IsUnit (K.jacobian i h x) ↔ IsFrame (dOn p x) := by
  rw [← K.jacobian_smul_om i hV h x]
  constructor
  · intro hu
    exact ⟨hV, ((K.isFrame i).res hV h).gen.smul_iff.2 hu⟩
  · intro hf
    exact ((K.isFrame i).res hV h).gen.smul_iff.1 hf.gen

end CanonLB

namespace LB

variable {L : LB Y} {T : Scheme.{0}}

def VanishesAlong (s : LB.Sec L) (y : T ⟶ Y) : Prop := ∀ j, (y.app (L.U j)).hom (s.f j) = 0

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Y.presheaf.map (homOfLE h).op ≫ y.appLE V W e).hom (s.f j) = 0`. Rewrite using `[Scheme.Hom.map_appLE, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, hs j, map_zero]`.
-/
theorem VanishesAlong.appLE_resG {s : LB.Sec L} {y : T ⟶ Y} (hs : VanishesAlong s y) (j : L.ι)
    {V : Y.Opens} (h : V ≤ L.U j) {W : T.Opens} (e : W ≤ y ⁻¹ᵁ V) :
    (y.appLE V W e).hom (resG Y h (s.f j)) = 0 := by
  change (Y.presheaf.map (homOfLE h).op ≫ y.appLE V W e).hom (s.f j) = 0
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, hs j, map_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs`. Express the relevant statement in the definitionally equal form `((y.app (L.U j) ≫ (Sp R).presheaf.map (homOfLE h).op) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (s.f j) = 0`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, hs j, map_zero]`. Introduce `h0 j'`.

Establish `hA : (y.appLE (L.U j) ⊤ h).hom (s.f j) = 0`. Establish `e0` using `h0`. Unfold `evalPt at e0`. Rewrite `e0` using `[CommRingCat.hom_comp, RingHom.comp_apply]`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (e0.trans (map_zero _).symm)`.

Establish `hO' : y ⁻¹ᵁ L.U j' ≤ y ⁻¹ᵁ (L.U j' ⊓ L.U j)` using `le_preimage_inf le_rfl (le_top.trans h)`. Establish `e2 : (y.appLE (L.U j' ⊓ L.U j) (y ⁻¹ᵁ L.U j') hO').hom (resG Y inf_le_right (s.f j)) = 0`. Express the relevant statement in the definitionally equal form `(Y.presheaf.map (homOfLE inf_le_right).op ≫ y.appLE (L.U j' ⊓ L.U j) (y ⁻¹ᵁ L.U j') hO').hom (s.f j) = 0`. Rewrite using `[Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_map y h (homOfLE le_top).op, CommRingCat.hom_comp, RingHom.comp_apply, hA, map_zero]`. Establish `e1 : (y.appLE (L.U j') (y ⁻¹ᵁ L.U j') le_rfl).hom (s.f j') = (y.appLE (L.U j' ⊓ L.U j) (y ⁻¹ᵁ L.U j') hO').hom (resG Y inf_le_left (s.f j'))`.

Express the relevant statement in the definitionally equal form `_ = (Y.presheaf.map (homOfLE inf_le_left).op ≫ y.appLE (L.U j' ⊓ L.U j) (y ⁻¹ᵁ L.U j') hO').hom (s.f j')`. Rewrite using `[Scheme.Hom.map_appLE]`. Rewrite using `[Scheme.Hom.app_eq_appLE, e1, sec_rel s j' j inf_le_left inf_le_right le_rfl, map_mul, e2, mul_zero]`.
-/
theorem vanishesAlong_iff_evalPt {R : Type} [CommRing R] (s : LB.Sec L) (y : Sp R ⟶ Y) (j : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ L.U j) : VanishesAlong s y ↔ evalPt y _ h (s.f j) = 0 := by
  constructor
  · intro hs
    change ((y.app (L.U j) ≫ (Sp R).presheaf.map (homOfLE h).op) ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (s.f j) = 0
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, hs j, map_zero]
  · intro h0 j'
    have hA : (y.appLE (L.U j) ⊤ h).hom (s.f j) = 0 := by
      have e0 := h0
      unfold evalPt at e0
      rw [CommRingCat.hom_comp, RingHom.comp_apply] at e0
      exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (e0.trans (map_zero _).symm)
    have hO' : y ⁻¹ᵁ L.U j' ≤ y ⁻¹ᵁ (L.U j' ⊓ L.U j) := le_preimage_inf le_rfl (le_top.trans h)
    have e2 : (y.appLE (L.U j' ⊓ L.U j) (y ⁻¹ᵁ L.U j') hO').hom (resG Y inf_le_right (s.f j)) = 0 := by
      change (Y.presheaf.map (homOfLE inf_le_right).op ≫ y.appLE (L.U j' ⊓ L.U j) (y ⁻¹ᵁ L.U j') hO').hom
        (s.f j) = 0
      rw [Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_map y h (homOfLE le_top).op, CommRingCat.hom_comp,
        RingHom.comp_apply, hA, map_zero]
    have e1 : (y.appLE (L.U j') (y ⁻¹ᵁ L.U j') le_rfl).hom (s.f j') =
        (y.appLE (L.U j' ⊓ L.U j) (y ⁻¹ᵁ L.U j') hO').hom (resG Y inf_le_left (s.f j')) := by
      change _ = (Y.presheaf.map (homOfLE inf_le_left).op ≫ y.appLE (L.U j' ⊓ L.U j) (y ⁻¹ᵁ L.U j') hO').hom
        (s.f j')
      rw [Scheme.Hom.map_appLE]
    rw [Scheme.Hom.app_eq_appLE, e1, sec_rel s j' j inf_le_left inf_le_right le_rfl, map_mul, e2, mul_zero]

/- English proof (translation)
Introduce `x hx`. Conclude with `Set.mem_iInter.1 hx PUnit.unit`.
-/
theorem lbPow_U_le (n : ℕ) (j : (lbPow L n).ι) : (lbPow L n).U j ≤ L.U (j PUnit.unit) := by
  intro x hx
  exact Set.mem_iInter.1 hx PUnit.unit

/- English proof (translation)
Express the relevant statement in the definitionally equal form `resG Y h ((∏ k : PUnit, (res _ ((pullU (𝟙 Y) _) (L.g (j k) (j' k)))) ^ (n : ℤ) : Γ(Y, (lbPow L n).U j ⊓ (lbPow L n).U j')ˣ) : Γ(Y, _)) = _`. Simplify using `only [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, pullU, Scheme.Hom.id_app]`. Use `congr 1`. Conclude with `resG_resG _ _ _`.
-/
private theorem lbPow_g_res_eq_pow (L : LB Y) (n : ℕ) (j j' : (lbPow L n).ι) {W : Y.Opens}
    (h : W ≤ (lbPow L n).U j ⊓ (lbPow L n).U j') (h₂ : W ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :
    resG Y h ((lbPow L n).g j j').val = resG Y h₂ (L.g (j PUnit.unit) (j' PUnit.unit)).val ^ n := by
  change resG Y h ((∏ k : PUnit, (res _ ((pullU (𝟙 Y) _) (L.g (j k) (j' k)))) ^ (n : ℤ) :
    Γ(Y, (lbPow L n).U j ⊓ (lbPow L n).U j')ˣ) : Γ(Y, _)) = _
  simp only [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, pullU, Scheme.Hom.id_app]
  congr 1
  exact resG_resG _ _ _

/- English proof (translation)
Rewrite using `[show ((tens M (lbPow L n)).g a b).val = resG Y (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (M.g a.1 b.1).val * resG Y (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) ((lbPow L n).g a.2 b.2).val from rfl]`. Conclude with `(map_mul (resG Y h) _ _).trans (congrArg₂ (· * ·) (resG_resG _ _ _) ((resG_resG _ _ _).trans (lbPow_g_res_eq_pow L n a.2 b.2 _ h₂)))`.
-/
theorem resG_tens_lbPow_g (M : LB Y) (n : ℕ) (a b : (tens M (lbPow L n)).ι) {W : Y.Opens}
    (h : W ≤ (tens M (lbPow L n)).U a ⊓ (tens M (lbPow L n)).U b)
    (h₁ : W ≤ M.U a.1 ⊓ M.U b.1) (h₂ : W ≤ L.U (a.2 PUnit.unit) ⊓ L.U (b.2 PUnit.unit)) :
    resG Y h ((tens M (lbPow L n)).g a b).val =
      resG Y h₁ (M.g a.1 b.1).val * resG Y h₂ (L.g (a.2 PUnit.unit) (b.2 PUnit.unit)).val ^ n := by
  rw [show ((tens M (lbPow L n)).g a b).val =
      resG Y (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (M.g a.1 b.1).val *
        resG Y (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
          ((lbPow L n).g a.2 b.2).val from rfl]
  exact (map_mul (resG Y h) _ _).trans (congrArg₂ (· * ·) (resG_resG _ _ _)
    ((resG_resG _ _ _).trans (lbPow_g_res_eq_pow L n a.2 b.2 _ h₂)))

end LB

namespace CanonLB

variable {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K K' : CanonLB p D) {L : LB Y}
  {V W : Y.Opens}

/- English proof (translation)
Establish `hq` using `isUnit_mk_of_formallyUnramified ((K.isFrame i).res hV h).gen f (K.jacobian_smul_om i hV h f) hu`. Establish `hker : Ideal.span (Set.range f) ≤ RingHom.ker ψ` using `Ideal.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hf a)`. Conclude with `hq.map (Ideal.Quotient.lift _ ψ fun x hx => hker hx)`.
-/
theorem isUnit_map_jacobian {R : Type*} [CommRing R] (i : K.bundle.ι) (hV : IsAffineOpen V)
    (h : V ≤ K.bundle.U i) (f : Fin D → Γ(Y, V))
    (hu : ((Ideal.Quotient.mk (Ideal.span (Set.range f))).comp (algX p V)).FormallyUnramified)
    (ψ : Γ(Y, V) →+* R) (hf : ∀ a, ψ (f a) = 0) : IsUnit (ψ (K.jacobian i h f)) := by
  have hq := isUnit_mk_of_formallyUnramified ((K.isFrame i).res hV h).gen f (K.jacobian_smul_om i hV h f) hu
  have hker : Ideal.span (Set.range f) ≤ RingHom.ker ψ :=
    Ideal.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hf a)
  exact hq.map (Ideal.Quotient.lift _ ψ fun x hx => hker hx)

abbrev adj (L : LB Y) (n : ℕ) : LB Y := tens K.bundle (lbPow L n)

/- English proof (translation)
The claim follows from `isLB_tens K.isLB (LB.isLB_linComb hL _ _)`.
-/
theorem isLB_adj (hL : L.IsLB) (n : ℕ) : (K.adj L n).IsLB := isLB_tens K.isLB (LB.isLB_linComb hL _ _)

def jacFun (s : Fin D → LB.Sec L) (i : K.bundle.ι) (j : L.ι) : Γ(Y, K.bundle.U i ⊓ L.U j) :=
  K.jacobian i inf_le_left fun a => resG Y inf_le_right ((s a).f j)

/- English proof (translation)
Unfold `jacFun`. Rewrite using `[K.resG_jacobian]`. Simplify using `only [resG_resG]`.
-/
theorem resG_jacFun (s : Fin D → LB.Sec L) (i : K.bundle.ι) (j : L.ι)
    (h : V ≤ K.bundle.U i ⊓ L.U j) : resG Y h (K.jacFun s i j) =
      K.jacobian i (h.trans inf_le_left) fun a => resG Y (h.trans inf_le_right) ((s a).f j) := by
  unfold jacFun
  rw [K.resG_jacobian]
  simp only [resG_resG]

/- English proof (translation)
Establish `hF : (fun a => resG Y (h.trans inf_le_right) ((s a).f j)) = fun a => resG Y h₂ (L.g j j').val * resG Y (h'.trans inf_le_right) ((s a).f j')`. Use function extensionality and compare the values at `fun a => sec_rel (s a) _ _ _ _ h₂`. Rewrite using `[K.resG_jacFun, K.resG_jacFun, hF]`. Establish `h3` using `K.jacobian_mul_sub_mem i (h.trans inf_le_left) I (resG Y h₂ (L.g j j').val) _ hI`. Rewrite `h3` using `[K.jacobian_change i i' (h.trans inf_le_left) (h'.trans inf_le_left) (fun a => resG Y (h'.trans inf_le_right) ((s a).f j'))]`.

Use `h3 using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacFun_change_sub_mem (s : Fin D → LB.Sec L) (i i' : K.bundle.ι) (j j' : L.ι)
    (h : V ≤ K.bundle.U i ⊓ L.U j) (h' : V ≤ K.bundle.U i' ⊓ L.U j')
    (h₁ : V ≤ K.bundle.U i ⊓ K.bundle.U i') (h₂ : V ≤ L.U j ⊓ L.U j') (I : Ideal Γ(Y, V))
    (hI : ∀ a, resG Y (h'.trans inf_le_right) ((s a).f j') ∈ I) :
    resG Y h (K.jacFun s i j) - resG Y h₁ (K.bundle.g i i').val * resG Y h₂ (L.g j j').val ^ D *
      resG Y h' (K.jacFun s i' j') ∈ I := by
  have hF : (fun a => resG Y (h.trans inf_le_right) ((s a).f j)) =
      fun a => resG Y h₂ (L.g j j').val * resG Y (h'.trans inf_le_right) ((s a).f j') :=
    funext fun a => sec_rel (s a) _ _ _ _ h₂
  rw [K.resG_jacFun, K.resG_jacFun, hF]
  have h3 := K.jacobian_mul_sub_mem i (h.trans inf_le_left) I (resG Y h₂ (L.g j j').val) _ hI
  rw [K.jacobian_change i i' (h.trans inf_le_left) (h'.trans inf_le_left)
    (fun a => resG Y (h'.trans inf_le_right) ((s a).f j'))] at h3
  convert h3 using 2
  ring

/- English proof (translation)
Use `K.jacFun_change_sub_mem s i i' j j' h h' h₁ h₂ (RingHom.ker ψ) fun a => RingHom.mem_ker.2 (hψ a)` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, map_sub, sub_eq_zero, map_mul, map_mul, map_pow]`. Conclude with `this`.
-/
theorem map_jacFun_change {R : Type*} [CommRing R] (s : Fin D → LB.Sec L) (i i' : K.bundle.ι)
    (j j' : L.ι) (h : V ≤ K.bundle.U i ⊓ L.U j) (h' : V ≤ K.bundle.U i' ⊓ L.U j')
    (h₁ : V ≤ K.bundle.U i ⊓ K.bundle.U i') (h₂ : V ≤ L.U j ⊓ L.U j') (ψ : Γ(Y, V) →+* R)
    (hψ : ∀ a, ψ (resG Y (h'.trans inf_le_right) ((s a).f j')) = 0) :
    ψ (resG Y h (K.jacFun s i j)) =
      ψ (resG Y h₁ (K.bundle.g i i').val) * ψ (resG Y h₂ (L.g j j').val) ^ D *
        ψ (resG Y h' (K.jacFun s i' j')) := by
  have := K.jacFun_change_sub_mem s i i' j j' h h' h₁ h₂ (RingHom.ker ψ) fun a => RingHom.mem_ker.2 (hψ a)
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_mul, map_mul, map_pow] at this
  exact this

/- English proof (translation)
The claim follows from `le_inf inf_le_left (inf_le_right.trans (lbPow_U_le n a.2))`.
-/
theorem adj_U_le (n : ℕ) (a : (K.adj L n).ι) :
    (K.adj L n).U a ≤ K.bundle.U a.1 ⊓ L.U (a.2 PUnit.unit) := le_inf inf_le_left (inf_le_right.trans (lbPow_U_le n a.2))

def dSec {T : Scheme.{0}} (s : Fin D → LB.Sec L) (y : T ⟶ Y) (hs : ∀ a, VanishesAlong (s a) y) :
    LB.Sec ((K.adj L D).pull y) where
  f c := (y.appLE _ _ ((pull_U_le y c).trans (y.preimage_mono (K.adj_U_le D (c PUnit.unit))))).hom
    (K.jacFun s (c PUnit.unit).1 ((c PUnit.unit).2 PUnit.unit))
  compat c c' := by
    have e : ((K.adj L D).pull y).U c ⊓ ((K.adj L D).pull y).U c' ≤
        y ⁻¹ᵁ ((K.adj L D).U (c PUnit.unit) ⊓ (K.adj L D).U (c' PUnit.unit)) :=
      inf_le_inf (pull_U_le y c) (pull_U_le y c')
    have l := K.adj_U_le D (c PUnit.unit)
    have l' := K.adj_U_le D (c' PUnit.unit)
    have l₁ := inf_le_inf (l.trans inf_le_left) (l'.trans inf_le_left)
    have l₂ := inf_le_inf (l.trans inf_le_right) (l'.trans inf_le_right)
    have h₁ := K.map_jacFun_change s _ _ _ _ (inf_le_left.trans l) (inf_le_right.trans l') l₁ l₂
      (y.appLE _ _ e).hom fun a => (hs a).appLE_resG _ _ e
    have h₂ := resG_tens_lbPow_g K.bundle D (c PUnit.unit) (c' PUnit.unit) le_rfl l₁ l₂
    have h₃ := resG_pull_g y c c' le_rfl
    rw [resG_self] at h₂ h₃
    rw [← map_pow, ← map_mul, LB.appLE_resG, LB.appLE_resG y (inf_le_right.trans l')] at h₁
    exact (resG_appLE y _ _ _).trans (h₁.trans (congrArg₂ (· * ·)
      ((congrArg (y.appLE _ _ e).hom h₂.symm).trans h₃.symm) (resG_appLE y _ _ _).symm))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dSec_f {T : Scheme.{0}} (s : Fin D → LB.Sec L) (y : T ⟶ Y)
    (hs : ∀ a, VanishesAlong (s a) y) (c : ((K.adj L D).pull y).ι) :
    (K.dSec s y hs).f c =
      (y.appLE _ _ ((pull_U_le y c).trans (y.preimage_mono (K.adj_U_le D (c PUnit.unit))))).hom
        (K.jacFun s (c PUnit.unit).1 ((c PUnit.unit).2 PUnit.unit)) := rfl

section Point

variable {F : Type} [CommRing F]

def jacVal (s : Fin D → LB.Sec L) (y : Sp F ⟶ Y) (i : K.bundle.ι) (j : L.ι)
    (hi : ⊤ ≤ y ⁻¹ᵁ K.bundle.U i) (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) : F :=
  evalPt y (K.bundle.U i ⊓ L.U j) (le_preimage_inf hi hj) (K.jacFun s i j)

/- English proof (translation)
Unfold `jacVal`. Rewrite using `[← evalPt_res y (le_inf h₁ h₂) _ hy, K.resG_jacFun]`.
-/
theorem jacVal_eq (s : Fin D → LB.Sec L) (y : Sp F ⟶ Y) (i : K.bundle.ι) (j : L.ι)
    (hi : ⊤ ≤ y ⁻¹ᵁ K.bundle.U i) (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) (h₁ : V ≤ K.bundle.U i) (h₂ : V ≤ L.U j)
    (hy : ⊤ ≤ y ⁻¹ᵁ V) : K.jacVal s y i j hi hj =
      evalPt y V hy (K.jacobian i h₁ fun a => resG Y h₂ ((s a).f j)) := by
  unfold jacVal
  rw [← evalPt_res y (le_inf h₁ h₂) _ hy, K.resG_jacFun]

/- English proof (translation)
Establish `hV : ⊤ ≤ y ⁻¹ᵁ (K.bundle.U i ⊓ L.U j ⊓ (K.bundle.U i' ⊓ L.U j'))` using `le_preimage_inf (le_preimage_inf hi hj) (le_preimage_inf hi' hj')`. Use `K.map_jacFun_change s i i' j j' inf_le_left inf_le_right (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (evalPt y _ hV) fun a => by` as an intermediate fact. Rewrite using `[evalPt_res y _ hj' hV]`. Conclude with `(vanishesAlong_iff_evalPt (s a) y j' hj').1 (hs a)`. Rewrite `this` using `[evalPt_res y _ (le_preimage_inf hi hj) hV, evalPt_res y _ (le_preimage_inf hi hi') hV, evalPt_res y _ (le_preimage_inf hj hj') hV, evalPt_res y _ (le_preimage_inf hi' hj') hV]`.

Conclude with `this`.
-/
theorem jacVal_change (s : Fin D → LB.Sec L) (y : Sp F ⟶ Y) (hs : ∀ a, VanishesAlong (s a) y)
    (i i' : K.bundle.ι) (j j' : L.ι) (hi : ⊤ ≤ y ⁻¹ᵁ K.bundle.U i) (hi' : ⊤ ≤ y ⁻¹ᵁ K.bundle.U i')
    (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ y ⁻¹ᵁ L.U j') :
    K.jacVal s y i j hi hj =
      evalPt y _ (le_preimage_inf hi hi') (K.bundle.g i i').val *
        evalPt y _ (le_preimage_inf hj hj') (L.g j j').val ^ D * K.jacVal s y i' j' hi' hj' := by
  have hV : ⊤ ≤ y ⁻¹ᵁ (K.bundle.U i ⊓ L.U j ⊓ (K.bundle.U i' ⊓ L.U j')) :=
    le_preimage_inf (le_preimage_inf hi hj) (le_preimage_inf hi' hj')
  have := K.map_jacFun_change s i i' j j' inf_le_left inf_le_right
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (evalPt y _ hV) fun a => by
      rw [evalPt_res y _ hj' hV]
      exact (vanishesAlong_iff_evalPt (s a) y j' hj').1 (hs a)
  rw [evalPt_res y _ (le_preimage_inf hi hj) hV, evalPt_res y _ (le_preimage_inf hi hi') hV,
    evalPt_res y _ (le_preimage_inf hj hj') hV, evalPt_res y _ (le_preimage_inf hi' hj') hV] at this
  exact this

/- English proof (translation)
Rewrite using `[K.jacVal_eq s y i j hi hj h₁ h₂ hy, show (fun a => resG Y h₂ ((s a).f j)) = fun a => u * f a from funext e]`. Conclude with `K.map_jacobian_mul i h₁ (evalPt y V hy) u f hf`.
-/
theorem jacVal_eq_pow_mul (s : Fin D → LB.Sec L) (y : Sp F ⟶ Y) (i : K.bundle.ι) (j : L.ι)
    (hi : ⊤ ≤ y ⁻¹ᵁ K.bundle.U i) (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) (h₁ : V ≤ K.bundle.U i) (h₂ : V ≤ L.U j)
    (hy : ⊤ ≤ y ⁻¹ᵁ V) (u : Γ(Y, V)) (f : Fin D → Γ(Y, V))
    (e : ∀ a, resG Y h₂ ((s a).f j) = u * f a) (hf : ∀ a, evalPt y V hy (f a) = 0) :
    K.jacVal s y i j hi hj = evalPt y V hy u ^ D * evalPt y V hy (K.jacobian i h₁ f) := by
  rw [K.jacVal_eq s y i j hi hj h₁ h₂ hy, show (fun a => resG Y h₂ ((s a).f j)) = fun a => u * f a from funext e]
  exact K.map_jacobian_mul i h₁ (evalPt y V hy) u f hf

/- English proof (translation)
Establish `hV : ⊤ ≤ y ⁻¹ᵁ (K'.bundle.U a ⊓ K.bundle.U b ⊓ L.U j)` using `le_preimage_inf (le_preimage_inf ha hb) hj`. Rewrite using `[K'.jacVal_eq s y a j ha hj (inf_le_left.trans inf_le_left) inf_le_right hV, K.jacVal_eq s y b j hb hj (inf_le_left.trans inf_le_right) inf_le_right hV, ← evalPt_res y inf_le_left (le_preimage_inf ha hb) hV, ← map_mul]`. Use `congr 1`. Conclude with `K.coeff_eq_iso_mul K' a b _ _ _`.
-/
theorem jacVal_eq_iso_mul (s : Fin D → LB.Sec L) (y : Sp F ⟶ Y) (a : K'.bundle.ι) (b : K.bundle.ι)
    (j : L.ι) (ha : ⊤ ≤ y ⁻¹ᵁ K'.bundle.U a) (hb : ⊤ ≤ y ⁻¹ᵁ K.bundle.U b)
    (hj : ⊤ ≤ y ⁻¹ᵁ L.U j) :
    K'.jacVal s y a j ha hj =
      evalPt y _ (le_preimage_inf ha hb) ((K'.isFrame a).ratio (K.isFrame b)).val *
        K.jacVal s y b j hb hj := by
  have hV : ⊤ ≤ y ⁻¹ᵁ (K'.bundle.U a ⊓ K.bundle.U b ⊓ L.U j) := le_preimage_inf (le_preimage_inf ha hb) hj
  rw [K'.jacVal_eq s y a j ha hj (inf_le_left.trans inf_le_left) inf_le_right hV,
    K.jacVal_eq s y b j hb hj (inf_le_left.trans inf_le_right) inf_le_right hV,
    ← evalPt_res y inf_le_left (le_preimage_inf ha hb) hV, ← map_mul]
  congr 1
  exact K.coeff_eq_iso_mul K' a b _ _ _

/- English proof (translation)
Rewrite using `[dSec_f]`. Unfold `jacVal evalPt`. Express the relevant statement in the definitionally equal form `((y.appLE _ _ _ ≫ (Sp F).presheaf.map (homOfLE hc).op) ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom _ = _`. Rewrite using `[Scheme.Hom.appLE_map]`.
-/
theorem dSec_f_eq_jacVal (s : Fin D → LB.Sec L) (y : Sp F ⟶ Y) (hs : ∀ a, VanishesAlong (s a) y)
    (c : ((K.adj L D).pull y).ι) (hc : ⊤ ≤ ((K.adj L D).pull y).U c)
    (hi : ⊤ ≤ y ⁻¹ᵁ K.bundle.U (c PUnit.unit).1)
    (hj : ⊤ ≤ y ⁻¹ᵁ L.U ((c PUnit.unit).2 PUnit.unit)) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (resG _ hc ((K.dSec s y hs).f c)) =
      K.jacVal s y _ _ hi hj := by
  rw [dSec_f]
  unfold jacVal evalPt
  change ((y.appLE _ _ _ ≫ (Sp F).presheaf.map (homOfLE hc).op) ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom _ = _
  rw [Scheme.Hom.appLE_map]

/- English proof (translation)
Rewrite using `[K.jacVal_eq s y i j hi hj h₁ h₂ hy]`. Use `K.isUnit_map_jacobian i hV h₁ _ hu _ fun a => ?_` and prove the remaining obligations. Rewrite using `[evalPt_res y h₂ hj hy]`. Conclude with `(vanishesAlong_iff_evalPt (s a) y j hj).1 (hs a)`.
-/
theorem isUnit_jacVal (s : Fin D → LB.Sec L) (y : Sp F ⟶ Y) (hs : ∀ a, VanishesAlong (s a) y)
    (i : K.bundle.ι) (j : L.ι) (hi : ⊤ ≤ y ⁻¹ᵁ K.bundle.U i) (hj : ⊤ ≤ y ⁻¹ᵁ L.U j)
    (hV : IsAffineOpen V) (h₁ : V ≤ K.bundle.U i) (h₂ : V ≤ L.U j) (hy : ⊤ ≤ y ⁻¹ᵁ V)
    (hu : ((Ideal.Quotient.mk (Ideal.span (Set.range fun a => resG Y h₂ ((s a).f j)))).comp
      (algX p V)).FormallyUnramified) : IsUnit (K.jacVal s y i j hi hj) := by
  rw [K.jacVal_eq s y i j hi hj h₁ h₂ hy]
  refine K.isUnit_map_jacobian i hV h₁ _ hu _ fun a => ?_
  rw [evalPt_res y h₂ hj hy]
  exact (vanishesAlong_iff_evalPt (s a) y j hj).1 (hs a)

end Point

end CanonLB

namespace TopForm

variable {p : Y ⟶ Sp k} {D : ℕ} {U V : Y.Opens}

variable (p) in

def jacOn (f : Fin (D + 1) → Γ(Y, U)) : FormsOn p D U := letI := (algX p U).toAlgebra; jac k f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jacOn_eq (f : Fin (D + 1) → Γ(Y, U)) : jacOn p f =
    ∑ a : Fin (D + 1), ((-1 : Γ(Y, U)) ^ (a : ℕ) * f a) • dOn p fun b => f (a.succAbove b) := rfl

/- English proof (translation)
Set `` to `(algX p U).toAlgebra`. Set `` to `(algX p V).toAlgebra`. Set `` to `(resG Y h).toAlgebra`. Establish `: IsScalarTower k Γ(Y, U) Γ(Y, V)` using `IsScalarTower.of_algebraMap_eq' (resG_comp_algX p h).symm`. Conclude with `map_jac k Γ(Y, V) f`.
-/
@[simp] theorem resForm_jacOn (h : V ≤ U) (f : Fin (D + 1) → Γ(Y, U)) :
    resForm h (jacOn p f) = jacOn p fun a => resG Y h (f a) := by
  let := (algX p U).toAlgebra
  let := (algX p V).toAlgebra
  let := (resG Y h).toAlgebra
  have : IsScalarTower k Γ(Y, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq' (resG_comp_algX p h).symm
  exact map_jac k Γ(Y, V) f

/- English proof (translation)
Set `` to `(algX p U).toAlgebra`. Conclude with `jac_mul k u f`.
-/
theorem jacOn_mul (u : Γ(Y, U)) (f : Fin (D + 1) → Γ(Y, U)) :
    jacOn p (fun a => u * f a) = u ^ (D + 1) • jacOn p f := by
  let := (algX p U).toAlgebra
  exact jac_mul k u f

end TopForm

namespace CanonLB

variable {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) {L : LB Y}
  {V : Y.Opens}

def jacSec (s : Fin (D + 1) → LB.Sec L) : LB.Sec (K.adj L (D + 1)) where
  f c := K.coeff c.1 ((K.adj_U_le _ c).trans inf_le_left)
    (jacOn p fun a => resG Y ((K.adj_U_le _ c).trans inf_le_right) ((s a).f (c.2 PUnit.unit)))
  compat c c' := by
    have l := K.adj_U_le _ c
    have l' := K.adj_U_le _ c'
    have l₁ := inf_le_inf (l.trans inf_le_left) (l'.trans inf_le_left)
    have l₂ := inf_le_inf (l.trans inf_le_right) (l'.trans inf_le_right)
    have h₂ := resG_tens_lbPow_g K.bundle (D + 1) c c' le_rfl l₁ l₂
    rw [resG_self] at h₂
    refine (K.resG_coeff _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) h₂.symm (K.resG_coeff _ _ _ _).symm))
    rw [K.coeff_change c.1 c'.1 _ (l₁.trans inf_le_right), mul_assoc, ← smul_eq_mul (_ ^ _),
      ← map_smul, resForm_jacOn, resForm_jacOn, ← jacOn_mul]
    simp only [resG_resG, fun a => sec_rel (s a) _ _ (l₂.trans inf_le_left)
      (l₂.trans inf_le_right) l₂]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `resG Y h (K.coeff c.1 _ (jacOn p fun a => resG Y _ ((s a).f (c.2 PUnit.unit)))) = _`. Rewrite using `[K.resG_coeff, resForm_jacOn]`. Simplify using `only [resG_resG]`.
-/
theorem resG_jacSec_f (s : Fin (D + 1) → LB.Sec L) (c : (K.adj L (D + 1)).ι)
    (h : V ≤ (K.adj L (D + 1)).U c) (h₁ : V ≤ K.bundle.U c.1) (h₂ : V ≤ L.U (c.2 PUnit.unit)) :
    resG Y h ((K.jacSec s).f c) =
      K.coeff c.1 h₁ (jacOn p fun a => resG Y h₂ ((s a).f (c.2 PUnit.unit))) := by
  change resG Y h (K.coeff c.1 _ (jacOn p fun a => resG Y _ ((s a).f (c.2 PUnit.unit)))) = _
  rw [K.resG_coeff, resForm_jacOn]
  simp only [resG_resG]

/- English proof (translation)
Rewrite using `[jacOn_eq, map_sum, map_sum, Fin.sum_univ_succ]`. Simplify using `only [map_smul, smul_eq_mul, map_mul, hf, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]`. Both sides reduce to the same expression.
-/
theorem map_coeff_jacOn {R : Type*} [CommRing R] (i : K.bundle.ι) (h : V ≤ K.bundle.U i)
    (ψ : Γ(Y, V) →+* R) (f : Fin (D + 1) → Γ(Y, V)) (hf : ∀ a : Fin D, ψ (f a.succ) = 0) :
    ψ (K.coeff i h (jacOn p f)) = ψ (f 0) * ψ (K.jacobian i h fun a => f a.succ) := by
  rw [jacOn_eq, map_sum, map_sum, Fin.sum_univ_succ]
  simp only [map_smul, smul_eq_mul, map_mul, hf, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rfl

/- English proof (translation)
Establish `hf : ∀ a : Fin D, evalPt y _ hc (resG Y ((K.adj_U_le _ c).trans inf_le_right) ((s a.succ).f (c.2 PUnit.unit))) = 0` using `fun a => by`. Rewrite using `[evalPt_res y _ hj hc]`. Conclude with `(vanishesAlong_iff_evalPt _ y _ hj).1 (hs a)`. Express the relevant statement in the definitionally equal form `evalPt y _ hc (K.coeff c.1 ((K.adj_U_le _ c).trans inf_le_left) (jacOn p fun a => resG Y ((K.adj_U_le _ c).trans inf_le_right) ((s a).f (c.2 PUnit.unit)))) = _`. Rewrite using `[K.map_coeff_jacOn c.1 _ _ _ hf, evalPt_res y _ hj hc, K.jacVal_eq (fun a => s a.succ) y _ _ hi hj ((K.adj_U_le _ c).trans inf_le_left) ((K.adj_U_le _ c).trans inf_le_right) hc]`.
-/
theorem evalPt_jacSec_f {F : Type} [CommRing F] (s : Fin (D + 1) → LB.Sec L) (y : Sp F ⟶ Y)
    (hs : ∀ a : Fin D, VanishesAlong (s a.succ) y) (c : (K.adj L (D + 1)).ι)
    (hc : ⊤ ≤ y ⁻¹ᵁ (K.adj L (D + 1)).U c) (hi : ⊤ ≤ y ⁻¹ᵁ K.bundle.U c.1)
    (hj : ⊤ ≤ y ⁻¹ᵁ L.U (c.2 PUnit.unit)) :
    evalPt y _ hc ((K.jacSec s).f c) =
      evalPt y _ hj ((s 0).f (c.2 PUnit.unit)) * K.jacVal (fun a => s a.succ) y _ _ hi hj := by
  have hf : ∀ a : Fin D, evalPt y _ hc (resG Y ((K.adj_U_le _ c).trans inf_le_right)
      ((s a.succ).f (c.2 PUnit.unit))) = 0 := fun a => by
    rw [evalPt_res y _ hj hc]
    exact (vanishesAlong_iff_evalPt _ y _ hj).1 (hs a)
  change evalPt y _ hc (K.coeff c.1 ((K.adj_U_le _ c).trans inf_le_left)
    (jacOn p fun a => resG Y ((K.adj_U_le _ c).trans inf_le_right) ((s a).f (c.2 PUnit.unit)))) = _
  rw [K.map_coeff_jacOn c.1 _ _ _ hf, evalPt_res y _ hj hc,
    K.jacVal_eq (fun a => s a.succ) y _ _ hi hj ((K.adj_U_le _ c).trans inf_le_left)
      ((K.adj_U_le _ c).trans inf_le_right) hc]

end CanonLB

namespace CanonLB

/- English proof (translation)
Establish `hd : dFun (algX p V) y = (-y ^ 2) • dFun (algX p V) x`. Set `_` to `(algX p V).toAlgebra`. Establish `h1 : KaehlerDifferential.D k Γ(Y, V) (x * y) = 0`. Rewrite using `[e]`. Conclude with `(KaehlerDifferential.D k Γ(Y, V)).map_one_eq_zero`.

Rewrite `h1` using `[Derivation.leibniz]`. Establish `h2` using `congrArg (y • ·) h1`. Simplify using `only [smul_add, smul_smul, smul_zero] at h2`. Rewrite `h2` using `[mul_comm y x, e, one_smul]`. Express the relevant statement in the definitionally equal form `KaehlerDifferential.D k Γ(Y, V) y = (-y ^ 2) • KaehlerDifferential.D k Γ(Y, V) x`.

Rewrite using `[neg_smul, eq_neg_iff_add_eq_zero, pow_two]`. Conclude with `h2`. Establish `hm : ∀ a, dFun (algX p V) (![y] a) = ∑ b, (!![-y ^ 2] : Matrix (Fin 1) (Fin 1) Γ(Y, V)) a b • dFun (algX p V) (![x] b)`. Introduce `a`. Use `fin_cases a`.

Simplify using `using hd`. Rewrite using `[K.jacobian_eq_det_mul i h ![y] ![x] _ hm, Matrix.det_fin_one_of]`.
-/
theorem jacobian_inv {p : Y ⟶ Sp k} [SmoothOfRelativeDimension 1 p] (K : CanonLB p 1)
    {V : Y.Opens} (i : K.bundle.ι) (h : V ≤ K.bundle.U i) (x y : Γ(Y, V)) (e : x * y = 1) :
    K.jacobian i h ![y] = -y ^ 2 * K.jacobian i h ![x] := by
  have hd : dFun (algX p V) y = (-y ^ 2) • dFun (algX p V) x := by
    let _ := (algX p V).toAlgebra
    have h1 : KaehlerDifferential.D k Γ(Y, V) (x * y) = 0 := by
      rw [e]
      exact (KaehlerDifferential.D k Γ(Y, V)).map_one_eq_zero
    rw [Derivation.leibniz] at h1
    have h2 := congrArg (y • ·) h1
    simp only [smul_add, smul_smul, smul_zero] at h2
    rw [mul_comm y x, e, one_smul] at h2
    change KaehlerDifferential.D k Γ(Y, V) y = (-y ^ 2) • KaehlerDifferential.D k Γ(Y, V) x
    rw [neg_smul, eq_neg_iff_add_eq_zero, pow_two]
    exact h2
  have hm : ∀ a, dFun (algX p V) (![y] a) =
      ∑ b, (!![-y ^ 2] : Matrix (Fin 1) (Fin 1) Γ(Y, V)) a b • dFun (algX p V) (![x] b) := by
    intro a
    fin_cases a
    simpa using hd
  rw [K.jacobian_eq_det_mul i h ![y] ![x] _ hm, Matrix.det_fin_one_of]

/- English proof (translation)
Establish `h₁` using `K.jacobian_inv i inf_le_left _ _ e`. Establish `h₂ : K.jacobian i inf_le_left ![resG Y (inf_le_left : _ ⊓ K.bundle.U j ≤ _) x] = 1`. Rewrite using `[← K.coeff_om i inf_le_left, hx, resForm_dOn, jacobian]`. Simplify using `only [Matrix.vec_single_eq_const, Function.const_apply]`. Establish `h₃ : K.jacobian j inf_le_right ![resG Y (inf_le_right : K.bundle.U i ⊓ _ ≤ _) y] = 1`.

Rewrite using `[← K.coeff_om j inf_le_right, hy, resForm_dOn, jacobian]`. Simplify using `only [Matrix.vec_single_eq_const, Function.const_apply]`. Rewrite `h₁` using `[K.jacobian_change i j _ inf_le_right, h₂, h₃, mul_one, mul_one, resG_self]`. Then use the resulting hypothesis.
-/
example {p : Y ⟶ Sp k} [SmoothOfRelativeDimension 1 p] (K : CanonLB p 1) (i j : K.bundle.ι)
    (x : Γ(Y, K.bundle.U i)) (y : Γ(Y, K.bundle.U j)) (hx : K.om i = dOn p ![x])
    (hy : K.om j = dOn p ![y])
    (e : resG Y (inf_le_left : K.bundle.U i ⊓ K.bundle.U j ≤ _) x * resG Y inf_le_right y = 1) :
    (K.bundle.g i j).val = -resG Y inf_le_right y ^ 2 := by
  have h₁ := K.jacobian_inv i inf_le_left _ _ e
  have h₂ : K.jacobian i inf_le_left ![resG Y (inf_le_left : _ ⊓ K.bundle.U j ≤ _) x] = 1 := by
    rw [← K.coeff_om i inf_le_left, hx, resForm_dOn, jacobian]
    simp only [Matrix.vec_single_eq_const, Function.const_apply]
  have h₃ : K.jacobian j inf_le_right ![resG Y (inf_le_right : K.bundle.U i ⊓ _ ≤ _) y] = 1 := by
    rw [← K.coeff_om j inf_le_right, hy, resForm_dOn, jacobian]
    simp only [Matrix.vec_single_eq_const, Function.const_apply]
  rwa [K.jacobian_change i j _ inf_le_right, h₂, h₃, mul_one, mul_one, resG_self] at h₁

section AffineSpace

open MvPolynomial

variable (k) (D : ℕ)

abbrev affStr : Sp (MvPolynomial (Fin D) k) ⟶ Sp k := spMap (algebraMap k _)

instance smooth_affStr : SmoothOfRelativeDimension D (affStr k D) := by
  let P₀ : Algebra.Presentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := Algebra.Generators.mvPolynomial k (Fin D)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation k (MvPolynomial (Fin D) k) (Fin D) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).2 ?_
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).2
      (P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])))

variable {k D} in

def polyFn : MvPolynomial (Fin D) k →+* Γ(Sp (MvPolynomial (Fin D) k), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv.hom

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, polyFn, algX]`. Rewrite using `[show Scheme.Hom.appLE (affStr k D) ⊤ ⊤ _ = (affStr k D).appTop from (Scheme.Hom.app_eq_appLE _).symm]`. Conclude with `congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k))))`.
-/
theorem polyFn_comp : (polyFn (k := k) (D := D)).comp (algebraMap k _) = algX (affStr k D) ⊤ := by
  ext a
  simp only [RingHom.comp_apply, polyFn, algX]
  rw [show Scheme.Hom.appLE (affStr k D) ⊤ ⊤ _ = (affStr k D).appTop from (Scheme.Hom.app_eq_appLE _).symm]
  exact congrArg (fun φ => φ.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k))))

/- English proof (translation)
Set `_` to `(algX (affStr k D) ⊤).toAlgebra`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C c`. Establish `e : polyFn (C c : MvPolynomial (Fin D) k) = algX (affStr k D) ⊤ c`. Rewrite using `[← polyFn_comp]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Simplify using `only [pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]`. Conclude with `(KaehlerDifferential.D k _).map_algebraMap c`. Consider the case `add p q hp hq`.

Simplify using `only [map_add, hp, hq, add_smul, Finset.sum_add_distrib]`. Consider the case `mul_X p i hp`. Establish `hl : dFun (algX (affStr k D) ⊤) (polyFn (p * X i)) = polyFn p • dFun (algX (affStr k D) ⊤) (polyFn (X i)) + polyFn (X i : MvPolynomial (Fin D) k) • dFun (algX (affStr k D) ⊤) (polyFn p)`. Rewrite using `[map_mul]`. Conclude with `(KaehlerDifferential.D k _).leibniz _ _`.

Rewrite using `[hl, hp, Finset.smul_sum]`. Simplify using `only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, add_smul, mul_smul, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using `[Pi.single_apply]`.
-/
private theorem dFun_polyFn_eq_sum_pderiv (g : MvPolynomial (Fin D) k) :
    dFun (algX (affStr k D) ⊤) (polyFn g) =
      ∑ b, polyFn (pderiv b g) • dFun (algX (affStr k D) ⊤) (polyFn (X b)) := by
  let _ := (algX (affStr k D) ⊤).toAlgebra
  induction g using MvPolynomial.induction_on with
  | C c =>
    have e : polyFn (C c : MvPolynomial (Fin D) k) = algX (affStr k D) ⊤ c := by
      rw [← polyFn_comp]
      rfl
    rw [e]
    simp only [pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact (KaehlerDifferential.D k _).map_algebraMap c
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hl : dFun (algX (affStr k D) ⊤) (polyFn (p * X i)) =
        polyFn p • dFun (algX (affStr k D) ⊤) (polyFn (X i)) +
          polyFn (X i : MvPolynomial (Fin D) k) • dFun (algX (affStr k D) ⊤) (polyFn p) := by
      rw [map_mul]
      exact (KaehlerDifferential.D k _).leibniz _ _
    rw [hl, hp, Finset.smul_sum]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, add_smul, mul_smul,
      Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply]

/- English proof (translation)
Use `⟨isAffineOpen_top _, ?_⟩` and prove the remaining obligations. Establish `hfg : IsFreeGen (MvPolynomial (Fin D) k) (dForm (algebraMap k (MvPolynomial (Fin D) k)) fun a => X a)`. Set `Pinst : Algebra k (MvPolynomial (Fin D) k) → Prop` to `fun I =>`. Use `letI := I`. Use `IsFreeGen (MvPolynomial (Fin D) k) (exteriorPower.ιMulti (MvPolynomial (Fin D) k) D fun a => KaehlerDifferential.D k (MvPolynomial (Fin D) k) (X a))`.

Establish `hstd : Pinst inferInstance`. Establish `hb` using `isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))`. Rewrite using `[show ⇑(KaehlerDifferential.mvPolynomialBasis k (Fin D)) = fun a => KaehlerDifferential.D k (MvPolynomial (Fin D) k) (X a) from`. Use function extensionality and compare the values at `fun a => by simp [KaehlerDifferential.mvPolynomialBasis_apply]] at hb`. Conclude with `hb`.

Establish `h : (inferInstance : Algebra k (MvPolynomial (Fin D) k)) = (algebraMap k (MvPolynomial (Fin D) k)).toAlgebra` using `toAlgebra_algebraMap.symm`. Conclude with `Eq.mp (congrArg Pinst h) hstd`. Establish `hρ : (polyFn (k` using `k) (D := D)).Etale := RingHom.Etale.of_bijective (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).commRingCatIsoToRingEquiv.symm.bijective`. Use `hfg.formMap hρ (polyFn_comp k D)` as an intermediate fact. Rewrite `this` using `[formMap_dForm]`.

Conclude with `this`.
-/
theorem isFrame_dX : IsFrame (dOn (affStr k D) fun a => polyFn (X a)) := by
  refine ⟨isAffineOpen_top _, ?_⟩
  have hfg : IsFreeGen (MvPolynomial (Fin D) k) (dForm (algebraMap k (MvPolynomial (Fin D) k)) fun a => X a) := by
    let Pinst : Algebra k (MvPolynomial (Fin D) k) → Prop := fun I =>
      letI := I
      IsFreeGen (MvPolynomial (Fin D) k) (exteriorPower.ιMulti (MvPolynomial (Fin D) k) D
        fun a => KaehlerDifferential.D k (MvPolynomial (Fin D) k) (X a))
    have hstd : Pinst inferInstance := by
      have hb := isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))
      rw [show ⇑(KaehlerDifferential.mvPolynomialBasis k (Fin D)) =
          fun a => KaehlerDifferential.D k (MvPolynomial (Fin D) k) (X a) from
        funext fun a => by simp [KaehlerDifferential.mvPolynomialBasis_apply]] at hb
      exact hb
    have h : (inferInstance : Algebra k (MvPolynomial (Fin D) k)) =
        (algebraMap k (MvPolynomial (Fin D) k)).toAlgebra := toAlgebra_algebraMap.symm
    exact Eq.mp (congrArg Pinst h) hstd
  have hρ : (polyFn (k := k) (D := D)).Etale := RingHom.Etale.of_bijective
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).commRingCatIsoToRingEquiv.symm.bijective
  have := hfg.formMap hρ (polyFn_comp k D)
  rw [formMap_dForm] at this
  exact this

def affineSpace : CanonLB (affStr k D) D :=
  ofFrames (ι := PUnit) (fun _ => ⊤) (fun _ => dOn _ fun a => polyFn (X a))
    (fun _ => isFrame_dX k D) iSup_const

variable {k D} in

/- English proof (translation)
Establish `hx : (affineSpace k D).jacobian PUnit.unit le_rfl (fun a => polyFn (X a)) = 1`. Use `(affineSpace k D).coeff_om PUnit.unit le_rfl` as an intermediate fact. Rewrite `this` using `[resForm_self]`. Then use the resulting hypothesis. Rewrite using `[(affineSpace k D).jacobian_eq_det_mul PUnit.unit le_rfl _ (fun a => polyFn (X a)) (polyFn.mapMatrix (Matrix.of fun a b => pderiv b (f a))) (fun a => dFun_polyFn_eq_sum_pderiv k D (f a)), hx, mul_one, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem jacobian_affineSpace (f : Fin D → MvPolynomial (Fin D) k) :
    (affineSpace k D).jacobian PUnit.unit le_rfl (fun a => polyFn (f a)) =
      polyFn (Matrix.of fun a b => pderiv b (f a)).det := by
  have hx : (affineSpace k D).jacobian PUnit.unit le_rfl (fun a => polyFn (X a)) = 1 := by
    have := (affineSpace k D).coeff_om PUnit.unit le_rfl
    rwa [resForm_self] at this
  rw [(affineSpace k D).jacobian_eq_det_mul PUnit.unit le_rfl _ (fun a => polyFn (X a))
    (polyFn.mapMatrix (Matrix.of fun a b => pderiv b (f a))) (fun a => dFun_polyFn_eq_sum_pderiv k D (f a)), hx, mul_one,
    RingHom.map_det]
  rfl

/- English proof (translation)
Use `(jacobian_affineSpace _).trans (Eq.trans ?_ (map_one polyFn))` and prove the remaining obligations. Rewrite using `[← Matrix.det_one (n := Fin D)]`. Use `congr 2`. Use extensionality with `a b : 2`. Simplify using `[Matrix.one_apply, Pi.single_apply]`.
-/
example : (affineSpace k D).jacobian PUnit.unit le_rfl (fun a => polyFn (X a)) = 1 := by
  refine (jacobian_affineSpace _).trans (Eq.trans ?_ (map_one polyFn))
  rw [← Matrix.det_one (n := Fin D)]
  congr 2
  ext a b : 2
  simp [Matrix.one_apply, Pi.single_apply]

/- English proof (translation)
Rewrite using `[jacobian_affineSpace]`. Simplify using `[Matrix.det_fin_two]`. Both sides reduce to the same expression.
-/
example : (affineSpace k 2).jacobian PUnit.unit le_rfl (fun a => polyFn (![X 1, X 0] a)) = -1 := by
  rw [jacobian_affineSpace]
  simp [Matrix.det_fin_two]
  rfl

/- English proof (translation)
Rewrite using `[jacobian_affineSpace]`. Simplify using `[map_ofNat]`. Both sides reduce to the same expression.
-/
example : (affineSpace k 1).jacobian PUnit.unit le_rfl (fun a => polyFn (![X 0 ^ 2] a)) =
    2 * polyFn (X 0) := by
  rw [jacobian_affineSpace]
  simp [map_ofNat]
  rfl

variable {k D} in

def polySec (f : MvPolynomial (Fin D) k) :
    LB.Sec (Out.Inh.trivLB (Sp (MvPolynomial (Fin D) k))) :=
  ⟨fun _ => polyFn f, fun _ _ => (one_mul _).symm⟩

/- English proof (translation)
Establish `h1` using `(affineSpace k D).jacVal_eq (fun a => polySec (f a)) (spMap φ) PUnit.unit PUnit.unit le_rfl le_rfl (V := ⊤) le_rfl le_rfl le_rfl`. Use `h1.trans ((congrArg (evalPt (spMap φ) ⊤ _) (congrArg ((affineSpace k D).jacobian PUnit.unit le_rfl) (funext fun a => resG_self _ _))).trans ?_)` and prove the remaining obligations. Conclude with `(congrArg _ (jacobian_affineSpace f)).trans (evalPt_spMap φ _)`.
-/
theorem jacVal_affineSpace {F : Type} [CommRing F] (φ : MvPolynomial (Fin D) k →+* F)
    (f : Fin D → MvPolynomial (Fin D) k) :
    (affineSpace k D).jacVal (fun a => polySec (f a)) (spMap φ) PUnit.unit PUnit.unit
      le_rfl le_rfl = φ (Matrix.of fun a b => pderiv b (f a)).det := by
  have h1 := (affineSpace k D).jacVal_eq (fun a => polySec (f a)) (spMap φ) PUnit.unit PUnit.unit le_rfl le_rfl
    (V := ⊤) le_rfl le_rfl le_rfl
  refine h1.trans ((congrArg (evalPt (spMap φ) ⊤ _) (congrArg ((affineSpace k D).jacobian PUnit.unit le_rfl)
    (funext fun a => resG_self _ _))).trans ?_)
  exact (congrArg _ (jacobian_affineSpace f)).trans (evalPt_spMap φ _)

/- English proof (translation)
Use `⟨(vanishesAlong_iff_evalPt _ _ PUnit.unit le_rfl).2 ((evalPt_spMap _ _).trans (by simp)), ?_⟩` and prove the remaining obligations. Rewrite using `[jacVal_affineSpace]`. Simplify using the standard rewrite rules.
-/
example : VanishesAlong (polySec (X 0 ^ 2 - 1 : MvPolynomial (Fin 1) k))
      (spMap (eval fun _ => 1)) ∧
    (affineSpace k 1).jacVal (fun a => polySec (![X 0 ^ 2 - 1] a)) (spMap (eval fun _ => 1))
      PUnit.unit PUnit.unit le_rfl le_rfl = 2 := by
  refine ⟨(vanishesAlong_iff_evalPt _ _ PUnit.unit le_rfl).2
    ((evalPt_spMap _ _).trans (by simp)), ?_⟩
  rw [jacVal_affineSpace]
  simp

end AffineSpace

end CanonLB

end GlobalTheory
