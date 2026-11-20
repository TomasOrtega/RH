import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigidEndo

/- English proof (translation)
Establish `: IsAffine U` using `hU`. Establish `hr : Set.range f ⊆ Set.range U.ι` using `by simpa using hf`. Set `g : X ⟶ U` to `IsOpenImmersion.lift U.ι f hr`. Establish `hg : g ≫ U.ι = f` using `IsOpenImmersion.lift_fac _ _ _`. Use `⟨S.isoSpec.hom ≫ inv (Spec.map p.appTop) ≫ Spec.map g.appTop ≫ (U : Scheme).isoSpec.inv ≫ U.ι, ?_⟩` and prove the remaining obligations.

Establish `e1 : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ (U : Scheme).isoSpec.inv`. Rewrite using `[← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]`. Establish `e2 : X.toSpecΓ = p ≫ S.isoSpec.hom ≫ inv (Spec.map p.appTop)`. Rewrite using `[Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]`. Rewrite using `[← hg]`.

Use `nth_rw 1 [e1]`. Rewrite using `[e2]`. Simplify using `only [Category.assoc]`.
-/
theorem exists_factor_of_range_subset {X Y S : Scheme.{0}} [IsAffine S] (p : X ⟶ S) [IsIso p.appTop]
    (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U) (hf : Set.range f ⊆ U) :
    ∃ h : S ⟶ Y, f = p ≫ h := by
  have : IsAffine U := hU
  have hr : Set.range f ⊆ Set.range U.ι := by simpa using hf
  let g : X ⟶ U := IsOpenImmersion.lift U.ι f hr
  have hg : g ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  refine ⟨S.isoSpec.hom ≫ inv (Spec.map p.appTop) ≫ Spec.map g.appTop ≫ (U : Scheme).isoSpec.inv ≫ U.ι, ?_⟩
  have e1 : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ (U : Scheme).isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have e2 : X.toSpecΓ = p ≫ S.isoSpec.hom ≫ inv (Spec.map p.appTop) := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← hg]
  nth_rw 1 [e1]
  rw [e2]
  simp only [Category.assoc]

/- English proof (translation)
Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Use `hB.geomConnected` as an intermediate fact. Use `haveI : GeometricallyIntegral B.hom := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom ‹_› ‹_›`. Conclude with `GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange GlobalTheory.exists_noetherian_model_of_smooth B.hom ⊤`.
-/
theorem isIso_appTop (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B]
    (hB : IsAbelianScheme B) : IsIso B.hom.appTop := by
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom ‹_› ‹_›
  exact GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange
    GlobalTheory.exists_noetherian_model_of_smooth B.hom ⊤

/- English proof (translation)
Introduce `k _ B _ hB α hα`. Use `set β : B ⟶ B := α * (𝟙 B)⁻¹ with hβ`. Establish `h1 : ∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k), z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → z ≫ β.left = z ≫ B.hom ≫ η[B].left`. Introduce `Z z y hz`. Set `zo : Over.mk (z ≫ B.hom) ⟶ B` to `Over.homMk z`.

Establish `ha : zo ≫ α = zo` using `by ext; exact hα Z z y hz`. Establish `hb : zo ≫ β = toUnit _ ≫ η[B]`. Rewrite using `[hβ, comp_mul, GrpObj.comp_inv, ha, Category.comp_id, mul_inv_cancel, Hom.one_def]`. Use `congrArg CommaMorphism.left hb` as an intermediate fact. Simplify `this` using `[zo]`.

Set `q : Sp k` to `Classical.arbitrary _`. Set `e0 : B.left` to `η[B].left (spMap (TrivSqZeroExt.fstHom k k k).toRingHom q)`. Establish `hsurj : Surjective (pullback.fst B.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))`. Use `GlobalTheory.ConstThickening.surjective_spMap_fst (K := k)` as an intermediate fact. Use `infer_instance`.

Establish `h2 : ∀ x : B.left, β.left x = e0`. Introduce `x`. Take `⟨w, rfl⟩` from `hsurj.surj x`. Use `h1 _ _ _ (pullback.condition (f := B.hom) (g := spMap (TrivSqZeroExt.fstHom k k k).toRingHom))` as an intermediate fact. Rewrite using `[← Scheme.Hom.comp_apply, this, pullback.condition_assoc]`.

Simplify using `only [Scheme.Hom.comp_apply, e0]`. Use `congr 2`. Conclude with `Subsingleton.elim _ _`. Take `⟨U, hU, heU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := B.left) (x := e0) (U := ⊤) trivial`. Use `isIso_appTop k B hB` as an intermediate fact.

Take `⟨h, hh⟩` from `exists_factor_of_range_subset B.hom β.left U hU (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[h2 x]`. Conclude with `heU)`. Establish `hη : η[B].left ≫ B.hom = 𝟙 _` using `by simpa using Over.w η[B]`.

Establish `h3 : β.left = B.hom ≫ η[B].left ≫ β.left`. Rewrite using `[hh, reassoc_of% hη]`. Establish `h4 : β = toUnit B ≫ η[B] ≫ β` using `by ext; simpa using h3`. Establish `h5 : η[B] ≫ β = η[B] ≫ α`. Establish `e : η[B] = (1 : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B)`.

Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Establish `e' : η[B]⁻¹ = (1 : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B)` using `by rw [e, inv_one]`. Rewrite using `[hβ, comp_mul, GrpObj.comp_inv, Category.comp_id, e', _root_.mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_translate : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B →
    ∀ (α : B ⟶ B), (∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k),
      z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → z ≫ α.left = z) →
    α = lift (toUnit B ≫ η[B] ≫ α) (𝟙 B) ≫ μ[B] := by
  intro k _ B _ hB α hα
  set β : B ⟶ B := α * (𝟙 B)⁻¹ with hβ

  have h1 : ∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k),
      z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
      z ≫ β.left = z ≫ B.hom ≫ η[B].left := by
    intro Z z y hz
    let zo : Over.mk (z ≫ B.hom) ⟶ B := Over.homMk z
    have ha : zo ≫ α = zo := by
      ext; exact hα Z z y hz
    have hb : zo ≫ β = toUnit _ ≫ η[B] := by
      rw [hβ, comp_mul, GrpObj.comp_inv, ha, Category.comp_id, mul_inv_cancel, Hom.one_def]
    have := congrArg CommaMorphism.left hb
    simpa [zo] using this

  let q : Sp k := Classical.arbitrary _
  let e0 : B.left := η[B].left (spMap (TrivSqZeroExt.fstHom k k k).toRingHom q)
  have hsurj : Surjective (pullback.fst B.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) := by
    have := GlobalTheory.ConstThickening.surjective_spMap_fst (K := k)
    infer_instance
  have h2 : ∀ x : B.left, β.left x = e0 := by
    intro x
    obtain ⟨w, rfl⟩ := hsurj.surj x
    have := h1 _ _ _ (pullback.condition (f := B.hom) (g := spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
    rw [← Scheme.Hom.comp_apply, this, pullback.condition_assoc]
    simp only [Scheme.Hom.comp_apply, e0]
    congr 2
    exact Subsingleton.elim _ _

  obtain ⟨U, hU, heU, -⟩ := exists_isAffineOpen_mem_and_subset (X := B.left) (x := e0) (U := ⊤) trivial
  have := isIso_appTop k B hB
  obtain ⟨h, hh⟩ := exists_factor_of_range_subset B.hom β.left U hU (by
    rintro _ ⟨x, rfl⟩; rw [h2 x]; exact heU)
  have hη : η[B].left ≫ B.hom = 𝟙 _ := by simpa using Over.w η[B]
  have h3 : β.left = B.hom ≫ η[B].left ≫ β.left := by
    rw [hh, reassoc_of% hη]

  have h4 : β = toUnit B ≫ η[B] ≫ β := by
    ext; simpa using h3
  have h5 : η[B] ≫ β = η[B] ≫ α := by
    have e : η[B] = (1 : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B) := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have e' : η[B]⁻¹ = (1 : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B) := by rw [e, inv_one]
    rw [hβ, comp_mul, GrpObj.comp_inv, Category.comp_id, e', _root_.mul_one]
  calc α = β * 𝟙 B := by rw [hβ, inv_mul_cancel_right]
    _ = _ := by rw [Hom.mul_def, h4, h5]

end GlobalTheory.RigidEndo
