import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSchemeMapFromSpecialFibreStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.FinFlat

/- English proof (translation)
Establish `hsurj : Function.Surjective f`. Establish `hQ : Subsingleton (IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f))`. Establish `key : ∀ z : IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f), z = 0` using `fun z => by`. Take `⟨w, rfl⟩` from `LinearMap.lTensor_surjective (IsLocalRing.ResidueField R) (Submodule.mkQ_surjective (LinearMap.range f)) z`. Take `⟨v, rfl⟩` from `h.2 w`.

Establish `h0 : (LinearMap.range f).mkQ ∘ₗ f = 0`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero]`. Both sides reduce to the same expression.

Conclude with `⟨fun x y => by rw [key x, key y]⟩`. Establish `h1 : Subsingleton (N ⧸ LinearMap.range f)` using `IsLocalRing.subsingleton_tensorProduct.1 hQ`. Conclude with `fun y => (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).1 (Subsingleton.elim _ _)`. Establish `hfree : Module.Free R N` using `Module.free_of_flat_of_isLocalRing`. Take `⟨s, hs⟩` from `Module.projective_lifting_property f LinearMap.id hsurj`.

Establish `hs' : ∀ y, f (s y) = y` using `fun y => LinearMap.congr_fun hs y`. Set `π : M →ₗ[R] LinearMap.ker f` to `(LinearMap.id - s ∘ₗ f).codRestrict (LinearMap.ker f) (fun x => by`. Simplify using `[hs'])`. Establish `hπ : π ∘ₗ (LinearMap.ker f).subtype = LinearMap.id`. Use extensionality with `x`.

Simplify using `[π, LinearMap.mem_ker.1 x.2]`. Establish `hK : Subsingleton (IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f)`. Establish `key : ∀ z : IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f, z = 0` using `fun z => by`. Establish `h0 : f ∘ₗ (LinearMap.ker f).subtype = 0`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Establish `h1 : (LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z = 0`. Apply `h.1` to reduce the goal to its premises. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero, map_zero]`. Both sides reduce to the same expression.

Establish `h2 : π.lTensor (IsLocalRing.ResidueField R) ((LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z) = z`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπ, LinearMap.lTensor_id]`. Both sides reduce to the same expression. Rewrite using `[← h2, h1, map_zero]`. Conclude with `⟨fun x y => by rw [key x, key y]⟩`.

Establish `hK' : Subsingleton (LinearMap.ker f)` using `IsLocalRing.subsingleton_tensorProduct.1 hK`. Use `⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, hsurj⟩` and prove the remaining obligations. Establish `h3 : (⟨x, hx⟩ : LinearMap.ker f) = 0` using `Subsingleton.elim _ _`. Simplify using `using congrArg Subtype.val h3`.
-/
theorem bijective_of_lTensor (R M N : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] (f : M →ₗ[R] N)
    (h : Function.Bijective (f.lTensor (IsLocalRing.ResidueField R))) : Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have hQ : Subsingleton (IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f)) := by
      have key : ∀ z : IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f), z = 0 := fun z => by
        obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective (IsLocalRing.ResidueField R)
          (Submodule.mkQ_surjective (LinearMap.range f)) z
        obtain ⟨v, rfl⟩ := h.2 w
        have h0 : (LinearMap.range f).mkQ ∘ₗ f = 0 := by
          ext x
          simp
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero]
        rfl
      exact ⟨fun x y => by rw [key x, key y]⟩
    have h1 : Subsingleton (N ⧸ LinearMap.range f) := IsLocalRing.subsingleton_tensorProduct.1 hQ
    exact fun y => (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).1 (Subsingleton.elim _ _)
  have hfree : Module.Free R N := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ y, f (s y) = y := fun y => LinearMap.congr_fun hs y
  let π : M →ₗ[R] LinearMap.ker f := (LinearMap.id - s ∘ₗ f).codRestrict (LinearMap.ker f) (fun x => by
    simp [hs'])
  have hπ : π ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    simp [π, LinearMap.mem_ker.1 x.2]
  have hK : Subsingleton (IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f) := by
    have key : ∀ z : IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f, z = 0 := fun z => by
      have h0 : f ∘ₗ (LinearMap.ker f).subtype = 0 := by
        ext x
        simp
      have h1 : (LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z = 0 := by
        apply h.1
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero, map_zero]
        rfl
      have h2 : π.lTensor (IsLocalRing.ResidueField R) ((LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z) = z := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπ, LinearMap.lTensor_id]
        rfl
      rw [← h2, h1, map_zero]
    exact ⟨fun x y => by rw [key x, key y]⟩
  have hK' : Subsingleton (LinearMap.ker f) := IsLocalRing.subsingleton_tensorProduct.1 hK
  refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, hsurj⟩
  have h3 : (⟨x, hx⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h3

/- English proof (translation)
Take `⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩` from `GlobalTheory.T.finite_scheme_map_from_special_fibre R A B b`. Use `h3 inferInstance` as an intermediate fact. Establish `h' : Flat (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom))`. Establish `: Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) = i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ j₀.hom`. Rewrite using `[e2]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `infer_instance`. Rewrite `h'` using `[Flat.SpecMap_iff]`. Establish `h'' : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom))`.

Rewrite using `[Flat.SpecMap_iff]`. Conclude with `GlobalTheory.T.flat_of_flat_special_fibre R Q P φ h'`. Rewrite using `[e1]`. Use `infer_instance`.
-/
theorem flat_left_of_fibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Over (Spec (CommRingCat.of R))) [IsFinite A.hom] [IsFinite B.hom] [Flat A.hom] (b : A ⟶ B)
    (h : Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) : Flat b.left := by
  obtain ⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩ := GlobalTheory.T.finite_scheme_map_from_special_fibre R A B b
  have := h3 inferInstance
  have h' : Flat (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) =
        i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ j₀.hom := by
      rw [e2]; simp
    rw [this]; infer_instance
  rw [Flat.SpecMap_iff] at h'
  have h'' : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    rw [Flat.SpecMap_iff]
    exact GlobalTheory.T.flat_of_flat_special_fibre R Q P φ h'
  rw [e1]; infer_instance

/- English proof (translation)
Take `⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩` from `GlobalTheory.T.finite_scheme_map_from_special_fibre R C K u`. Use `h3 inferInstance` as an intermediate fact. Establish `h0 : IsIso ((Over.forget _).map ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u))` using `inferInstance`. Establish `h0' : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left` using `h0`. Establish `h' : IsIso (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom))`.

Establish `: Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) = i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left ≫ j₀.hom`. Rewrite using `[e2]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `infer_instance`.

Establish `h2' : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ)` using `isIso_SpecMap_iff.1 h'`. Establish `hco : ⇑(φ.toLinearMap.lTensor (IsLocalRing.ResidueField R)) = ⇑(Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ)`. Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hφ : Function.Bijective φ` using `bijective_of_lTensor R Q P φ.toLinearMap (by rw [hco]; exact h2')`. Establish `hS : IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom))` using `isIso_SpecMap_iff.2 hφ`. Establish `hl : IsIso u.left` using `by rw [e1]; infer_instance`.

Use `haveI : IsIso ((Over.forget _).map u) := hl`. Conclude with `isIso_of_reflects_iso u (Over.forget _)`.
-/
theorem isIso_of_fibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C K : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite K.hom] [Flat C.hom] (u : C ⟶ K)
    (h : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)) : IsIso u := by
  obtain ⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩ := GlobalTheory.T.finite_scheme_map_from_special_fibre R C K u
  have := h3 inferInstance
  have h0 : IsIso ((Over.forget _).map ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)) := inferInstance
  have h0' : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left := h0
  have h' : IsIso (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) =
        i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left ≫ j₀.hom := by
      rw [e2]; simp
    rw [this]; infer_instance
  have h2' : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ) :=
    isIso_SpecMap_iff.1 h'
  have hco : ⇑(φ.toLinearMap.lTensor (IsLocalRing.ResidueField R)) =
      ⇑(Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hφ : Function.Bijective φ :=
    bijective_of_lTensor R Q P φ.toLinearMap (by rw [hco]; exact h2')
  have hS : IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom)) := isIso_SpecMap_iff.2 hφ
  have hl : IsIso u.left := by rw [e1]; infer_instance
  haveI : IsIso ((Over.forget _).map u) := hl
  exact isIso_of_reflects_iso u (Over.forget _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x`. Establish `hsp : SpecializingMap B.hom` using `B.hom.isClosedMap.specializingMap`. Take `⟨y, hxy, hy⟩` from `hsp (IsLocalRing.specializes_closedPoint (B.hom x))`. Establish `: Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))`.

Rewrite using `[Ideal.Quotient.nontrivial_iff]`. Simplify using `using (IsLocalRing.maximalIdeal.isMaximal R).ne_top`. Take `⟨t⟩ : Nonempty (Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))))` from `inferInstance`. Establish `ht : thick R (IsLocalRing.maximalIdeal R) 0 t = IsLocalRing.closedPoint R`. Establish `hle : IsLocalRing.maximalIdeal R ≤ (thick R (IsLocalRing.maximalIdeal R) 0 t).asIdeal` using `fun x hx => by show Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)) x ∈ t.asIdeal`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hx)]`. Conclude with `zero_mem _`. Conclude with `PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (thick R (IsLocalRing.maximalIdeal R) 0 t).isPrime.ne_top) hle)`. Take `⟨y₀, hy₀, -⟩` from `Scheme.Pullback.exists_preimage_pullback y t (hy.trans ht.symm)`. Take `⟨z₀, hz₀⟩` from `h.surj y₀`.

Establish `hcomp : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ pullback.fst B.hom (thick R (IsLocalRing.maximalIdeal R) 0) = pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) ≫ b.left` using `pullback.lift_fst _ _ _`. Establish `hz : b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) = y`. Rewrite using `[← hy₀, ← hz₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]`. Take `⟨w, -, hw⟩` from `Flat.generalizingMap b.left (show x ⤳ b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) by rwa [hz])`. Conclude with `⟨w, hw⟩`.
-/
theorem surjective_left_of_fibre (R : Type) [CommRing R] [IsLocalRing R] (A B : Over (Spec (CommRingCat.of R))) [IsFinite B.hom] (b : A ⟶ B) [Flat b.left]
    (h : Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) : Surjective b.left := by
  constructor
  intro x
  have hsp : SpecializingMap B.hom := B.hom.isClosedMap.specializingMap
  obtain ⟨y, hxy, hy⟩ := hsp (IsLocalRing.specializes_closedPoint (B.hom x))
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) := by
    rw [Ideal.Quotient.nontrivial_iff]; simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))) := inferInstance
  have ht : thick R (IsLocalRing.maximalIdeal R) 0 t = IsLocalRing.closedPoint R := by
    have hle : IsLocalRing.maximalIdeal R ≤ (thick R (IsLocalRing.maximalIdeal R) 0 t).asIdeal := fun x hx => by
      show Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)) x ∈ t.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hx)]
      exact zero_mem _
    exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (thick R (IsLocalRing.maximalIdeal R) 0 t).isPrime.ne_top) hle)
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback y t (hy.trans ht.symm)
  obtain ⟨z₀, hz₀⟩ := h.surj y₀
  have hcomp : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ pullback.fst B.hom (thick R (IsLocalRing.maximalIdeal R) 0) =
      pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) ≫ b.left := pullback.lift_fst _ _ _
  have hz : b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) = y := by
    rw [← hy₀, ← hz₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]
  obtain ⟨w, -, hw⟩ := Flat.generalizingMap b.left (show x ⤳ b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) by rwa [hz])
  exact ⟨w, hw⟩

/- English proof (translation)
Establish `hb : Flat b.left` using `flat_left_of_fibre R A B b hf`. Establish `hK : IsPullback (pullback.fst b e) (toUnit (pullback b e)) b e`. Establish `h` using `IsPullback.of_hasPullback b e`. Rewrite `h` using `[toUnit_unique (pullback.snd _ _) (toUnit _)]`. Then use the resulting hypothesis. Establish `hKl` using `hK.map (Over.forget _)`.

Establish `hKl' : IsPullback (pullback.fst b e).left (pullback b e).hom b.left e.left`. Establish `hA : (toUnit (pullback b e)).left = (pullback b e).hom` using `by simpa using Over.w (toUnit (pullback b e))`. Rewrite using `[← hA]`. Conclude with `hKl`. Establish `hbfin : IsFinite b.left`.

Establish `: IsFinite (b.left ≫ B.hom)` using `by rw [Over.w b]; infer_instance`. Conclude with `IsFinite.of_comp b.left B.hom`. Establish `hKfin : IsFinite (pullback b e).hom`. Establish `h1 : IsFinite (pullback b e).hom` using `MorphismProperty.of_isPullback hKl' ‹_›`. Conclude with `h1`.

Establish `hclosed : IsClosedImmersion (pullback.fst b e).left`. Establish `he : IsClosedImmersion e.left`. Establish `: IsClosedImmersion (e.left ≫ B.hom)`. Establish `: e.left ≫ B.hom = 𝟙 _` using `by simpa using Over.w e`. Rewrite using `[this]`.

Use `infer_instance`. Conclude with `IsClosedImmersion.of_comp _ B.hom`. Conclude with `MorphismProperty.of_isPullback hKl'.flip he`. Set `u : C ⟶ pullback b e` to `hK.lift a (toUnit C) hab`. Establish `hu1 : u ≫ pullback.fst b e = a` using `hK.lift_fst _ _ _`.

Establish `hu0 : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)`. Establish `hK0` using `hK.map (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0))`. Establish `: (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u = (h₀.isoIsPullback _ _ hK0).hom`. Apply `hK0.hom_ext` to reduce the goal to its premises. Rewrite using `[IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp, hu1]`.

Rewrite using `[IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp, toUnit_unique (u ≫ toUnit _) (toUnit C)]`. Rewrite using `[this]`. Use `infer_instance`. Establish `hu : IsIso u` using `isIso_of_fibre R C _ u hu0`. Use `⟨?_, hb, surjective_left_of_fibre R A B b hs, ?_⟩` and prove the remaining obligations.

Establish `: IsIso u.left` using `inferInstanceAs (IsIso ((Over.forget _).map u))`. Rewrite using `[← hu1, Over.comp_left]`. Use `infer_instance`. Conclude with `IsPullback.of_iso hK (asIso u).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hu1]) (by simp) (by simp) (by simp)`.
-/
theorem main (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C A B : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite A.hom] [IsFinite B.hom] [Flat C.hom] [Flat A.hom] [Flat B.hom] (a : C ⟶ A) (b : A ⟶ B) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (hab : a ≫ b = toUnit C ≫ e)
  (h₀ : IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map (toUnit C)) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map e))
  (hf : Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left)
  (hs : Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) :
  IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit C) b e := by
  have hb : Flat b.left := flat_left_of_fibre R A B b hf
  have hK : IsPullback (pullback.fst b e) (toUnit (pullback b e)) b e := by
    have h := IsPullback.of_hasPullback b e
    rwa [toUnit_unique (pullback.snd _ _) (toUnit _)] at h
  have hKl := hK.map (Over.forget _)
  have hKl' : IsPullback (pullback.fst b e).left (pullback b e).hom b.left e.left := by
    have hA : (toUnit (pullback b e)).left = (pullback b e).hom := by simpa using Over.w (toUnit (pullback b e))
    rw [← hA]; exact hKl
  have hbfin : IsFinite b.left := by
    have : IsFinite (b.left ≫ B.hom) := by rw [Over.w b]; infer_instance
    exact IsFinite.of_comp b.left B.hom
  have hKfin : IsFinite (pullback b e).hom := by
    have h1 : IsFinite (pullback b e).hom := MorphismProperty.of_isPullback hKl' ‹_›
    exact h1
  have hclosed : IsClosedImmersion (pullback.fst b e).left := by
    have he : IsClosedImmersion e.left := by
      have : IsClosedImmersion (e.left ≫ B.hom) := by
        have : e.left ≫ B.hom = 𝟙 _ := by simpa using Over.w e
        rw [this]; infer_instance
      exact IsClosedImmersion.of_comp _ B.hom
    exact MorphismProperty.of_isPullback hKl'.flip he
  let u : C ⟶ pullback b e := hK.lift a (toUnit C) hab
  have hu1 : u ≫ pullback.fst b e = a := hK.lift_fst _ _ _
  have hu0 : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u) := by
    have hK0 := hK.map (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0))
    have : (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u = (h₀.isoIsPullback _ _ hK0).hom := by
      apply hK0.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp, hu1]
      · rw [IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp, toUnit_unique (u ≫ toUnit _) (toUnit C)]
    rw [this]; infer_instance
  have hu : IsIso u := isIso_of_fibre R C _ u hu0
  refine ⟨?_, hb, surjective_left_of_fibre R A B b hs, ?_⟩
  · have : IsIso u.left := inferInstanceAs (IsIso ((Over.forget _).map u))
    rw [← hu1, Over.comp_left]; infer_instance
  · exact IsPullback.of_iso hK (asIso u).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hu1]) (by simp) (by simp) (by simp)

/- English proof (translation)
Introduce `R _ _ _ C A B _ _ _ _ _ _ a b e hab h₀ hf hs`. Conclude with `main R C A B a b e hab h₀ hf hs`.
-/
theorem exact_of_closedFibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C A B : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite A.hom] [IsFinite B.hom] [Flat C.hom] [Flat A.hom] [Flat B.hom] (a : C ⟶ A) (b : A ⟶ B) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B), a ≫ b = toUnit C ≫ e → IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map (toUnit C)) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map e) → Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left → Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left → IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit C) b e := by
  intro R _ _ _ C A B _ _ _ _ _ _ a b e hab h₀ hf hs
  exact main R C A B a b e hab h₀ hf hs

end GlobalTheory.CompanionTheory.Ar.BT.FinFlat
