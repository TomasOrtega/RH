import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.AbelianImage

/- English proof (translation)
Set `Z : TopologicalSpace.Closeds G.left` to `⟨Set.range ν.left, ν.left.isClosedEmbedding.isClosed_range⟩`. Establish `h2 : ν.left.ker ≤ g.left.ker` using `(Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 (show Z ≤ ν.left.ker.support from ν.left.range_subset_ker_support)).trans (ReducedSubgroup.vanishingIdeal_le_ker g.left Z h)`. Establish `h3` using `IsClosedImmersion.lift_fac ν.left g.left h2`. Use `⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w ν, ← Category.assoc, h3, Over.w]`.

Use `ext1`. Conclude with `h3`.
-/
theorem exists_lift {S : Scheme.{0}} {T N G : Over S} [IsReduced T.left] (ν : N ⟶ G)
    [IsClosedImmersion ν.left] (g : T ⟶ G) (h : Set.range g.left ⊆ Set.range ν.left) :
    ∃ l : T ⟶ N, l ≫ ν = g := by
  let Z : TopologicalSpace.Closeds G.left :=
    ⟨Set.range ν.left, ν.left.isClosedEmbedding.isClosed_range⟩
  have h2 : ν.left.ker ≤ g.left.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1
      (show Z ≤ ν.left.ker.support from ν.left.range_subset_ker_support)).trans
      (ReducedSubgroup.vanishingIdeal_le_ker g.left Z h)
  have h3 := IsClosedImmersion.lift_fac ν.left g.left h2
  refine ⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩
  · rw [← Over.w ν, ← Category.assoc, h3, Over.w]
  · ext1
    exact h3

/- English proof (translation)
Use `⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩` and prove the remaining obligations. Establish `: ConnectedSpace ↥(pullback (p ≫ f) x)` using `GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)`. Set `q` to `(pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)`. Establish `: Surjective q` using `inferInstance`. Conclude with `q.surjective.connectedSpace q.continuous`.
-/
theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

/- English proof (translation)
Take `⟨x⟩ : Nonempty X` from `inferInstance`. Take `⟨A', j', hj', ⟨y, hy⟩, -⟩` from `Scheme.exists_affine_mem_range_and_range_subset (x := p x) (U := ⊤) trivial`. Take `⟨A, j, hj, ⟨z, hz⟩, hr⟩` from `Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := p ⁻¹ᵁ j'.opensRange) ⟨y, hy⟩`. Establish `hrange : Set.range (j ≫ p) ⊆ Set.range j'`. Introduce and unpack `_ ⟨t, rfl⟩`.

Conclude with `hr ⟨t, rfl⟩`. Establish `hl` using `IsOpenImmersion.lift_fac j' (j ≫ p) hrange`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (IsOpenImmersion.lift j' (j ≫ p) hrange)`. Take `⟨α, hα⟩` from `Spec.map_surjective (j' ≫ f)`. Rewrite `hl` using `[← hφ]`.

Establish `: Nonempty (Spec A)` using `⟨z⟩`. Establish `: Nonempty (Spec A')` using `⟨y⟩`. Establish `: IsIntegral (Spec A)` using `isIntegral_of_isOpenImmersion j`. Establish `: IsIntegral (Spec A')` using `isIntegral_of_isOpenImmersion j'`. Establish `: IsDomain A` using `(affine_isIntegral_iff A).1 inferInstance`.

Establish `: IsDomain A'` using `(affine_isIntegral_iff A').1 inferInstance`. Establish `: IsDominant j` using `⟨j.isOpenEmbedding.isOpen_range.dense ⟨_, z, rfl⟩⟩`. Establish `: IsDominant (Spec.map φ ≫ j')` using `by rw [hl]; infer_instance`. Establish `hd : IsDominant (Spec.map φ)` using `IsDominant.of_comp_of_isOpenImmersion _ j'`. Establish `hinj : Function.Injective φ.hom`.

Establish `h1` using `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).1 hd.1`. Rewrite `h1` using `[nilradical_eq_zero]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h1)`. Use `letI : Algebra k A' := α.hom.toAlgebra`. Use `letI : Algebra k A := (α ≫ φ).hom.toAlgebra`.

Establish `h1` using `trdeg_eq_of_smoothOfRelativeDimension k Y f b hb A' j' hj' hα.symm`. Establish `h2` using `trdeg_eq_of_smoothOfRelativeDimension k X (p ≫ f) a ha A j hj (by`. Rewrite using `[← Category.assoc, ← hl, Category.assoc, ← hα, ← Spec.map_comp]`. Use the proof step `rfl)`. Establish `h3` using `trdeg_le_of_injective (R := k) (A := A') (A' := A) ⟨φ.hom, fun _ => rfl⟩ hinj`.

Rewrite `h3` using `[h1, h2]`. Conclude with `h3` after adjusting the coercions.
-/
theorem relDim_le_of_isDominant {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Y) [IsDominant p] (f : Y ⟶ Spec (.of k)) {a b : ℕ}
    (ha : SmoothOfRelativeDimension a (p ≫ f)) (hb : SmoothOfRelativeDimension b f) : b ≤ a := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨A', j', hj', ⟨y, hy⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := p x) (U := ⊤) trivial
  obtain ⟨A, j, hj, ⟨z, hz⟩, hr⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := p ⁻¹ᵁ j'.opensRange) ⟨y, hy⟩
  have hrange : Set.range (j ≫ p) ⊆ Set.range j' := by
    rintro _ ⟨t, rfl⟩
    exact hr ⟨t, rfl⟩
  have hl := IsOpenImmersion.lift_fac j' (j ≫ p) hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j' (j ≫ p) hrange)
  obtain ⟨α, hα⟩ := Spec.map_surjective (j' ≫ f)
  rw [← hφ] at hl
  have : Nonempty (Spec A) := ⟨z⟩
  have : Nonempty (Spec A') := ⟨y⟩
  have : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec A') := isIntegral_of_isOpenImmersion j'
  have : IsDomain A := (affine_isIntegral_iff A).1 inferInstance
  have : IsDomain A' := (affine_isIntegral_iff A').1 inferInstance
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense ⟨_, z, rfl⟩⟩
  have : IsDominant (Spec.map φ ≫ j') := by rw [hl]; infer_instance
  have hd : IsDominant (Spec.map φ) := IsDominant.of_comp_of_isOpenImmersion _ j'
  have hinj : Function.Injective φ.hom := by
    have h1 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).1 hd.1
    rw [nilradical_eq_zero] at h1
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h1)
  letI : Algebra k A' := α.hom.toAlgebra
  letI : Algebra k A := (α ≫ φ).hom.toAlgebra
  have h1 := trdeg_eq_of_smoothOfRelativeDimension k Y f b hb A' j' hj' hα.symm
  have h2 := trdeg_eq_of_smoothOfRelativeDimension k X (p ≫ f) a ha A j hj (by
    rw [← Category.assoc, ← hl, Category.assoc, ← hα, ← Spec.map_comp]; rfl)
  have h3 := trdeg_le_of_injective (R := k) (A := A') (A' := A) ⟨φ.hom, fun _ => rfl⟩ hinj
  rw [h1, h2] at h3
  exact_mod_cast h3

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] [BraidedCategory 𝒞]

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]`.
-/
theorem isCommMonObj_of_mono {N G : 𝒞} [MonObj N] [MonObj G] [IsCommMonObj G] (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] : IsCommMonObj N := by
  refine ⟨?_⟩
  rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

omit [BraidedCategory 𝒞] in

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono ν, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]`. Rewrite using `[← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]`.
-/
theorem isMonHom_of_comp_mono {M N G : 𝒞} [MonObj M] [MonObj N] [MonObj G] (l : M ⟶ N) (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] [IsMonHom (l ≫ ν)] : IsMonHom l := by
  refine ⟨?_, ?_⟩
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end Cat

open RationalPoint in

/- English proof (translation)
Introduce `k _ _ G _ hG B _ hB ψ hψ`. Take `⟨hc, hs, hsep, -, -⟩` from `hG`. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Use `hB.geomConnected` as an intermediate fact.

Establish `: IsProper (ψ.left ≫ G.hom)` using `by rw [Over.w ψ]; infer_instance`. Establish `: IsProper ψ.left` using `IsProper.of_comp ψ.left G.hom`. Establish `hZ : IsClosed (Set.range ψ.left)` using `ψ.left.isClosedMap.isClosed_range`. Set `φ : (𝟙_ (Over (Sp k)) ⟶ B) →* (𝟙_ (Over (Sp k)) ⟶ G)` to `MonoidHom.mk' (fun x => x ≫ ψ) fun x y => MonObj.mul_comp x y ψ`. Establish `hC : ∀ x, x ∈ φ.range ↔ Set.range x.left ⊆ Set.range ψ.left` using `fun x => by`.

Rewrite using `[range_left_subset_iff, ← Set.image_univ, pt_mem_image_iff ψ isClosed_univ]`. Simplify using `only [Set.mem_univ, true_and]`. Both sides reduce to the same expression. Take `⟨N, _, ν, hν, hcl, hsm, hr⟩` from `ReducedSubgroup.exists_smooth_closed_subgroup k G inferInstance φ.range _ hZ hC`. Establish `: ConnectedSpace B.left` using `GeometricallyConnected.connectedSpace_of_subsingleton B.hom`.

Establish `: IsIntegral B.left` using `isIntegral_of_smooth_field_of_connectedSpace B.hom`. Take `⟨π, hπ⟩` from `exists_lift ν ψ hr.ge`. Establish `: Surjective π.left` using `⟨fun y => by`. Take `⟨x, hx⟩` from `hr.le ⟨y, rfl⟩`. Use `⟨x, ν.left.isClosedEmbedding.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[← hx, ← hπ]`. Use the proof step `rfl⟩`. Establish `: Mono ν` using `(Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))`. Establish `: ConnectedSpace N.left` using `π.left.surjective.connectedSpace π.left.continuous`. Establish `: IsIntegral N.left` using `isIntegral_of_smooth_field_of_connectedSpace N.hom`.

Establish `hw : π.left ≫ N.hom = B.hom` using `Over.w π`. Establish `: IsSeparated N.hom` using `by rw [← Over.w ν]; infer_instance`. Establish `: UniversallyClosed (π.left ≫ N.hom)` using `by rw [hw]; infer_instance`. Establish `: UniversallyClosed N.hom` using `UniversallyClosed.of_comp_surjective π.left N.hom`. Establish `: GeometricallyConnected (π.left ≫ N.hom)` using `by rw [hw]; infer_instance`.

Establish `hN : IsAbelianScheme N` using `⟨isCommMonObj_of_mono ν, hsm, ⟨⟩, geometricallyConnected_of_surjective π.left N.hom⟩`. Use `⟨N, inferInstance, ν, π, hN, hν, hcl, hπ, fun F hF h => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : Set.range (ψ ≫ F).left ⊆ Set.range ψ.left` using `ReducedSubgroup.range_subset_of_points (ψ ≫ F) hZ fun x => by`. Take `⟨y, hy⟩` from `h x`. Conclude with `(hC _).1 ⟨y, hy.symm⟩`.

Take `⟨F', hF'⟩` from `exists_lift ν (ν ≫ F) (by`. Introduce and unpack `_ ⟨t, rfl⟩`. Take `⟨x, hx⟩` from `hr.le ⟨t, rfl⟩`. Use `hr.ge (h1 ⟨x, ?_⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F.left (ψ.left x) = F.left (ν.left t)`.

Rewrite using `[hx])`. Establish `: IsMonHom (F' ≫ ν)` using `by rw [hF']; infer_instance`. Conclude with `⟨F', isMonHom_of_comp_mono F' ν, hF'⟩`. Take `⟨b, hb⟩` from `AbelianDim.exists_relDim k N hN`. Conclude with `⟨b, relDim_le_of_isDominant π.left N.hom (hw ▸ ha) hb, hb⟩`.
-/
theorem exists_image : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ ψ : B ⟶ G, IsMonHom ψ → ∃ (B' : Over (Sp k)) (_ : GrpObj B') (ν : B' ⟶ G) (π : B ⟶ B'), IsAbelianScheme B' ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ π ≫ ν = ψ ∧ (∀ F : G ⟶ G, IsMonHom F → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), ∃ y : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ψ ≫ F = y ≫ ψ) → ∃ F' : B' ⟶ B', IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ a, SmoothOfRelativeDimension a B.hom → ∃ a', a' ≤ a ∧ SmoothOfRelativeDimension a' B'.hom := by
  intro k _ _ G _ hG B _ hB ψ hψ
  obtain ⟨hc, hs, hsep, -, -⟩ := hG
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : IsProper (ψ.left ≫ G.hom) := by rw [Over.w ψ]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have hZ : IsClosed (Set.range ψ.left) := ψ.left.isClosedMap.isClosed_range
  let φ : (𝟙_ (Over (Sp k)) ⟶ B) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  have hC : ∀ x, x ∈ φ.range ↔ Set.range x.left ⊆ Set.range ψ.left := fun x => by
    rw [range_left_subset_iff, ← Set.image_univ, pt_mem_image_iff ψ isClosed_univ]
    simp only [Set.mem_univ, true_and]
    rfl
  obtain ⟨N, _, ν, hν, hcl, hsm, hr⟩ := ReducedSubgroup.exists_smooth_closed_subgroup k G
    inferInstance φ.range _ hZ hC
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have : IsIntegral B.left := isIntegral_of_smooth_field_of_connectedSpace B.hom
  obtain ⟨π, hπ⟩ := exists_lift ν ψ hr.ge
  have : Surjective π.left := ⟨fun y => by
    obtain ⟨x, hx⟩ := hr.le ⟨y, rfl⟩
    refine ⟨x, ν.left.isClosedEmbedding.injective ?_⟩
    rw [← hx, ← hπ]
    rfl⟩
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have : ConnectedSpace N.left := π.left.surjective.connectedSpace π.left.continuous
  have : IsIntegral N.left := isIntegral_of_smooth_field_of_connectedSpace N.hom
  have hw : π.left ≫ N.hom = B.hom := Over.w π
  have : IsSeparated N.hom := by rw [← Over.w ν]; infer_instance
  have : UniversallyClosed (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed N.hom := UniversallyClosed.of_comp_surjective π.left N.hom
  have : GeometricallyConnected (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have hN : IsAbelianScheme N := ⟨isCommMonObj_of_mono ν, hsm, ⟨⟩,
    geometricallyConnected_of_surjective π.left N.hom⟩
  refine ⟨N, inferInstance, ν, π, hN, hν, hcl, hπ, fun F hF h => ?_, fun a ha => ?_⟩
  · have h1 : Set.range (ψ ≫ F).left ⊆ Set.range ψ.left :=
      ReducedSubgroup.range_subset_of_points (ψ ≫ F) hZ fun x => by
        obtain ⟨y, hy⟩ := h x
        exact (hC _).1 ⟨y, hy.symm⟩
    obtain ⟨F', hF'⟩ := exists_lift ν (ν ≫ F) (by
      rintro _ ⟨t, rfl⟩
      obtain ⟨x, hx⟩ := hr.le ⟨t, rfl⟩
      refine hr.ge (h1 ⟨x, ?_⟩)
      change F.left (ψ.left x) = F.left (ν.left t)
      rw [hx])
    have : IsMonHom (F' ≫ ν) := by rw [hF']; infer_instance
    exact ⟨F', isMonHom_of_comp_mono F' ν, hF'⟩
  · obtain ⟨b, hb⟩ := AbelianDim.exists_relDim k N hN
    exact ⟨b, relDim_le_of_isDominant π.left N.hom (hw ▸ ha) hb, hb⟩

end GlobalTheory.AbelianImage
