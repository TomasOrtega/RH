import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ReducedSubgroup

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]

/- English proof (translation)
Establish `hl : ∀ {T : 𝒞} (a b : T ⟶ N), lift a b ≫ m ≫ ν = (a ≫ ν) * (b ≫ ν)`. Introduce `T a b`. Rewrite using `[hm, lift_map_assoc, Hom.mul_def]`. Establish `hm' : m ≫ ν = (fst N N ≫ ν) * (snd N N ≫ ν)`. Rewrite using `[← hl, lift_fst_snd, Category.id_comp]`.

Establish `he' : ∀ {T : 𝒞} (a : T ⟶ 𝟙_ 𝒞), a ≫ e ≫ ν = 1`. Introduce `T a`. Rewrite using `[he, Hom.one_def, toUnit_unique a (toUnit T)]`. Establish `hi' : i ≫ ν = ν⁻¹` using `by rw [hi, Hom.inv_def]`. Use `letI M : MonObj N := { one := e mul := m one_mul := by`.

Rewrite using `[← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, he', _root_.one_mul, leftUnitor_hom]`. Use `mul_one := by`. Rewrite using `[← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, he', _root_.mul_one, rightUnitor_hom]`. Use `mul_assoc := by`. Rewrite using `[← cancel_mono ν]`.

Simplify using `only [Category.assoc]`. Use `conv_lhs => rw [hm', comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, hm', comp_mul]`. Use `conv_rhs => rw [hm', comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hm', comp_mul, comp_mul, comp_mul]`. Simplify using `[_root_.mul_assoc] }`. Use `⟨{ inv := i, left_inv := ?_, right_inv := ?_ }, ⟨he, hm⟩⟩` and prove the remaining obligations.

Rewrite using `[← cancel_mono ν, Category.assoc, Category.assoc]`. Conclude with `(hl i (𝟙 N)).trans (by rw [hi', Category.id_comp, inv_mul_cancel]; exact (he' _).symm)`. Rewrite using `[← cancel_mono ν, Category.assoc, Category.assoc]`. Conclude with `(hl (𝟙 N) i).trans (by rw [hi', Category.id_comp, mul_inv_cancel]; exact (he' _).symm)`.
-/
theorem exists_grpObj_of_mono {N B : 𝒞} [GrpObj B] (ν : N ⟶ B) [Mono ν] (e : 𝟙_ 𝒞 ⟶ N)
    (m : N ⊗ N ⟶ N) (i : N ⟶ N) (he : e ≫ ν = η[B]) (hm : m ≫ ν = (ν ⊗ₘ ν) ≫ μ[B])
    (hi : i ≫ ν = ν ≫ GrpObj.inv) : ∃ _ : GrpObj N, IsMonHom ν := by
  have hl : ∀ {T : 𝒞} (a b : T ⟶ N), lift a b ≫ m ≫ ν = (a ≫ ν) * (b ≫ ν) := by
    intro T a b
    rw [hm, lift_map_assoc, Hom.mul_def]
  have hm' : m ≫ ν = (fst N N ≫ ν) * (snd N N ≫ ν) := by
    rw [← hl, lift_fst_snd, Category.id_comp]
  have he' : ∀ {T : 𝒞} (a : T ⟶ 𝟙_ 𝒞), a ≫ e ≫ ν = 1 := by
    intro T a
    rw [he, Hom.one_def, toUnit_unique a (toUnit T)]
  have hi' : i ≫ ν = ν⁻¹ := by rw [hi, Hom.inv_def]
  letI M : MonObj N :=
    { one := e
      mul := m
      one_mul := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerRight_fst_assoc,
          whiskerRight_snd_assoc, he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono ν]
        simp only [Category.assoc]
        conv_lhs => rw [hm', comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, hm',
          comp_mul]
        conv_rhs => rw [hm', comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hm',
          comp_mul, comp_mul, comp_mul]
        simp [_root_.mul_assoc] }
  refine ⟨{ inv := i, left_inv := ?_, right_inv := ?_ }, ⟨he, hm⟩⟩
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl i (𝟙 N)).trans (by rw [hi', Category.id_comp, inv_mul_cancel]; exact (he' _).symm)
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl (𝟙 N) i).trans (by rw [hi', Category.id_comp, mul_inv_cancel]; exact (he' _).symm)

end Cat

section Reduced

universe u

open Scheme.IdealSheafData in

/- English proof (translation)
Establish `: ∀ U, IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U)` using `fun U => by`. Use `(affine_isReduced_iff (.of (Γ(X, U.1) ⧸ (vanishingIdeal Z).ideal U))).mpr ?_` and prove the remaining obligations. Use `(Ideal.isRadical_iff_quotient_reduced _).mp ?_` and prove the remaining obligations. Conclude with `PrimeSpectrum.isRadical_vanishingIdeal _`. Conclude with `IsReduced.of_openCover _ (vanishingIdeal Z).subschemeCover.openCover`.
-/
theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have : ∀ U, IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ (vanishingIdeal Z).ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact IsReduced.of_openCover _ (vanishingIdeal Z).subschemeCover.openCover

open Scheme.IdealSheafData in

/- English proof (translation)
Use `le_ofIdeals_iff.mpr fun U a ha => ?_` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]`. Introduce `t ht`. Establish `h1 : g t ∈ (vanishingIdeal Z).support` using `h ⟨t, rfl⟩`. Establish `h2` using `((coe_support_inter (vanishingIdeal Z) U).le ⟨h1, X.basicOpen_le a ht⟩).1`.

Conclude with `((Scheme.mem_zeroLocus_iff _ _ _).mp h2 a ha ht).elim`.
-/
theorem vanishingIdeal_le_ker {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X)
    (Z : TopologicalSpace.Closeds X) (h : Set.range g ⊆ Z) : vanishingIdeal Z ≤ g.ker := by
  refine le_ofIdeals_iff.mpr fun U a ha => ?_
  rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
  intro t ht
  have h1 : g t ∈ (vanishingIdeal Z).support := h ⟨t, rfl⟩
  have h2 := ((coe_support_inter (vanishingIdeal Z) U).le
    ⟨h1, X.basicOpen_le a ht⟩).1
  exact ((Scheme.mem_zeroLocus_iff _ _ _).mp h2 a ha ht).elim

/- English proof (translation)
Use `⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ => ?_⟩` and prove the remaining obligations. Set `𝒰` to `Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`. Establish `: ∀ i, IsReduced (𝒰.X i)` using `fun i => by`. Use `X.affineOpenCover.map_prop i` as an intermediate fact. Establish `h0 : IsReduced (Spec (X.affineOpenCover.X i))` using `isReduced_of_isOpenImmersion (X.affineOpenCover.f i)`.

Establish `h1` using `(affine_isReduced_iff _).mp h0`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (X.affineOpenCover.f i ≫ f)`. Express the relevant statement in the definitionally equal form `IsReduced (pullback (X.affineOpenCover.f i ≫ f) _)`. Rewrite using `[← hφ]`. Use `letI : Algebra k (X.affineOpenCover.X i) := φ.hom.toAlgebra`.

Establish `h2` using `ReducedAlg.isReduced_tensor (k := k) (X.affineOpenCover.X i) K`. Establish `h3` using `(affine_isReduced_iff (.of (TensorProduct k (X.affineOpenCover.X i) K))).mpr h2`. Conclude with `isReduced_of_isOpenImmersion (pullbackSpecIso k (X.affineOpenCover.X i) K).hom`. Conclude with `IsReduced.of_openCover _ 𝒰`.
-/
theorem geometricallyReduced_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of k)) : GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ => ?_⟩
  let 𝒰 := Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := X.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (X.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (X.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (X.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra k (X.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 := ReducedAlg.isReduced_tensor (k := k) (X.affineOpenCover.X i) K
    have h3 := (affine_isReduced_iff
      (.of (TensorProduct k (X.affineOpenCover.X i) K))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso k (X.affineOpenCover.X i) K).hom
  exact IsReduced.of_openCover _ 𝒰

end Reduced

/- English proof (translation)
Use `LocallyOfFiniteType.jacobsonSpace T.hom` as an intermediate fact. Introduce and unpack `_ ⟨t, rfl⟩`. Assume the negation of the conclusion as `ht`. Take `⟨x, hx, hxc⟩` from `nonempty_inter_closedPoints (Z := (g.left ⁻¹' Z)ᶜ) ⟨t, ht⟩ (hZ.preimage g.left.continuous).isOpen_compl.isLocallyClosed`. Set `x' : 𝟙_ (Over (Sp k)) ⟶ T` to `Over.homMk (pointOfClosedPoint T.hom x hxc) (pointOfClosedPoint_comp T.hom x hxc)`.

Use `hx (h x' ⟨IsLocalRing.closedPoint k, ?_⟩)` and prove the remaining obligations. Conclude with `congrArg g.left (pointOfClosedPoint_apply T.hom x hxc _)`.
-/
theorem range_subset_of_points {k : Type} [Field k] [IsAlgClosed k] {T B : Over (Sp k)}
    [LocallyOfFiniteType T.hom] (g : T ⟶ B) {Z : Set B.left} (hZ : IsClosed Z)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ T, Set.range (x ≫ g).left ⊆ Z) : Set.range g.left ⊆ Z := by
  have := LocallyOfFiniteType.jacobsonSpace T.hom
  rintro _ ⟨t, rfl⟩
  by_contra ht
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Z := (g.left ⁻¹' Z)ᶜ) ⟨t, ht⟩
    (hZ.preimage g.left.continuous).isOpen_compl.isLocallyClosed
  let x' : 𝟙_ (Over (Sp k)) ⟶ T :=
    Over.homMk (pointOfClosedPoint T.hom x hxc) (pointOfClosedPoint_comp T.hom x hxc)
  refine hx (h x' ⟨IsLocalRing.closedPoint k, ?_⟩)
  exact congrArg g.left (pointOfClosedPoint_apply T.hom x hxc _)

open Scheme.IdealSheafData in

/- English proof (translation)
Set `I : B.left.IdealSheafData` to `vanishingIdeal ⟨Z, hZ⟩`. Set `N : Over (Sp k)` to `Over.mk (I.subschemeι ≫ B.hom)`. Set `ν : N ⟶ B` to `Over.homMk I.subschemeι rfl`. Establish `hν : IsClosedImmersion ν.left` using `inferInstanceAs (IsClosedImmersion I.subschemeι)`. Establish `hr : Set.range ν.left = Z`.

Express the relevant statement in the definitionally equal form `Set.range I.subschemeι = Z`. Rewrite using `[range_subschemeι]`. Both sides reduce to the same expression. Establish `: Mono ν` using `(Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))`. Establish `hred : IsReduced N.left` using `isReduced_subscheme_vanishingIdeal _`.

Establish `hft : LocallyOfFiniteType N.hom` using `inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ B.hom))`. Establish `hgr : GeometricallyReduced N.hom` using `geometricallyReduced_of_perfectField N.hom`. Establish `hnoeth : IsLocallyNoetherian N.left` using `LocallyOfFiniteType.isLocallyNoetherian N.hom`. Establish `hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ B), (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, x ≫ g ∈ C) → ∃ l : T ⟶ N, l ≫ ν = g`. Introduce `T _ _ g hg`.

Establish `h1` using `range_subset_of_points g hZ fun x => (hC _).mp (hg x)`. Establish `h2 : I.subschemeι.ker ≤ g.left.ker`. Rewrite using `[ker_subschemeι]`. Conclude with `vanishingIdeal_le_ker g.left ⟨Z, hZ⟩ h1`. Establish `h3` using `IsClosedImmersion.lift_fac I.subschemeι g.left h2`.

Use `⟨Over.homMk (IsClosedImmersion.lift I.subschemeι g.left h2) ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≫ I.subschemeι ≫ B.hom = _`. Rewrite using `[← Category.assoc, h3, Over.w]`. Use `ext1`. Conclude with `h3`.

Establish `hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C` using `fun x => by`. Rewrite using `[hC, ← hr]`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨x.left t, rfl⟩`. Establish `: IsReduced (𝟙_ (Over (Sp k))).left` using `inferInstanceAs (IsReduced (Sp k))`.

Establish `: LocallyOfFiniteType (𝟙_ (Over (Sp k))).hom` using `inferInstanceAs (LocallyOfFiniteType (𝟙 (Sp k)))`. Establish `: IsReduced (N ⊗ N).left` using `inferInstanceAs (IsReduced (pullback N.hom N.hom))`. Establish `: LocallyOfFiniteType (N ⊗ N).hom` using `inferInstanceAs (LocallyOfFiniteType (pullback.fst N.hom N.hom ≫ N.hom))`. Take `⟨e, he⟩` from `hlift η[B] fun x => by`. Rewrite using `[toUnit_unique x (toUnit _), ← Hom.one_def]`.

Conclude with `C.one_mem`. Take `⟨m, hm⟩` from `hlift ((ν ⊗ₘ ν) ≫ μ[B]) fun x => by`. Establish `: x ≫ (ν ⊗ₘ ν) ≫ μ[B] = ((x ≫ fst N N) ≫ ν) * ((x ≫ snd N N) ≫ ν)`. Rewrite using `[Hom.mul_def, ← lift_map, Category.assoc, ← comp_lift, lift_fst_snd, Category.comp_id]`. Rewrite using `[this]`.

Conclude with `C.mul_mem (hmem _) (hmem _)`. Take `⟨i, hi⟩` from `hlift (ν ≫ GrpObj.inv) fun x => by`. Rewrite using `[← Category.assoc, ← Hom.inv_def]`. Conclude with `C.inv_mem (hmem _)`. Take `⟨G, hG⟩` from `exists_grpObj_of_mono ν e m i he hm hi`.

Use `⟨N, G, ν, hG, hν, ?_, hr⟩` and prove the remaining obligations. Use `letI : GrpObj (Over.mk N.hom) := G`. Conclude with `smooth_of_grpObj N.hom`.
-/
theorem exists_smooth_closed_subgroup (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k))
    [GrpObj B] (hB : LocallyOfFiniteType B.hom) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B))
    (Z : Set B.left) (hZ : IsClosed Z) (hC : ∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) :
    ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ B), IsMonHom ν ∧ IsClosedImmersion ν.left ∧
      Smooth N.hom ∧ Set.range ν.left = Z := by
  let I : B.left.IdealSheafData := vanishingIdeal ⟨Z, hZ⟩
  let N : Over (Sp k) := Over.mk (I.subschemeι ≫ B.hom)
  let ν : N ⟶ B := Over.homMk I.subschemeι rfl
  have hν : IsClosedImmersion ν.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hr : Set.range ν.left = Z := by
    change Set.range I.subschemeι = Z
    rw [range_subschemeι]
    rfl
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hred : IsReduced N.left := isReduced_subscheme_vanishingIdeal _
  have hft : LocallyOfFiniteType N.hom :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ B.hom))
  have hgr : GeometricallyReduced N.hom := geometricallyReduced_of_perfectField N.hom
  have hnoeth : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ B),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, x ≫ g ∈ C) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    have h1 := range_subset_of_points g hZ fun x => (hC _).mp (hg x)
    have h2 : I.subschemeι.ker ≤ g.left.ker := by
      rw [ker_subschemeι]
      exact vanishingIdeal_le_ker g.left ⟨Z, hZ⟩ h1
    have h3 := IsClosedImmersion.lift_fac I.subschemeι g.left h2
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι g.left h2) ?_, ?_⟩
    · change _ ≫ I.subschemeι ≫ B.hom = _
      rw [← Category.assoc, h3, Over.w]
    · ext1
      exact h3
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have : LocallyOfFiniteType (𝟙_ (Over (Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Sp k)))
  have : IsReduced (N ⊗ N).left := inferInstanceAs (IsReduced (pullback N.hom N.hom))
  have : LocallyOfFiniteType (N ⊗ N).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst N.hom N.hom ≫ N.hom))
  obtain ⟨e, he⟩ := hlift η[B] fun x => by
    rw [toUnit_unique x (toUnit _), ← Hom.one_def]
    exact C.one_mem
  obtain ⟨m, hm⟩ := hlift ((ν ⊗ₘ ν) ≫ μ[B]) fun x => by
    have : x ≫ (ν ⊗ₘ ν) ≫ μ[B] = ((x ≫ fst N N) ≫ ν) * ((x ≫ snd N N) ≫ ν) := by
      rw [Hom.mul_def, ← lift_map, Category.assoc, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [this]
    exact C.mul_mem (hmem _) (hmem _)
  obtain ⟨i, hi⟩ := hlift (ν ≫ GrpObj.inv) fun x => by
    rw [← Category.assoc, ← Hom.inv_def]
    exact C.inv_mem (hmem _)
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨N, G, ν, hG, hν, ?_, hr⟩
  letI : GrpObj (Over.mk N.hom) := G
  exact smooth_of_grpObj N.hom

end GlobalTheory.ReducedSubgroup
