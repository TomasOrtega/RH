import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
import GroundTheory.ProfiniteCohomology.FilteredHomology
import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Union

variable (A : Rep.{u} k G) {ι : Type u} [Preorder ι] (W : ι → Submodule k A) (hW : Monotone W)
  (hstable : ∀ i g, W i ≤ (W i).comap (A.ρ g))

noncomputable def subrepInclusion {i j : ι} (h : i ≤ j) :
    A.subrepresentation (W i) (hstable i) ⟶ A.subrepresentation (W j) (hstable j) :=
  Rep.ofHom ⟨Submodule.inclusion (hW h), fun _ => LinearMap.ext fun _ => rfl⟩

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem subrepInclusion_refl {i : ι} (h : i ≤ i) : subrepInclusion A W hW hstable h = 𝟙 _ := by
  ext
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem subrepInclusion_trans {i j l : ι} (h₁ : i ≤ j) (h₂ : j ≤ l) :
    subrepInclusion A W hW hstable (h₁.trans h₂) =
      subrepInclusion A W hW hstable h₁ ≫ subrepInclusion A W hW hstable h₂ := by
  ext
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem subrepInclusion_comp_subtype {i j : ι} (h : i ≤ j) :
    subrepInclusion A W hW hstable h ≫ Rep.subtype A (W j) (hstable j) =
      Rep.subtype A (W i) (hstable i) := by
  ext
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A]

@[simps]
noncomputable def subrepCochains : ι ⥤ CochainComplex (ModuleCat k) ℕ where
  obj i := cochainsComplex (A.subrepresentation (W i) (hstable i))
  map h := cochainsMap (subrepInclusion A W hW hstable (leOfHom h))
  map_id i := by rw [subrepInclusion_refl, cochainsMap_id]
  map_comp f g := by rw [← cochainsMap_comp, ← subrepInclusion_trans]

@[simps]
noncomputable def subrepCochainsCocone : Cocone (subrepCochains A W hW hstable) where
  pt := cochainsComplex A
  ι :=
    { app i := cochainsMap (Rep.subtype A (W i) (hstable i))
      naturality i j h := by
        refine (cochainsMap_comp _ _).symm.trans ?_
        rw [subrepInclusion_comp_subtype]
        exact (Category.comp_id _).symm }

noncomputable abbrev subrepCohomology (n : ℕ) : ι ⥤ ModuleCat k :=
  subrepCochains A W hW hstable ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n

noncomputable abbrev subrepCohomologyCocone (n : ℕ) : Cocone (subrepCohomology A W hW hstable n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapCocone
    (subrepCochainsCocone A W hW hstable)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem subrepCohomology_map (n : ℕ) {i j : ι} (h : i ⟶ j) :
    (subrepCohomology A W hW hstable n).map h =
      cohomologyMap (subrepInclusion A W hW hstable (leOfHom h)) n :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem subrepCohomologyCocone_ι_app (n : ℕ) (i : ι) :
    (subrepCohomologyCocone A W hW hstable n).ι.app i =
      cohomologyMap (Rep.subtype A (W i) (hstable i)) n :=
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem subrepCochainsCocone_inj (n : ℕ) (i : ι)
    (y : ((subrepCochains A W hW hstable).obj i).X n)
    (hy : (((subrepCochainsCocone A W hW hstable).ι.app i).f n).hom y = 0) :
    ∃ (j : ι) (f : i ⟶ j), (((subrepCochains A W hW hstable).map f).f n).hom y = 0 := by
  refine ⟨i, 𝟙 i, ?_⟩
  have : Mono (Rep.subtype A (W i) (hstable i)) :=
    (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  have hinj : Function.Injective ((cochainsMap (Rep.subtype A (W i) (hstable i))).f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply]
  exact hinj (hy.trans (map_zero _).symm)

variable [CompactSpace G]

omit [IsTopologicalGroup G] [IsDiscreteRep A] in
include hW in

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_forall_mem_of_isLocallyConstant [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) {n : ℕ} {f : (Fin n → G) → A} (hf : IsLocallyConstant f) :
    ∃ j, ∀ g, f g ∈ W j := by
  classical
  choose idx hidx using hunion
  obtain ⟨j, hj⟩ := Finset.exists_le (hf.range_finite.toFinset.image idx)
  exact ⟨j, fun g => hW (hj _ (Finset.mem_image_of_mem _ (by simp))) (hidx (f g))⟩

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem subrepCochainsCocone_surj [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (x : (subrepCochainsCocone A W hW hstable).pt.X n) :
    ∃ (j : ι) (y : ((subrepCochains A W hW hstable).obj j).X n),
      (((subrepCochainsCocone A W hW hstable).ι.app j).f n).hom y = x := by
  have hx : IsLocallyConstant (((cochainsComplexι A).f n).hom x : (Fin n → G) → A) :=
    (show locallyConstantCochains A n from x).2
  obtain ⟨j, hj⟩ := exists_forall_mem_of_isLocallyConstant A W hW hunion hx
  have hy : IsLocallyConstant fun g : Fin n → G =>
      (⟨((cochainsComplexι A).f n).hom x g, hj g⟩ : W j) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro b
    have : (fun g : Fin n → G => (⟨((cochainsComplexι A).f n).hom x g, hj g⟩ : W j)) ⁻¹' {b} =
        (((cochainsComplexι A).f n).hom x : (Fin n → G) → A) ⁻¹' {(b : A)} := by
      ext g
      simp [Subtype.ext_iff]
    rw [this]
    exact hx.isOpen_fiber _
  refine ⟨j, ⟨_, hy⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι A).f n)).1 inferInstance
  rfl

include hW in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_cohomologyMap_subtype_eq [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (x : cohomology A n) :
    ∃ (i : ι) (y : cohomology (A.subrepresentation (W i) (hstable i)) n),
      (cohomologyMap (Rep.subtype A (W i) (hstable i)) n).hom y = x :=
  exists_homologyMap_eq_of_cocone (subrepCochainsCocone A W hW hstable) n
    (subrepCochainsCocone_surj A W hW hstable hunion n)
    (subrepCochainsCocone_inj A W hW hstable _) x

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_cohomologyMap_subrepInclusion_eq_zero [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (i : ι)
    (y : cohomology (A.subrepresentation (W i) (hstable i)) n)
    (hy : (cohomologyMap (Rep.subtype A (W i) (hstable i)) n).hom y = 0) :
    ∃ (j : ι) (h : i ≤ j), (cohomologyMap (subrepInclusion A W hW hstable h) n).hom y = 0 := by
  obtain ⟨j, f, hf⟩ := exists_homologyMap_map_eq_zero_of_cocone
    (subrepCochainsCocone A W hW hstable) n
    (subrepCochainsCocone_surj A W hW hstable hunion _)
    (subrepCochainsCocone_inj A W hW hstable n) i y hy
  exact ⟨j, leOfHom f, hf⟩

noncomputable def isColimitSubrepCohomologyCocone [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) :
    IsColimit (subrepCohomologyCocone A W hW hstable n) :=
  isColimitHomologyMapCocone (subrepCochainsCocone A W hW hstable) n
    (subrepCochainsCocone_surj A W hW hstable hunion) (subrepCochainsCocone_inj A W hW hstable)

noncomputable def cohomologyIsoColimitSubrep [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) :
    cohomology A n ≅ colimit (subrepCohomology A W hW hstable n) :=
  (isColimitSubrepCohomologyCocone A W hW hstable hunion n).coconePointUniqueUpToIso
    (colimit.isColimit _)

end Union

end GroundTheory.ProfCoh
