import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimGen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

open TensorProduct

/- English proof (translation)
Establish `h : genericPoint (Spec (.of A)) = (⟨⊥, inferInstance⟩ : PrimeSpectrum A)` using `genericPoint_eq_bot_of_affine (.of A)`. Rewrite using `[← h]`. Conclude with `genericPoint_eq_of_isOpenImmersion j`.
-/
theorem map_bot_eq_genericPoint {Y : Scheme.{0}} [IsIntegral Y] {A : Type} [CommRing A] [IsDomain A]
    (j : Spec (.of A) ⟶ Y) [IsOpenImmersion j] :
    j (⟨⊥, inferInstance⟩ : PrimeSpectrum A) = genericPoint Y := by
  have h : genericPoint (Spec (.of A)) = (⟨⊥, inferInstance⟩ : PrimeSpectrum A) :=
    genericPoint_eq_bot_of_affine (.of A)
  rw [← h]
  exact genericPoint_eq_of_isOpenImmersion j

/- English proof (translation)
Take `⟨A, _, _, _, _, _, j, _, -, hj, hA⟩` from `exists_affine_chart_trdeg_eq Z.str (genericPoint Z.X)`. Take `⟨d, hd⟩` from `exists_trdeg_eq_natCast O (A := A)`. Establish `h₁` using `topologicalKrullDim_preimage_genericPoint_eq Z.str (hA.symm.trans hd)`. Establish `h₂` using `topologicalKrullDim_eq_of_isEmbedding Z.gen.ι.isOpenEmbedding.isEmbedding (Z := Z.str ⁻¹' {genericPoint (Spec (.of O))}) (by`. Rewrite using `[Scheme.Opens.range_ι, genericPoint_eq_bot_of_affine]`.

Use extensionality with `x`. Conclude with `mem_gen_iff_eq_bot.trans ⟨fun h => PrimeSpectrum.ext h, fun h => congrArg PrimeSpectrum.asIdeal h⟩)`. Rewrite `h₂` using `[h₁, topologicalKrullDim_gen]`. Take `rfl : d = Z.relDim` from `by exact_mod_cast h₂`. Take `⟨_, ⟨b, rfl⟩, hb, hbW⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := (⟨⊥, inferInstance⟩ : PrimeSpectrum A)) (u := j ⁻¹' W) ((map_bot_eq_genericPoint j).symm ▸ hη : j (⟨⊥, inferInstance⟩ : PrimeSpectrum A) ∈ W) (hW.preimage j.continuous)`.

Establish `hb0 : b ≠ 0` using `hb`. Establish `hle` using `powers_le_nonZeroDivisors_of_noZeroDivisors hb0`. Establish `: IsDomain (Localization.Away b)` using `IsLocalization.isDomain_localization hle`. Establish `: FaithfulSMul A (Localization.Away b)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)`. Establish `: Algebra.IsAlgebraic A (Localization.Away b)` using `IsLocalization.isAlgebraic _ (.powers b)`.

Establish `: IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b))))` using `.of_isLocalization b`. Use `⟨Localization.Away b, inferInstance, inferInstance, inferInstance, .trans (S := A) inferInstance inferInstance, .trans O A _, Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ j, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hbW ((PrimeSpectrum.localization_away_comap_range (Localization.Away b) b).le ⟨x, rfl⟩)`. Rewrite using `[Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]`.

Rewrite using `[trdeg_eq_of_isAlgebraic_top O A, hd]`.
-/
theorem exists_chart_trdeg_eq_relDim {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O) (W : Set Z.X) (hW : IsOpen W)
    (hη : genericPoint Z.X ∈ W) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra O A)
      (_ : Algebra.FiniteType O A) (_ : FaithfulSMul O A) (j : Spec (.of A) ⟶ Z.X)
      (_ : IsOpenImmersion j), Set.range j ⊆ W ∧
      j ≫ Z.str = Spec.map (CommRingCat.ofHom (algebraMap O A)) ∧
      Algebra.trdeg O A = Z.relDim := by
  obtain ⟨A, _, _, _, _, _, j, _, -, hj, hA⟩ :=
    exists_affine_chart_trdeg_eq Z.str (genericPoint Z.X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq Z.str (hA.symm.trans hd)
  have h₂ := topologicalKrullDim_eq_of_isEmbedding Z.gen.ι.isOpenEmbedding.isEmbedding
    (Z := Z.str ⁻¹' {genericPoint (Spec (.of O))}) (by
      rw [Scheme.Opens.range_ι, genericPoint_eq_bot_of_affine]
      ext x
      exact mem_gen_iff_eq_bot.trans ⟨fun h => PrimeSpectrum.ext h, fun h => congrArg PrimeSpectrum.asIdeal h⟩)
  rw [h₁, topologicalKrullDim_gen] at h₂
  obtain rfl : d = Z.relDim := by exact_mod_cast h₂
  obtain ⟨_, ⟨b, rfl⟩, hb, hbW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := (⟨⊥, inferInstance⟩ : PrimeSpectrum A)) (u := j ⁻¹' W)
    ((map_bot_eq_genericPoint j).symm ▸ hη : j (⟨⊥, inferInstance⟩ : PrimeSpectrum A) ∈ W) (hW.preimage j.continuous)
  have hb0 : b ≠ 0 := hb
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hb0
  have : IsDomain (Localization.Away b) := IsLocalization.isDomain_localization hle
  have : FaithfulSMul A (Localization.Away b) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic A (Localization.Away b) := IsLocalization.isAlgebraic _ (.powers b)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b)))) :=
    .of_isLocalization b
  refine ⟨Localization.Away b, inferInstance, inferInstance, inferInstance,
    .trans (S := A) inferInstance inferInstance, .trans O A _,
    Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ j, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hbW ((PrimeSpectrum.localization_away_comap_range (Localization.Away b) b).le ⟨x, rfl⟩)
  · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  · rw [trdeg_eq_of_isAlgebraic_top O A, hd]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

/- English proof (translation)
Introduce `O _ _ _ Z Z₁ f`. Use `f.dim_genFibre_le.antisymm ?_` and prove the remaining obligations. Establish `hη : f.f (genericPoint Z₁.X) = genericPoint Z.X`. Use `(genericPoint_spec Z₁.X).image f.f.continuous` as an intermediate fact. Rewrite `this` using `[Set.image_univ, f.f.surjective.range_eq, closure_univ]`.

Conclude with `this.eq (genericPoint_spec Z.X)`. Take `⟨A, _, _, _, _, _, j, _, -, hj, hA⟩` from `exists_chart_trdeg_eq_relDim Z Set.univ isOpen_univ trivial`. Take `⟨B, _, _, _, _, _, j₁, _, hr, hj₁, hB⟩` from `exists_chart_trdeg_eq_relDim Z₁ (f.f ⁻¹' Set.range j) (j.isOpenEmbedding.isOpen_range.preimage f.f.continuous) ⟨_, (map_bot_eq_genericPoint j).trans hη.symm⟩`. Establish `hr' : Set.range (j₁ ≫ f.f) ⊆ Set.range j`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `hr ⟨x, rfl⟩`. Set `ψ` to `Spec.preimage (IsOpenImmersion.lift j (j₁ ≫ f.f) hr')`. Establish `hψ : Spec.map ψ ≫ j = j₁ ≫ f.f`. Rewrite using `[Spec.map_preimage, IsOpenImmersion.lift_fac]`. Set `: Algebra A B` to `ψ.hom.toAlgebra`.

Establish `hpt (p : PrimeSpectrum B) : f.f (j₁ p) = j (PrimeSpectrum.comap (algebraMap A B) p)` using `congr($hψ p).symm`. Establish `hc : CommRingCat.ofHom (algebraMap O A) ≫ ψ = CommRingCat.ofHom (algebraMap O B)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, ← hj, ← hj₁, ← Category.assoc, hψ, Category.assoc, f.comp_str]`. Establish `: IsScalarTower O A B` using `IsScalarTower.of_algebraMap_eq fun a => congr($(hc).hom a).symm`.

Establish `: Algebra.FiniteType A B` using `.of_restrictScalars_finiteType O A B`. Establish `: FaithfulSMul A B`. Establish `h` using `hpt ⟨⊥, inferInstance⟩`. Rewrite `h` using `[map_bot_eq_genericPoint, hη, ← map_bot_eq_genericPoint j]`. Rewrite using `[faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot]`.

Conclude with `(congrArg PrimeSpectrum.asIdeal (j.isOpenEmbedding.injective h)).symm`. Take `⟨e, he⟩` from `exists_trdeg_eq_natCast A (A := B)`. Establish `hadd` using `trdeg_add_eq O A (A := B)`. Rewrite `hadd` using `[hA, hB, he]`. Choose the witnesses or unpack the hypotheses as in `rfl : e = f.relDim := by`.

Establish `h₁ : Z.relDim + e = Z₁.relDim` using `by exact_mod_cast hadd`. Establish `h₂` using `f.relDim_add`. Use linear arithmetic over natural numbers and integers. Use `IsLocalization.tensorRight (S := B) (FractionRing A) (nonZeroDivisors A)` as an intermediate fact. Establish `hemb` using `j₁.isOpenEmbedding.isEmbedding.comp (PrimeSpectrum.localization_comap_isEmbedding (FractionRing A ⊗[A] B) (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)))`.

Rewrite using `[← ringKrullDim_genericFibre_eq A (FractionRing A) he, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← topologicalKrullDim_eq_of_isEmbedding hemb rfl]`. Use `(QCoh.topologicalKrullDim_mono ?_).trans (topologicalKrullDim_eq_of_isEmbedding (f.f.fiberι (genericPoint Z.X)).isEmbedding (f.f.range_fiberι _)).le` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Establish `hp` using `(PrimeSpectrum.localization_comap_range (FractionRing A ⊗[A] B) (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))).le ⟨p, rfl⟩`. Use `(hpt _).trans ((congrArg j (PrimeSpectrum.ext (eq_bot_iff.2 fun a ha => ?_))).trans (map_bot_eq_genericPoint j))` and prove the remaining obligations.

Assume the negation of the conclusion as `h0`. Conclude with `Set.disjoint_left.1 hp ⟨a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ ha`.
-/
theorem topologicalKrullDim_genFibre : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z Z₁ : Model O) (f : Hom Z₁ Z),
    topologicalKrullDim f.genFibre = f.relDim := by
  intro O _ _ _ Z Z₁ f
  refine f.dim_genFibre_le.antisymm ?_
  have hη : f.f (genericPoint Z₁.X) = genericPoint Z.X := by
    have := (genericPoint_spec Z₁.X).image f.f.continuous
    rw [Set.image_univ, f.f.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec Z.X)
  obtain ⟨A, _, _, _, _, _, j, _, -, hj, hA⟩ :=
    exists_chart_trdeg_eq_relDim Z Set.univ isOpen_univ trivial
  obtain ⟨B, _, _, _, _, _, j₁, _, hr, hj₁, hB⟩ :=
    exists_chart_trdeg_eq_relDim Z₁ (f.f ⁻¹' Set.range j)
      (j.isOpenEmbedding.isOpen_range.preimage f.f.continuous)
      ⟨_, (map_bot_eq_genericPoint j).trans hη.symm⟩
  have hr' : Set.range (j₁ ≫ f.f) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact hr ⟨x, rfl⟩
  let ψ := Spec.preimage (IsOpenImmersion.lift j (j₁ ≫ f.f) hr')
  have hψ : Spec.map ψ ≫ j = j₁ ≫ f.f := by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  let : Algebra A B := ψ.hom.toAlgebra
  have hpt (p : PrimeSpectrum B) : f.f (j₁ p) = j (PrimeSpectrum.comap (algebraMap A B) p) :=
    congr($hψ p).symm
  have hc : CommRingCat.ofHom (algebraMap O A) ≫ ψ = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hj, ← hj₁, ← Category.assoc, hψ, Category.assoc, f.comp_str]
  have : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq fun a => congr($(hc).hom a).symm
  have : Algebra.FiniteType A B := .of_restrictScalars_finiteType O A B
  have : FaithfulSMul A B := by
    have h := hpt ⟨⊥, inferInstance⟩
    rw [map_bot_eq_genericPoint, hη, ← map_bot_eq_genericPoint j] at h
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot]
    exact (congrArg PrimeSpectrum.asIdeal (j.isOpenEmbedding.injective h)).symm
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast A (A := B)
  have hadd := trdeg_add_eq O A (A := B)
  rw [hA, hB, he] at hadd
  obtain rfl : e = f.relDim := by
    have h₁ : Z.relDim + e = Z₁.relDim := by exact_mod_cast hadd
    have h₂ := f.relDim_add
    omega
  have := IsLocalization.tensorRight (S := B) (FractionRing A) (nonZeroDivisors A)
  have hemb := j₁.isOpenEmbedding.isEmbedding.comp
      (PrimeSpectrum.localization_comap_isEmbedding (FractionRing A ⊗[A] B)
        (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)))
  rw [← ringKrullDim_genericFibre_eq A (FractionRing A) he,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ← topologicalKrullDim_eq_of_isEmbedding hemb rfl]
  refine (QCoh.topologicalKrullDim_mono ?_).trans (topologicalKrullDim_eq_of_isEmbedding
    (f.f.fiberι (genericPoint Z.X)).isEmbedding (f.f.range_fiberι _)).le
  rintro _ ⟨p, rfl⟩
  have hp := (PrimeSpectrum.localization_comap_range (FractionRing A ⊗[A] B)
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))).le ⟨p, rfl⟩
  refine (hpt _).trans ((congrArg j (PrimeSpectrum.ext (eq_bot_iff.2 fun a ha => ?_))).trans
    (map_bot_eq_genericPoint j))
  by_contra h0
  exact Set.disjoint_left.1 hp ⟨a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ ha

end GlobalTheory.Vert.Model
