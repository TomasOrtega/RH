import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSectionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroNoetherianBaseStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalSectionNonzeroAllFibresModuliStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

/- English proof (translation)
Establish `hopen : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j)` using `j.isOpenEmbedding.isOpen_range.preimage x.continuous`. Take `⟨_, ⟨g, rfl⟩, hg, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hopen`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Establish `hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x) ⊆ Set.range j`. Introduce and unpack `_ ⟨q, rfl⟩`.

Rewrite using `[Scheme.Hom.comp_apply]`. Apply `hsub` to reduce the goal to its premises. Establish `: PrimeSpectrum.comap (algebraMap S (Localization.Away g)) q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g)))` using `⟨q, rfl⟩`. Rewrite `this` using `[PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]`. Conclude with `this`.

Use `⟨(Spec.preimage (IsOpenImmersion.lift j _ hr)).hom, ?_⟩` and prove the remaining obligations. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]`.
-/
theorem exists_away_lift {X : Scheme.{0}} {S R : Type} [CommRing S] [CommRing R]
    (x : Spec (CommRingCat.of S) ⟶ X) (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p : Spec (CommRingCat.of S)) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∃ φ : R →+* Localization.Away g,
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x =
        Spec.map (CommRingCat.ofHom φ) ≫ j := by
  have hopen : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hopen
  refine ⟨g, hg, ?_⟩
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x) ⊆
      Set.range j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hsub
    have : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) q ∈
        Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := ⟨q, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at this
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j _ hr)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

/- English proof (translation)
Introduce `hB E _ _ _ H Dw l Xo S _ x p`. Take `⟨R, _, _, j, θ₀, hj, hz, hnz⟩` from `GlobalTheory.T.exists_local_section_nonzero_all_fibres_moduli hB E H Dw l Xo (x p)`. Take `⟨g, hg, φ, hφ⟩` from `exists_away_lift x j p hz`. Establish `hφ' : spMap (algebraMap S (Localization.Away g)) ≫ x = spMap φ ≫ j` using `hφ`. Take `⟨θ, hθ, -⟩` from `GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo R (Localization.Away g) φ 1 j _ hφ' θ₀`.

Use `⟨g, hg, θ, ?_⟩` and prove the remaining obligations. Introduce `T _ ψ x' θ' hx' hbc`. Establish `h1 : SecBC (ψ.comp φ) 1 j x' θ₀ θ'` using `((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo R (Localization.Away g) T φ ψ j _ x' hφ' hx').1 1 θ₀ θ θ' hθ).1 hbc`. Establish `hx'' : x' = spMap (ψ.comp φ) ≫ j`. Rewrite using `[hx', hφ', ← Category.assoc]`.

Use `congr 1`. Conclude with `(Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm`. Conclude with `⟨GlobalTheory.T.fibreSectionGenerates_of_nowhereZero_noetherian_baseChange hB E H Dw l Xo R j θ₀ hnz T (ψ.comp φ) x' θ' hx'' h1, fun p' => (GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo R T (ψ.comp φ) j x' hx'' θ₀ θ' h1 p').2 (hnz _)⟩`.
-/
theorem exists_local_generator : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (p : Sp S), ∃ g : S, g ∉ p.asIdeal ∧ ∃ θ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x)), ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x → SecBC ψ 1 _ x' θ θ' → SecGen x' θ' ∧ SecNZ x' θ' := by
  intro hB E _ _ _ H Dw l Xo S _ x p
  obtain ⟨R, _, _, j, θ₀, hj, hz, hnz⟩ := GlobalTheory.T.exists_local_section_nonzero_all_fibres_moduli hB E H Dw l Xo (x p)
  obtain ⟨g, hg, φ, hφ⟩ := exists_away_lift x j p hz
  have hφ' : spMap (algebraMap S (Localization.Away g)) ≫ x = spMap φ ≫ j := hφ
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo R (Localization.Away g) φ 1 j _ hφ' θ₀
  refine ⟨g, hg, θ, ?_⟩
  intro T _ ψ x' θ' hx' hbc
  have h1 : SecBC (ψ.comp φ) 1 j x' θ₀ θ' :=
    ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo R (Localization.Away g) T φ ψ j _ x' hφ' hx').1 1 θ₀ θ θ' hθ).1 hbc
  have hx'' : x' = spMap (ψ.comp φ) ≫ j := by
    rw [hx', hφ', ← Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm
  exact ⟨GlobalTheory.T.fibreSectionGenerates_of_nowhereZero_noetherian_baseChange hB E H Dw l Xo R j θ₀ hnz T (ψ.comp φ) x' θ' hx'' h1,
    fun p' => (GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo R T (ψ.comp φ) j x' hx'' θ₀ θ' h1 p').2 (hnz _)⟩

end GlobalTheory.Frames
