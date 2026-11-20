import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf

/- English proof (translation)
Introduce `k _ G A B F _ _ _ _ _ _ j φ δ χ₀ hj h`. Set `U : (Spec (CommRingCat.of B)).Opens` to `φ.left ⁻¹ᵁ j.left.opensRange`. Set `p₀ : PrimeSpectrum F` to `⟨⊥, Ideal.isPrime_bot⟩`. Set `p : PrimeSpectrum B` to `PrimeSpectrum.comap (δ : B →+* F) p₀`. Establish `hl : (algOverHom δ).left ≫ φ.left = (algOverHom χ₀).left ≫ j.left`.

Use `congrArg (fun x => x.left) h` as an intermediate fact. Simplify `this` using `only [Over.comp_left]`. Establish `hp : p ∈ (U : Set (Spec (CommRingCat.of B)))`. Use `⟨(algOverHom χ₀).left p₀, ?_⟩` and prove the remaining obligations. Use `congrArg (fun x => x p₀) hl` as an intermediate fact.

Simplify using `only [Scheme.Hom.comp_apply] at this`. Conclude with `this.symm`. Take `⟨_, ⟨e, rfl⟩, he, heU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen`. Use `⟨e, fun h0 => he (show δ e ∈ (⊥ : Ideal F) from h0), ?_⟩` and prove the remaining obligations. Introduce `B' _ _ ρ hρ`.

Establish `hr : Set.range ((algOverHom ρ).left ≫ φ.left) ⊆ Set.range j.left`. Introduce and unpack `_ ⟨q, rfl⟩`. Establish `hq : PrimeSpectrum.comap (ρ : B →+* B') q ∈ PrimeSpectrum.basicOpen e`. Introduce `hm`. Conclude with `q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ρ e ∈ q.asIdeal from hm) hρ)`.

Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `heU hq`. Establish `hf` using `IsOpenImmersion.lift_fac j.left ((algOverHom ρ).left ≫ φ.left) hr`. Set `ψ : algOver k B' ⟶ algOver k A` to `Over.homMk (IsOpenImmersion.lift j.left ((algOverHom ρ).left ≫ φ.left) hr) (by`. Rewrite using `[← Over.w j, ← Category.assoc, hf, Category.assoc, Over.w φ, Over.w (algOverHom ρ)])`.

Take `⟨χ, hχ⟩` from `algOverHom_surjective ψ`. Use `⟨χ, ?_⟩` and prove the remaining obligations. Rewrite using `[hχ]`. Use `ext1`. Conclude with `hf`.
-/
theorem exists_basicOpen_factor : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  intro k _ G A B F _ _ _ _ _ _ j φ δ χ₀ hj h
  let U : (Spec (CommRingCat.of B)).Opens := φ.left ⁻¹ᵁ j.left.opensRange
  let p₀ : PrimeSpectrum F := ⟨⊥, Ideal.isPrime_bot⟩
  let p : PrimeSpectrum B := PrimeSpectrum.comap (δ : B →+* F) p₀
  have hl : (algOverHom δ).left ≫ φ.left = (algOverHom χ₀).left ≫ j.left := by
    have := congrArg (fun x => x.left) h
    simpa only [Over.comp_left] using this
  have hp : p ∈ (U : Set (Spec (CommRingCat.of B))) := by
    refine ⟨(algOverHom χ₀).left p₀, ?_⟩
    have := congrArg (fun x => x p₀) hl
    simp only [Scheme.Hom.comp_apply] at this
    exact this.symm
  obtain ⟨_, ⟨e, rfl⟩, he, heU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨e, fun h0 => he (show δ e ∈ (⊥ : Ideal F) from h0), ?_⟩
  intro B' _ _ ρ hρ
  have hr : Set.range ((algOverHom ρ).left ≫ φ.left) ⊆ Set.range j.left := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap (ρ : B →+* B') q ∈ PrimeSpectrum.basicOpen e := by
      intro hm
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ρ e ∈ q.asIdeal from hm) hρ)
    rw [Scheme.Hom.comp_apply]
    exact heU hq
  have hf := IsOpenImmersion.lift_fac j.left ((algOverHom ρ).left ≫ φ.left) hr
  let ψ : algOver k B' ⟶ algOver k A :=
    Over.homMk (IsOpenImmersion.lift j.left ((algOverHom ρ).left ≫ φ.left) hr) (by
      rw [← Over.w j, ← Category.assoc, hf, Category.assoc, Over.w φ, Over.w (algOverHom ρ)])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective ψ
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

end GlobalTheory.SS.ArcInf
end
