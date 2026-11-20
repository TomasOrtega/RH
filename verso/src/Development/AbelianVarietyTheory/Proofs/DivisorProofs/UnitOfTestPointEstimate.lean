import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

/- English proof (translation)
Establish `h1` using `(PadicComplexInt.integers p).isUnit_iff_valuation_eq_one.1 hx`. Rewrite using `[← coe_valued]`. Express the relevant statement in the definitionally equal form `((Valued.v ((algebraMap 𝓞_ℂ_[p] ℂ_[p]) x) : ℝ≥0) : ℝ) = 1`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem norm_coe_of_isUnit_padicComplexInt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) (hx : IsUnit x) :
    ‖(x : ℂ_[p])‖ = 1 := by
  have h1 := (PadicComplexInt.integers p).isUnit_iff_valuation_eq_one.1 hx
  rw [← coe_valued]
  change ((Valued.v ((algebraMap 𝓞_ℂ_[p] ℂ_[p]) x) : ℝ≥0) : ℝ) = 1
  rw [h1]; rfl

/- English proof (translation)
Introduce `F _ _ V p _ hp hD X s Xw hX hflat hlft hXw hne A _ w hw u hu`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `𝔮 ⟨hle, h𝔮⟩`. Assume the negation of the conclusion as `hf`. Set `f : A` to `u - 1`.

Set `B` to `Localization.Away f`. Use `haveI : IsOpenImmersion (spMap (algebraMap A B)) := inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))`. Set `ξ : Sp B ⟶ X` to `spMap (algebraMap A B) ≫ w`. Establish `hpq : (p : A) ∈ 𝔮` using `hle (Ideal.subset_span rfl)`. Establish `hdisj : Disjoint (Submonoid.powers f : Set A) (𝔮 : Set A)` using `(Ideal.disjoint_powers_iff_notMem _ h𝔮.isRadical).2 hf`.

Set `Q : Ideal B` to `Ideal.map (algebraMap A B) 𝔮`. Use `haveI hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) B 𝔮 h𝔮 hdisj`. Establish `hpQ : (p : B) ∈ Q`. Rewrite using `[← map_natCast (algebraMap A B)]`. Conclude with `Ideal.mem_map_of_mem _ hpq`.

Set `y : Sp B` to `(⟨Q, hQ⟩ : PrimeSpectrum B)`. Establish `hx : ξ y ∉ X.basicOpen (p : Γ(X, ⊤))`. Establish `h1 : y ∉ ξ ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤))`. Rewrite using `[Scheme.preimage_basicOpen_top, map_natCast]`. Establish `h2 : ((p : Γ(Sp B, ⊤))) = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (p : B)` using `(map_natCast _ _).symm`.

Rewrite using `[h2, basicOpen_eq_of_affine]`. Introduce `h3`. Conclude with `((PrimeSpectrum.mem_basicOpen _ _).1 h3) hpQ`. Conclude with `h1`. Take `⟨φ, hφ⟩` from `hD F V p hp X s Xw hX hflat hlft hXw hne B ξ inferInstance ⟨ξ y, ⟨y, rfl⟩, hx⟩`.

Establish `hφ' : IsTest p Xw (spMap (φ.comp (algebraMap A B)) ≫ w)`. Rewrite using `[← sp_sp]`. Conclude with `hφ`. Establish `h1` using `hu _ hφ'`. Establish `hunit : IsUnit ((φ.comp (algebraMap A B)) f)` using `(IsLocalization.Away.algebraMap_isUnit (S := B) f).map φ`.

Establish `h2 : ((φ.comp (algebraMap A B) u : 𝓞_ℂ_[p]) : ℂ_[p]) - 1 = (((φ.comp (algebraMap A B)) f : 𝓞_ℂ_[p]) : ℂ_[p])`. Simplify using `[f, map_sub]`. Rewrite `h1` using `[h2, norm_coe_of_isUnit_padicComplexInt p _ hunit]`. Conclude with `lt_irrefl _ h1`.
-/
theorem sub_one_mem_radical_of_isTest : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → ∀ u : A, (∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ‖(φ u : ℂ_[p]) - 1‖ < 1) → u - 1 ∈ (Ideal.span {(p : A)}).radical := by
  intro F _ _ V p _ hp hD X s Xw hX hflat hlft hXw hne A _ w hw u hu
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro 𝔮 ⟨hle, h𝔮⟩
  by_contra hf
  let f : A := u - 1
  let B := Localization.Away f
  haveI : IsOpenImmersion (spMap (algebraMap A B)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))
  let ξ : Sp B ⟶ X := spMap (algebraMap A B) ≫ w
  have hpq : (p : A) ∈ 𝔮 := hle (Ideal.subset_span rfl)
  have hdisj : Disjoint (Submonoid.powers f : Set A) (𝔮 : Set A) :=
    (Ideal.disjoint_powers_iff_notMem _ h𝔮.isRadical).2 hf
  let Q : Ideal B := Ideal.map (algebraMap A B) 𝔮
  haveI hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) B 𝔮 h𝔮 hdisj
  have hpQ : (p : B) ∈ Q := by
    rw [← map_natCast (algebraMap A B)]; exact Ideal.mem_map_of_mem _ hpq
  let y : Sp B := (⟨Q, hQ⟩ : PrimeSpectrum B)
  have hx : ξ y ∉ X.basicOpen (p : Γ(X, ⊤)) := by
    have h1 : y ∉ ξ ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := by
      rw [Scheme.preimage_basicOpen_top, map_natCast]
      have h2 : ((p : Γ(Sp B, ⊤))) = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (p : B) := (map_natCast _ _).symm
      rw [h2, basicOpen_eq_of_affine]
      intro h3
      exact ((PrimeSpectrum.mem_basicOpen _ _).1 h3) hpQ
    exact h1
  obtain ⟨φ, hφ⟩ := hD F V p hp X s Xw hX hflat hlft hXw hne B ξ inferInstance ⟨ξ y, ⟨y, rfl⟩, hx⟩
  have hφ' : IsTest p Xw (spMap (φ.comp (algebraMap A B)) ≫ w) := by
    rw [← sp_sp]; exact hφ
  have h1 := hu _ hφ'
  have hunit : IsUnit ((φ.comp (algebraMap A B)) f) :=
    (IsLocalization.Away.algebraMap_isUnit (S := B) f).map φ
  have h2 : ((φ.comp (algebraMap A B) u : 𝓞_ℂ_[p]) : ℂ_[p]) - 1 = (((φ.comp (algebraMap A B)) f : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    simp [f, map_sub]
  rw [h2, norm_coe_of_isUnit_padicComplexInt p _ hunit] at h1
  exact lt_irrefl _ h1

end GlobalTheory.FlatModel
