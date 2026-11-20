import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionRealisingSubextensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationQuotientPointsRationalFiniteExtensioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionFractionFieldUniformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitMovesToFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRationalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Enlarge

/- English proof (translation)
Introduce `R _ _ _ hR D n hn hodd hnu R₁ _ _ _ ρ D₁ A hρ hP hS hU`. Establish `hn1 : 1 ≤ n` using `hn.one_lt.le`. Establish `hR₁ : Base R₁` using `⟨hρ.1, by haveI := hR.2; exact charZero_of_injective_ringHom hρ.2.1⟩`. Take `⟨EQ, fQ, hQ⟩` from `GlobalTheory.T.degenerationQuotientPoints_rational_finiteExtension R₁ hR₁ D₁ n hn1`. Take `⟨EA, fA, hA⟩` from `GlobalTheory.T.exists_finite_extension_fraction_field_uniform R₁ hR₁ A n hn1`.

Use `haveI := fQ`. Use `haveI := fA`. Take `⟨R₂, _, _, _, i₁₂, e, hi₁₂, hi₁₂ρ, hloc, he⟩` from `GlobalTheory.T.exists_finiteExtension_realising_subextension R hR R₁ ρ hρ (EQ ⊔ EA) inferInstance`. Take `⟨D₂, hD₂⟩` from `GlobalTheory.MumPull.exists_pull R₁ R₂ i₁₂ hi₁₂.2.1 hloc D₁`. Establish `hP₂` using `nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ i₁₂ D.toPre D₁.toPre D₂.toPre hi₁₂.2.1 hP hD₂`.

Establish `hle : nonZeroDivisors R₁ ≤ (nonZeroDivisors R₂).comap i₁₂` using `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i₁₂ hi₁₂.2.1`. Set `ga : FractionRing R₁ →+* FractionRing R₂` to `IsLocalization.map (FractionRing R₂) i₁₂ hle`. Take `⟨A₂, g, hg, -, hm, t, ht⟩` from `GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap ga) A`. Establish `gp : IsGrpPullback A₂.A A.A (spMap ga) g` using `⟨hg, fun T x y x₀ y₀ hx hy => by`. Take `rfl : x₀ = toBase hg.w x` from `Over.OverMorphism.ext hx`.

Take `rfl : y₀ = toBase hg.w y` from `Over.OverMorphism.ext hy`. Conclude with `congrArg (·.left) (hm T x y).symm⟩`. Establish `hlb : LBIso A₂.L (A.L.pull g)` using `LBIso.symm ⟨t, ht⟩`. Establish `hfib : IsFib i₁₂ A A₂ g` using `⟨ga, fun r => IsLocalization.map_eq hle r, gp, hlb⟩`. Establish `hS₂ : (letI` using `A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) := by`.

Use `letI := A.isAb.comm`. Use `letI := A₂.isAb.comm`. Conclude with `GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A A₂.A (spMap ga) g A.L A₂.L A.isLB A₂.isLB gp hlb hS`. Set `eQ : EQ →+* FractionRing R₂` to `e.comp (IntermediateField.inclusion (le_sup_left : EQ ≤ EQ ⊔ EA)).toRingHom`. Set `eA : EA →+* FractionRing R₂` to `e.comp (IntermediateField.inclusion (le_sup_right : EA ≤ EQ ⊔ EA)).toRingHom`.

Establish `hrat` using `hQ R₂ i₁₂ eQ hi₁₂ hloc (fun r => he r) D₂ hD₂`. Use `⟨R₂, inferInstance, inferInstance, inferInstance, i₁₂.comp ρ, D₂, A₂, hi₁₂ρ, hP₂, hS₂, GlobalTheory.T.uniformisedTrait_moves_to_finite_extension R₁ hR₁ D₁ A hU R₂ i₁₂ hi₁₂ hloc D₂ hD₂ A₂ g hfib, fun σ => ⟨GlobalTheory.T.galois_fixes_quotientPoints_of_rational R₂ D₂ n hrat σ, fun …` and prove the remaining obligations. Take `⟨x₀, hx₀⟩` from `hA R₂ i₁₂ eA hi₁₂.2.1 (fun r => he r) A₂ g hfib x hx`. Rewrite using `[hx₀, ← Category.assoc, ← spMap_comp]`. Conclude with `congrArg (fun f => spMap f ≫ x₀) (RingHom.ext fun a => σ.commutes a)`.
-/
theorem exists_rational_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D n hn hodd hnu R₁ _ _ _ ρ D₁ A hρ hP hS hU
  have hn1 : 1 ≤ n := hn.one_lt.le
  have hR₁ : Base R₁ := ⟨hρ.1, by haveI := hR.2; exact charZero_of_injective_ringHom hρ.2.1⟩
  obtain ⟨EQ, fQ, hQ⟩ := GlobalTheory.T.degenerationQuotientPoints_rational_finiteExtension R₁ hR₁ D₁ n hn1
  obtain ⟨EA, fA, hA⟩ := GlobalTheory.T.exists_finite_extension_fraction_field_uniform R₁ hR₁ A n hn1
  haveI := fQ
  haveI := fA
  obtain ⟨R₂, _, _, _, i₁₂, e, hi₁₂, hi₁₂ρ, hloc, he⟩ := GlobalTheory.T.exists_finiteExtension_realising_subextension R hR R₁ ρ hρ (EQ ⊔ EA) inferInstance
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ i₁₂ hi₁₂.2.1 hloc D₁
  have hP₂ := nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ i₁₂ D.toPre D₁.toPre D₂.toPre hi₁₂.2.1 hP hD₂
  have hle : nonZeroDivisors R₁ ≤ (nonZeroDivisors R₂).comap i₁₂ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i₁₂ hi₁₂.2.1
  let ga : FractionRing R₁ →+* FractionRing R₂ := IsLocalization.map (FractionRing R₂) i₁₂ hle
  obtain ⟨A₂, g, hg, -, hm, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap ga) A
  have gp : IsGrpPullback A₂.A A.A (spMap ga) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact congrArg (·.left) (hm T x y).symm⟩
  have hlb : LBIso A₂.L (A.L.pull g) := LBIso.symm ⟨t, ht⟩
  have hfib : IsFib i₁₂ A A₂ g := ⟨ga, fun r => IsLocalization.map_eq hle r, gp, hlb⟩
  have hS₂ : (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) := by
    letI := A.isAb.comm
    letI := A₂.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A A₂.A (spMap ga) g A.L A₂.L A.isLB A₂.isLB gp hlb hS
  let eQ : EQ →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_left : EQ ≤ EQ ⊔ EA)).toRingHom
  let eA : EA →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_right : EA ≤ EQ ⊔ EA)).toRingHom
  have hrat := hQ R₂ i₁₂ eQ hi₁₂ hloc (fun r => he r) D₂ hD₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, i₁₂.comp ρ, D₂, A₂, hi₁₂ρ, hP₂, hS₂,
    GlobalTheory.T.uniformisedTrait_moves_to_finite_extension R₁ hR₁ D₁ A hU R₂ i₁₂ hi₁₂ hloc D₂ hD₂ A₂ g hfib, fun σ => ⟨GlobalTheory.T.galois_fixes_quotientPoints_of_rational R₂ D₂ n hrat σ, fun x hx => ?_⟩⟩
  obtain ⟨x₀, hx₀⟩ := hA R₂ i₁₂ eA hi₁₂.2.1 (fun r => he r) A₂ g hfib x hx
  rw [hx₀, ← Category.assoc, ← spMap_comp]
  exact congrArg (fun f => spMap f ≫ x₀) (RingHom.ext fun a => σ.commutes a)

end GlobalTheory.Mum.Enlarge
