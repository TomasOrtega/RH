import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeneratingSectionAllFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapAffineNormalBaseUniversalGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

/- English proof (translation)
Introduce `S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hu hn hP U hD hN hI hC x hx`. Set `R : Type` to `Γ(X, U)`. Establish `hU : IsAffineOpen (U : X.Opens)` using `U.2`. Set `β : o →+* R` to `(Spec.preimage (hU.fromSpec ≫ s)).hom`. Establish `hβ : spMap β = hU.fromSpec ≫ s` using `Spec.map_preimage _`.

Set `p : PrimeSpectrum R` to `hU.primeIdealOf ⟨x, hx⟩`. Take `⟨r, hr, θ, hθ⟩` from `GlobalTheory.T.exists_basicOpen_generating_section_all_fibres S G L hL g R (hU.fromSpec ≫ q) (hP R hU.fromSpec) p`. Set `Rr` to `Localization.Away r`. Establish `hr0 : r ≠ 0` using `fun h => hr (h ▸ p.asIdeal.zero_mem)`. Establish `hle : Submonoid.powers r ≤ nonZeroDivisors R` using `powers_le_nonZeroDivisors_of_noZeroDivisors hr0`.

Use `haveI : IsDomain Rr := IsLocalization.isDomain_localization hle`. Use `haveI : IsNoetherianRing Rr := IsLocalization.isNoetherianRing (Submonoid.powers r) Rr hN`. Use `haveI : IsIntegrallyClosed Rr := isIntegrallyClosed_of_isLocalization Rr _ hle`. Establish `hinj : Function.Injective (algebraMap R Rr)` using `IsLocalization.injective Rr hle`. Use `haveI : CharZero Rr := charZero_of_injective_algebraMap hinj`.

Set `β' : o →+* Rr` to `(algebraMap R Rr).comp β`. Establish `hu' : IsUnit (m : Rr)`. Use `hu.map β'` as an intermediate fact. Simplify using `using this`. Establish `hP' : PolFib G L g (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q)`.

Use `hP Rr (spMap (algebraMap R Rr) ≫ hU.fromSpec)` as an intermediate fact. Simplify `this` using `[Category.assoc]`. Take `⟨f, hf, hT⟩` from `GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator S G L ρ hL hρ g m n o Rr β' (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) θ hmo hm3 hu' hn hP' hθ`. Set `Wo : X.Opens` to `X.basicOpen r`. Establish `hW : IsAffineOpen Wo` using `hU.basicOpen r`.

Establish `hxW : x ∈ Wo`. Establish `h1 : hU.fromSpec p ∈ X.basicOpen r` using `by show p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r`. Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Conclude with `hr`. Rewrite `h1` using `[hU.fromSpec_primeIdealOf]`. Then use the resulting hypothesis.

Establish `hle' : Wo ≤ (U : X.Opens)` using `X.basicOpen_le r`. Set `res : R →+* Γ(X, Wo)` to `(X.presheaf.map (homOfLE hle').op).hom`. Establish `hres : IsUnit (res r)` using `RingedSpace.isUnit_res_basicOpen X.toRingedSpace r`. Set `lft : Rr →+* Γ(X, Wo)` to `IsLocalization.Away.lift r hres`. Establish `hlft : lft.comp (algebraMap R Rr) = res` using `IsLocalization.Away.lift_comp r hres`.

Set `e : Wo.toScheme ⟶ Sp Rr` to `hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lft)`. Establish `he : e ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec = Wo.ι`. Establish `: Spec.map (CommRingCat.ofHom lft) ≫ spMap (algebraMap R Rr) = Spec.map (X.presheaf.map (homOfLE hle').op)`. Rewrite using `[spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlft]`. Both sides reduce to the same expression.

Simplify using `only [e, Category.assoc]`. Rewrite using `[reassoc_of% this, hU.map_fromSpec hW, hW.isoSpec_hom_fromSpec]`. Use `⟨Wo, e ≫ f, hxW, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hf, show spMap β' = spMap (algebraMap R Rr) ≫ spMap β from by`. Rewrite using `[spMap, spMap, spMap, ← Spec.map_comp]`.

Use the proof step `rfl, hβ, ← he]`. Simplify using `only [Category.assoc]`. Introduce `K _ x' c hc`. Establish `hc' : HasTh G L ρ m ((x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) c`. Establish `: (x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q = x' ≫ Wo.ι ≫ q`.

Rewrite using `[← he]`. Simplify using `only [Category.assoc]`. Rewrite using `[this]`. Conclude with `hc`. Use `hT K (x' ≫ e) c hc'` as an intermediate fact.

Simplify `this` using `[Category.assoc]`.
-/
theorem exists_nbhd_thetaMap : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    ∀ (U : X.affineOpens), IsDomain Γ(X, U) → IsNoetherianRing Γ(X, U) → IsIntegrallyClosed Γ(X, U) → CharZero Γ(X, U) →
    ∀ x ∈ (U : X.Opens), ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧ ThMap G L ρ m (W.ι ≫ q) h := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hu hn hP U hD hN hI hC x hx
  let R : Type := Γ(X, U)
  have hU : IsAffineOpen (U : X.Opens) := U.2

  let β : o →+* R := (Spec.preimage (hU.fromSpec ≫ s)).hom
  have hβ : spMap β = hU.fromSpec ≫ s := Spec.map_preimage _
  let p : PrimeSpectrum R := hU.primeIdealOf ⟨x, hx⟩
  obtain ⟨r, hr, θ, hθ⟩ := GlobalTheory.T.exists_basicOpen_generating_section_all_fibres S G L hL g R (hU.fromSpec ≫ q) (hP R hU.fromSpec) p
  let Rr := Localization.Away r
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  haveI : IsDomain Rr := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rr := IsLocalization.isNoetherianRing (Submonoid.powers r) Rr hN
  haveI : IsIntegrallyClosed Rr := isIntegrallyClosed_of_isLocalization Rr _ hle
  have hinj : Function.Injective (algebraMap R Rr) := IsLocalization.injective Rr hle
  haveI : CharZero Rr := charZero_of_injective_algebraMap hinj
  let β' : o →+* Rr := (algebraMap R Rr).comp β
  have hu' : IsUnit (m : Rr) := by
    have := hu.map β'
    simpa using this
  have hP' : PolFib G L g (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) := by
    have := hP Rr (spMap (algebraMap R Rr) ≫ hU.fromSpec)
    simpa [Category.assoc] using this
  obtain ⟨f, hf, hT⟩ := GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator S G L ρ hL hρ g m n o Rr β' (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) θ
    hmo hm3 hu' hn hP' hθ

  let Wo : X.Opens := X.basicOpen r
  have hW : IsAffineOpen Wo := hU.basicOpen r
  have hxW : x ∈ Wo := by
    have h1 : hU.fromSpec p ∈ X.basicOpen r := by
      show p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
      rw [hU.fromSpec_preimage_basicOpen]; exact hr
    rwa [hU.fromSpec_primeIdealOf] at h1
  have hle' : Wo ≤ (U : X.Opens) := X.basicOpen_le r
  let res : R →+* Γ(X, Wo) := (X.presheaf.map (homOfLE hle').op).hom
  have hres : IsUnit (res r) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace r
  let lft : Rr →+* Γ(X, Wo) := IsLocalization.Away.lift r hres
  have hlft : lft.comp (algebraMap R Rr) = res := IsLocalization.Away.lift_comp r hres
  let e : Wo.toScheme ⟶ Sp Rr := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lft)
  have he : e ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec = Wo.ι := by
    have : Spec.map (CommRingCat.ofHom lft) ≫ spMap (algebraMap R Rr) =
        Spec.map (X.presheaf.map (homOfLE hle').op) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlft]
      rfl
    simp only [e, Category.assoc]
    rw [reassoc_of% this, hU.map_fromSpec hW, hW.isoSpec_hom_fromSpec]
  refine ⟨Wo, e ≫ f, hxW, ?_, ?_⟩
  · rw [Category.assoc, hf, show spMap β' = spMap (algebraMap R Rr) ≫ spMap β from by
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl, hβ, ← he]
    simp only [Category.assoc]
  · intro K _ x' c hc
    have hc' : HasTh G L ρ m ((x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) c := by
      have : (x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q = x' ≫ Wo.ι ≫ q := by
        rw [← he]; simp only [Category.assoc]
      rw [this]; exact hc
    have := hT K (x' ≫ e) c hc'
    simpa [Category.assoc] using this

end GlobalTheory.UMin
