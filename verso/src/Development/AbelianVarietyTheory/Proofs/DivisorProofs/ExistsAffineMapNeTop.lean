import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.PointSec

/- English proof (translation)
Introduce `R' _ X X' s' φ hs m hm`. Take `⟨x', hx'⟩` from `hs.surj (⟨m, hm.isPrime⟩ : PrimeSpectrum R')`. Take `⟨U, hU, hxU, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show φ.base x' ∈ (⊤ : X.Opens) from trivial)`. Use `⟨⟨U, hU⟩, ?_⟩` and prove the remaining obligations. Establish `hx : x' ∈ φ ⁻¹ᵁ U` using `hxU`.

Introduce `htop`. Set `g : Sec s' (φ ⁻¹ᵁ U) →+* X'.presheaf.stalk x'` to `(X'.presheaf.germ (φ ⁻¹ᵁ U) x' hx).hom`. Establish `key : ∀ a ∈ m, ¬ IsUnit (g (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a))`. Introduce `a ha hu`. Establish `h1 : x' ∈ X'.basicOpen (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a : Γ(X', φ ⁻¹ᵁ U))` using `(Scheme.mem_basicOpen _ _ _ hx).2 hu`.

Express the relevant statement in the definitionally equal form `x' ∈ X'.basicOpen ((X'.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)).op) (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a))) at h1`. Establish `h2 : x' ∈ X'.basicOpen (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a))` using `Scheme.basicOpen_restrict X' (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)) _ h1`. Establish `h3 : x' ∈ s' ⁻¹ᵁ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a)`. Rewrite using `[Scheme.preimage_basicOpen]`. Conclude with `h2`.

Establish `h4 : s'.base x' ∈ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a)` using `h3`. Rewrite `h4` using `[basicOpen_eq_of_affine]`. Establish `h2 : s'.base x' ∈ PrimeSpectrum.basicOpen a` using `h4`. Rewrite `h2` using `[hx']`. Conclude with `h2 ha`.

Establish `hle : Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m ≤ (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Conclude with `key a ha`. Establish `h1 : (1 : Sec s' (φ ⁻¹ᵁ U)) ∈ (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g` using `hle (by rw [show Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m = ⊤ from htop]; trivial)`.

Rewrite `h1` using `[Ideal.mem_comap, map_one]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one`.
-/
theorem exists_affine_map_ne_top : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  intro R' _ X X' s' φ hs m hm
  obtain ⟨x', hx'⟩ := hs.surj (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ.base x' ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, ?_⟩
  have hx : x' ∈ φ ⁻¹ᵁ U := hxU
  intro htop
  let g : Sec s' (φ ⁻¹ᵁ U) →+* X'.presheaf.stalk x' := (X'.presheaf.germ (φ ⁻¹ᵁ U) x' hx).hom
  have key : ∀ a ∈ m, ¬ IsUnit (g (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a)) := by
    intro a ha hu
    have h1 : x' ∈ X'.basicOpen (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a : Γ(X', φ ⁻¹ᵁ U)) :=
      (Scheme.mem_basicOpen _ _ _ hx).2 hu
    change x' ∈ X'.basicOpen ((X'.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)).op)
      (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a))) at h1
    have h2 : x' ∈ X'.basicOpen (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a)) :=
      Scheme.basicOpen_restrict X' (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)) _ h1
    have h3 : x' ∈ s' ⁻¹ᵁ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := by
      rw [Scheme.preimage_basicOpen]; exact h2
    have h4 : s'.base x' ∈ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := h3
    rw [basicOpen_eq_of_affine] at h4
    have h2 : s'.base x' ∈ PrimeSpectrum.basicOpen a := h4
    rw [hx'] at h2
    exact h2 ha
  have hle : Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m ≤
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact key a ha
  have h1 : (1 : Sec s' (φ ⁻¹ᵁ U)) ∈ (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g :=
    hle (by rw [show Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m = ⊤ from htop]; trivial)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
end GlobalTheory.PointSec
