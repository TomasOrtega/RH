import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnectedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ G _ hG O hO`. Use `haveI := hG.smooth`. Use `haveI := hG.geomConnected`. Set `g₀ : G.left` to `(1 : Over.mk (𝟙 (Sp R)) ⟶ G).left (closedPoint R)`. Establish `hg₀ : G.hom g₀ = closedPoint R`.

Use `Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)` as an intermediate fact. Express the relevant statement in the definitionally equal form `((1 : Over.mk (𝟙 (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `: IrreducibleSpace G.left` using `GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain R G inferInstance inferInstance ⟨g₀⟩`.

Conclude with `O.isOpen.dense ⟨g₀, hO g₀ hg₀⟩`.
-/
theorem dense_of_closedFibre_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G],
    IsSemiAbelian G → ∀ O : G.left.Opens, (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → Dense (O : Set G.left) := by
  intro R _ _ _ G _ hG O hO
  haveI := hG.smooth
  haveI := hG.geomConnected
  let g₀ : G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left (closedPoint R)
  have hg₀ : G.hom g₀ = closedPoint R := by
    have := Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)
    change ((1 : Over.mk (𝟙 (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
    rw [this]; rfl
  have : IrreducibleSpace G.left := GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain R G inferInstance inferInstance ⟨g₀⟩
  exact O.isOpen.dense ⟨g₀, hO g₀ hg₀⟩

/- English proof (translation)
Use `algebraize [ρ]`. Establish `: Algebra.IsIntegral R R'` using `⟨fun x => hf.to_isIntegral x⟩`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap ρ (maximalIdeal R') = maximalIdeal R`. Establish `: (Ideal.comap (algebraMap R R') (maximalIdeal R')).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R')`.

Conclude with `IsLocalRing.eq_maximalIdeal this`.
-/
theorem spMap_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) : spMap ρ (closedPoint R') = closedPoint R := by
  algebraize [ρ]
  have : Algebra.IsIntegral R R' := ⟨fun x => hf.to_isIntegral x⟩
  apply PrimeSpectrum.ext
  show Ideal.comap ρ (maximalIdeal R') = maximalIdeal R
  have : (Ideal.comap (algebraMap R R') (maximalIdeal R')).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R')
  exact IsLocalRing.eq_maximalIdeal this

/- English proof (translation)
Use `haveI := hG'.smooth`. Use `haveI := N.isOpen`. Establish `hred : IsReduced G'.left` using `GlobalTheory.isReduced_of_smooth_of_isReduced G'.hom`. Establish `hd` using `dense_of_closedFibre_sub R' G' hG' N.u.opensRange (fun x hx => by`. Take `⟨y, hy⟩` from `N.all x (by rw [hx]; exact spMap_closedPoint_of_finite ρ hf)`.

Conclude with `⟨y, hy⟩)`. Use `haveI : IsDominant N.u := ⟨by simpa [DenseRange] using hd⟩`. Establish `hσ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ`. Unfold `spMap`. Rewrite using `[← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `r`. Conclude with `σ.2 r`. Use `ext_of_isDominant_of_isSeparated G.hom ?_ N.u ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hβ, ← Category.assoc, hg, Category.assoc, hσ]`.

Take `⟨x₁, h1, -, h3⟩` from `hinv _ (pullback.snd _ _) (pullback.fst _ _) N.u ⟨𝟙 _, by simp, by simp, by simp⟩`. Rewrite using `[← Category.assoc, ← h3, Category.assoc, hu, ← Category.assoc, h1]`.
-/
theorem comp_eq_of_near {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) (G' : Over (Sp R')) [GrpObj G'] (hG' : IsSemiAbelian G') (N : Near (spMap ρ) G')
    (G : Over (Sp R)) [GrpObj G] (hG : IsSeparated G.hom) (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ)
    (i : N.U ⟶ G) (hu : N.u ≫ β = pullback.fst _ _ ≫ i.left) (σ : Gal ρ) (g : G'.left ⟶ G'.left)
    (hg : g ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ))
    (hinv : ∀ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x →
      N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ g)) : g ≫ β = β := by
  haveI := hG'.smooth
  haveI := N.isOpen
  have hred : IsReduced G'.left := GlobalTheory.isReduced_of_smooth_of_isReduced G'.hom
  have hd := dense_of_closedFibre_sub R' G' hG' N.u.opensRange (fun x hx => by
    obtain ⟨y, hy⟩ := N.all x (by rw [hx]; exact spMap_closedPoint_of_finite ρ hf)
    exact ⟨y, hy⟩)
  haveI : IsDominant N.u := ⟨by simpa [DenseRange] using hd⟩
  have hσ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact σ.2 r
  refine ext_of_isDominant_of_isSeparated G.hom ?_ N.u ?_
  · rw [Category.assoc, hβ, ← Category.assoc, hg, Category.assoc, hσ]
  · obtain ⟨x₁, h1, -, h3⟩ := hinv _ (pullback.snd _ _) (pullback.fst _ _) N.u ⟨𝟙 _, by simp, by simp, by simp⟩
    rw [← Category.assoc, ← h3, Category.assoc, hu, ← Category.assoc, h1]

end GlobalTheory.Mum
