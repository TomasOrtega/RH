import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

/- English proof (translation)
Use `show (z ≫ (Over.pullback f).map ι[G']).left ≫ _ = _`. Rewrite using `[Over.comp_left, Category.assoc]`. Use `congr 1`. Simplify using `only [Over.pullback_map_left]`. Apply the tactic sequence `first | exact pullback.lift_fst _ _ _ | erw [pullback.lift_fst]`.
-/
theorem inv_pullback_left_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (G' : Over Y) [GrpObj G'] {T : Over X}
    (z : T ⟶ (Over.pullback f).obj G') :
    (z⁻¹).left ≫ pullback.fst G'.hom f = z.left ≫ pullback.fst G'.hom f ≫ ι[G'].left := by
  show (z ≫ (Over.pullback f).map ι[G']).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left]
  first | exact pullback.lift_fst _ _ _ | erw [pullback.lift_fst]

/- English proof (translation)
Introduce `R _ _ _ _ S π hP hS hI G' _ G β hsm hpb φ hφ hc`. Establish `hfl : Flat G.hom` using `inferInstance`. Establish `D` using `fun (W : Scheme.{0}) => GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S G.left G'.left W π G.hom β G'.hom hP hS hI hfl hpb`. Establish `epi : ∀ {W : Scheme.{0}} (a b : G.left ⟶ W), β ≫ a = β ≫ b → a = b`. Introduce `W a b hab`.

Take `⟨h₀, -, hu⟩` from `D W (β ≫ a) (by rw [pullback.condition_assoc])`. Conclude with `(hu a rfl).trans (hu b hab.symm).symm`. Establish `hw : β ≫ G.hom = G'.hom ≫ π` using `hpb.w`. Use `set a₁ := pullback.fst β β`. Use `set a₂ := pullback.snd β β`.

Establish `hσ : (a₁ ≫ G'.hom) ≫ π = (a₂ ≫ G'.hom) ≫ π`. Simplify using `only [Category.assoc, ← hw]`. Rewrite using `[pullback.condition_assoc]`. Set `σ : pullback β β ⟶ pullback π π` to `pullback.lift _ _ hσ`. Set `x : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G'` to `Over.homMk (pullback.lift a₁ σ (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)`.

Establish `hcx : ∀ y : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G', y.left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β = (y ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β`. Introduce `y`. Rewrite using `[Over.comp_left, Category.assoc, ← hc]`. Establish `h2 : (x ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) = a₂`. Apply `hpb.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, ← hcx x] show pullback.lift a₁ σ _ ≫ _ ≫ β = _`. Rewrite using `[pullback.lift_fst_assoc]`. Conclude with `pullback.condition`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, show (x ≫ φ.hom).left ≫ pullback.snd G'.hom (pullback.snd π π) = σ from Over.w (x ≫ φ.hom)]`. Conclude with `pullback.lift_snd _ _ _`.

Establish `eq : a₁ ≫ ι[G'].left ≫ β = a₂ ≫ ι[G'].left ≫ β`. Use `hcx x⁻¹` as an intermediate fact. Rewrite `this` using `[GrpObj.inv_comp, reassoc_of% inv_pullback_left_fst, reassoc_of% inv_pullback_left_fst, reassoc_of% h2]`. Simplify using `only [x, Over.homMk_left] at this`. Rewrite `this` using `[pullback.lift_fst_assoc]`. Then use the resulting hypothesis.

Take `⟨h₀, hh₀, -⟩` from `D G.left (ι[G'].left ≫ β) eq`. Establish `hover : h₀ ≫ G.hom = G.hom`. Apply `epi` to reduce the goal to its premises. Rewrite using `[reassoc_of% hh₀, hw, ← Category.assoc, Over.w ι[G']]`. Use `⟨Over.homMk h₀ hover, ?_⟩` and prove the remaining obligations.

Introduce `T x' x₀ hx`. Rewrite using `[Over.comp_left]`. Use `show x₀.left ≫ h₀ = _`. Rewrite using `[hx, Category.assoc, hh₀]`. Use `show _ = (x' ≫ ι[G']).left ≫ β`.

Rewrite using `[Over.comp_left, Category.assoc]`.
-/
theorem exists_inv_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ i : G ⟶ G, ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hsm hpb φ hφ hc
  have hfl : Flat G.hom := inferInstance
  have D := fun (W : Scheme.{0}) => GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S G.left G'.left W π G.hom β G'.hom hP hS hI hfl hpb
  have epi : ∀ {W : Scheme.{0}} (a b : G.left ⟶ W), β ≫ a = β ≫ b → a = b := by
    intro W a b hab
    obtain ⟨h₀, -, hu⟩ := D W (β ≫ a) (by rw [pullback.condition_assoc])
    exact (hu a rfl).trans (hu b hab.symm).symm
  have hw : β ≫ G.hom = G'.hom ≫ π := hpb.w
  set a₁ := pullback.fst β β
  set a₂ := pullback.snd β β
  have hσ : (a₁ ≫ G'.hom) ≫ π = (a₂ ≫ G'.hom) ≫ π := by
    simp only [Category.assoc, ← hw]; rw [pullback.condition_assoc]
  let σ : pullback β β ⟶ pullback π π := pullback.lift _ _ hσ
  let x : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G' :=
    Over.homMk (pullback.lift a₁ σ (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcx : ∀ y : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G',
      y.left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β =
        (y ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
    intro y; rw [Over.comp_left, Category.assoc, ← hc]
  have h2 : (x ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) = a₂ := by
    apply hpb.hom_ext
    · rw [Category.assoc, ← hcx x]
      show pullback.lift a₁ σ _ ≫ _ ≫ β = _
      rw [pullback.lift_fst_assoc]
      exact pullback.condition
    · rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (x ≫ φ.hom).left ≫ pullback.snd G'.hom (pullback.snd π π) = σ from Over.w (x ≫ φ.hom)]
      exact pullback.lift_snd _ _ _
  have eq : a₁ ≫ ι[G'].left ≫ β = a₂ ≫ ι[G'].left ≫ β := by
    have := hcx x⁻¹
    rw [GrpObj.inv_comp, reassoc_of% inv_pullback_left_fst, reassoc_of% inv_pullback_left_fst,
      reassoc_of% h2] at this
    simp only [x, Over.homMk_left] at this
    rwa [pullback.lift_fst_assoc] at this
  obtain ⟨h₀, hh₀, -⟩ := D G.left (ι[G'].left ≫ β) eq
  have hover : h₀ ≫ G.hom = G.hom := by
    apply epi
    rw [reassoc_of% hh₀, hw, ← Category.assoc, Over.w ι[G']]
  refine ⟨Over.homMk h₀ hover, ?_⟩
  intro T x' x₀ hx
  rw [Over.comp_left]
  show x₀.left ≫ h₀ = _
  rw [hx, Category.assoc, hh₀]
  show _ = (x' ≫ ι[G']).left ≫ β
  rw [Over.comp_left, Category.assoc]

end GlobalTheory.Mum
