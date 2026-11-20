import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

/- English proof (translation)
Use `letI := algVia σ E`. Use `letI := algVia σ E'`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(spMap (φ : E →+* E') ≫ y.left) ≫ q = spMap (φ : E →+* E') ≫ (y.left ≫ q)`. Rewrite using `[Category.assoc]`.
-/
theorem ptVia_spOver (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E E' : Type} [CommRing E] [Algebra R' E]
    [CommRing E'] [Algebra R' E'] (φ : E →ₐ[R'] E') (y : Pt X' E) :
    ptVia w (spOver φ ≫ y) =
      @CategoryStruct.comp _ _ _ _ _ (@spOver R _ E E' _ (algVia σ E) _ (algVia σ E') (homVia σ φ)) (ptVia w y) := by
  letI := algVia σ E
  letI := algVia σ E'
  apply Over.OverMorphism.ext
  change (spMap (φ : E →+* E') ≫ y.left) ≫ q = spMap (φ : E →+* E') ≫ (y.left ≫ q)
  rw [Category.assoc]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h E _ _ E' _ _ E'' _ _ φ ψ y _`. Use `letI := algVia σ E`. Use `letI := algVia σ E'`. Use `letI := algVia σ E''`.

Establish `e` using `h E E' E'' (homVia σ φ) (homVia σ ψ) (ptVia w y) (sm_whole _)`. Establish `hc : (homVia σ ψ).comp (homVia σ φ) = homVia σ (ψ.comp φ)` using `AlgHom.ext fun _ ↦ rfl`. Rewrite `e` using `[hc, ← ptVia_spOver]`. Conclude with `e`. Introduce and unpack `⟨k, hk⟩`.

Use `⟨fun E _ _ y ↦ @k E _ (algVia σ E) (ptVia w y), ?_⟩` and prove the remaining obligations. Introduce `E _ _ E' _ _ φ y _`. Use `letI := algVia σ E`. Use `letI := algVia σ E'`. Establish `e` using `hk E E' (homVia σ φ) (ptVia w y) (sm_whole _)`.

Rewrite `e` using `[← ptVia_spOver]`. Conclude with `e`.
-/
theorem bcPull_coc_cob (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) :
    (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧
      ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  constructor
  · intro h E _ _ E' _ _ E'' _ _ φ ψ y _
    letI := algVia σ E
    letI := algVia σ E'
    letI := algVia σ E''
    have e := h E E' E'' (homVia σ φ) (homVia σ ψ) (ptVia w y) (sm_whole _)
    have hc : (homVia σ ψ).comp (homVia σ φ) = homVia σ (ψ.comp φ) := AlgHom.ext fun _ ↦ rfl
    rw [hc, ← ptVia_spOver] at e
    exact e
  · rintro ⟨k, hk⟩
    refine ⟨fun E _ _ y ↦ @k E _ (algVia σ E) (ptVia w y), ?_⟩
    intro E _ _ E' _ _ φ y _
    letI := algVia σ E
    letI := algVia σ E'
    have e := hk E E' (homVia σ φ) (ptVia w y) (sm_whole _)
    rw [← ptVia_spOver] at e
    exact e

/- English proof (translation)
The claim follows from `fun _ _ _ _ _ _ _ _ w u ↦ bcPull_coc_cob w u`.
-/
theorem bcPull_keeps : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) :=
  fun _ _ _ _ _ _ _ _ w u ↦ bcPull_coc_cob w u

end GlobalTheory.PtExt
