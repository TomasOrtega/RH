import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `g r Hm Hm' l hspan h`. Establish `h1 : ∀ z, ∀ j, (hermForm Hm z (l j)).im = (hermForm Hm' z (l j)).im`. Introduce `z j`. Establish `hz : z ∈ Submodule.span ℝ (Set.range l)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `h i j`. Consider the case `zero => simp [hermForm]`. Consider the case `add x y _ _ hx hy`.

Simplify using `only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢`. Rewrite using `[hx, hy]`. Consider the case `smul a x _ hx`. Simplify using `only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢`. Rewrite using `[hx]`.

Establish `h2 : ∀ z w, (hermForm Hm z w).im = (hermForm Hm' z w).im`. Introduce `z w`. Establish `hw : w ∈ Submodule.span ℝ (Set.range l)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨j, rfl⟩` from `hx`. Conclude with `h1 z j`. Consider the case `zero => simp [hermForm]`. Consider the case `add x y _ _ hx hy`. Simplify using `only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢`.

Rewrite using `[hx, hy]`. Consider the case `smul a x _ hx`. Simplify using `only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢`. Rewrite using `[hx]`. Use extensionality with `i j`.

Establish `e1` using `h2 (Pi.single i 1) (Pi.single j 1)`. Establish `e2` using `h2 (Pi.single i Complex.I) (Pi.single j 1)`. Simplify using `[hermForm] at e1 e2`. Conclude with `Complex.ext e2 e1`.
-/
theorem hermForm_eq_of_im_eq_on_span : ∀ (g r : ℕ) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ), Submodule.span ℝ (Set.range l) = ⊤ → (∀ i j, (hermForm Hm (l i) (l j)).im = (hermForm Hm' (l i) (l j)).im) → Hm = Hm' := by
  intro g r Hm Hm' l hspan h
  have h1 : ∀ z, ∀ j, (hermForm Hm z (l j)).im = (hermForm Hm' z (l j)).im := by
    intro z j
    have hz : z ∈ Submodule.span ℝ (Set.range l) := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h i j
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm Hm z w).im = (hermForm Hm' z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ (Set.range l) := hspan ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact h1 z j
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1

end GlobalTheory
