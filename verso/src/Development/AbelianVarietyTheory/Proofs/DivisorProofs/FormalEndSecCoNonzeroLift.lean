import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Rewrite `h`, the goal using `[← Scheme.preimage_basicOpen]`. Conclude with `h`.
-/
theorem mem_basicOpen_of_comp {X Y Y' : Scheme.{0}} (c : Y ⟶ Y') (f : Y' ⟶ X) {U : X.Opens} (r : Γ(X, U))
    {y : Y} (h : y ∈ Y.basicOpen ((c ≫ f).app U r)) : c y ∈ Y'.basicOpen (f.app U r) := by
  rw [← Scheme.preimage_basicOpen] at h ⊢
  exact h

/- English proof (translation)
Take `⟨y, i, i', h1, h2⟩` from `h`. Conclude with `⟨c y, i, i', mem_basicOpen_of_comp c u _ h1, mem_basicOpen_of_comp c v _ h2⟩`.
-/
theorem secCoNonzero_of_comp {X Y Y' : Scheme.{0}} (L : LB X) {k k' : ℕ} (c : Y ⟶ Y') (u v : Y' ⟶ X)
    (s : H0 L k) (t : H0 L k') (h : SecCoNonzero L (c ≫ u) (c ≫ v) s t) : SecCoNonzero L u v s t := by
  obtain ⟨y, i, i', h1, h2⟩ := h
  exact ⟨c y, i, i', mem_basicOpen_of_comp c u _ h1, mem_basicOpen_of_comp c v _ h2⟩

/- English proof (translation)
Introduce `R _ _ _ _ D A G _ _ _ U a h' b hb k k' s t h0 e`. Proceed by induction on `e with`. Consider the case `zero => exact h0`. Consider the case `succ e ih`. Apply `secCoNonzero_of_comp U.LG.L (thickMap R (maximalIdeal R) e G)` to reduce the goal to its premises.

Establish `hf : thickMap R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) (e + 1) G).left = (fstG (maximalIdeal R) e G).left` using `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`. Rewrite using `[hf, ← Category.assoc, hb.2.1 e, Category.assoc, hf]`. Conclude with `ih`.
-/
theorem formalEnd_secCoNonzero_lift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), FormalEnd U.toUnifPre a h' b → ∀ (k k' : ℕ) (s : H0 U.LG.L k) (t : H0 U.LG.L k'), SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s t → ∀ e : ℕ, SecCoNonzero U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s t := by
  intro R _ _ _ _ D A G _ _ _ U a h' b hb k k' s t h0 e
  induction e with
  | zero => exact h0
  | succ e ih =>
    apply secCoNonzero_of_comp U.LG.L (thickMap R (maximalIdeal R) e G)
    have hf : thickMap R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) (e + 1) G).left =
        (fstG (maximalIdeal R) e G).left := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [hf, ← Category.assoc, hb.2.1 e, Category.assoc, hf]
    exact ih

end GlobalTheory.Mum
