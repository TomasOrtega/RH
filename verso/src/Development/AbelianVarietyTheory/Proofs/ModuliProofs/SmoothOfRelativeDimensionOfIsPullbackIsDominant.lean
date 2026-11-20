import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Substitute using the available equality. Supply the required witnesses or components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem smoothOfRelativeDimension_of_isPullback_isDominant :
    ∀ (X U Y Y' : Scheme.{0}) (j : U ⟶ X) (p : Y ⟶ X) (p' : Y' ⟶ U) (φ : Y' ⟶ Y) (g : ℕ),
      IsPullback φ p' p j → IsDominant j → Smooth p → SmoothOfRelativeDimension g p' →
        SmoothOfRelativeDimension g p := by
  intro X U Y Y' j p p' φ g hpb hj hp hg
  have := hp
  have key : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ p) := by
    intro y
    obtain ⟨n, W, hyW, hn⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim p y
    have hopen : IsOpen (p '' (W : Set Y)) := p.isOpenMap _ W.isOpen
    obtain ⟨u, w, hwW, hwu⟩ := hj.denseRange.exists_mem_open hopen ⟨p y, y, hyW, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback w u hwu
    have h1 : φ (hpb.isoPullback.inv z) = w := by
      rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz1]
    have hng := ReciprocityTheory.ChartRestriction.G.H1.dim_base hpb hn hg (hpb.isoPullback.inv z) (h1 ▸ hwW)
    subst hng
    exact ⟨W, hyW, hn⟩
  choose W hyW hW using key
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} g)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) W ?_ hW
  rw [eq_top_iff]
  intro y _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩

end GlobalTheory
