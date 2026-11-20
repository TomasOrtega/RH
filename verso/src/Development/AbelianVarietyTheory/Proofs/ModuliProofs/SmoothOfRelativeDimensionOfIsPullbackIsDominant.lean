import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Introduce `X U Y Y' j p p' φ g hpb hj hp hg`. Use `hp` as an intermediate fact. Establish `key : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ p)`. Introduce `y`. Take `⟨n, W, hyW, hn⟩` from `ReciprocityTheory.ChartRestriction.G.H1.exists_dim p y`.

Establish `hopen : IsOpen (p '' (W : Set Y))` using `p.isOpenMap _ W.isOpen`. Take `⟨u, w, hwW, hwu⟩` from `hj.denseRange.exists_mem_open hopen ⟨p y, y, hyW, rfl⟩`. Take `⟨z, hz1, -⟩` from `Scheme.Pullback.exists_preimage_pullback w u hwu`. Establish `h1 : φ (hpb.isoPullback.inv z) = w`. Rewrite using `[← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz1]`.

Establish `hng` using `ReciprocityTheory.ChartRestriction.G.H1.dim_base hpb hn hg (hpb.isoPullback.inv z) (h1 ▸ hwW)`. Substitute `hng` using the available equality. Conclude with `⟨W, hyW, hn⟩`. Use `choose W hyW hW using key`. Establish `hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g)` using `HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} g)`.

Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) W ?_ hW` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `y _`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩`.
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
