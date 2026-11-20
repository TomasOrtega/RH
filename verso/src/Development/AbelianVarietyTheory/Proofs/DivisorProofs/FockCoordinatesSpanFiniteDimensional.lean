import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ProdModeCharExp

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

/- English proof (translation)
Introduce `n ε M _ _ E Z hZ hK`. Establish `hle : coordSpan Z ≤ ⨆ s : Finset (Fin (n * n)), Z.map (tcoef (M` using `M) ((fockBasis n).coord s)) := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `v ⟨s, y, hy, rfl⟩`. Conclude with `(le_iSup (fun s : Finset (Fin (n * n)) => Z.map (tcoef (M := M) ((fockBasis n).coord s))) s) (Submodule.mem_map_of_mem hy)`.

Use `⟨Submodule.finiteDimensional_of_le hle, ?_⟩` and prove the remaining obligations. Introduce `a b hab v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨s, y, hy, rfl⟩` from `hx`.

Establish `e` using `tco_diagE (ε := ε) E a b y s`. Establish `e2` using `tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y`. Establish `h1 : E a b (tcoef ((fockBasis n).coord s) y) = tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a b y) - tcoef ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n` using `n)) cmFock a b) y := by`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws.

Use `show E a b (tcoef ((fockBasis n).coord s) y) ∈ coordSpan Z`. Rewrite using `[h1, e2]`. Use `Submodule.sub_mem _ (Submodule.subset_span ⟨s, _, hK a b hab y hy, rfl⟩) ?_` and prove the remaining obligations. Use `Submodule.sum_mem _ fun s' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s', y, hy, rfl⟩)` and prove the remaining obligations. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem fockCoordinates_span_finiteDimensional : CoordFD := by
  intro n ε M _ _ E Z hZ hK
  have hle : coordSpan Z ≤ ⨆ s : Finset (Fin (n * n)), Z.map (tcoef (M := M) ((fockBasis n).coord s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨s, y, hy, rfl⟩
    exact (le_iSup (fun s : Finset (Fin (n * n)) => Z.map (tcoef (M := M) ((fockBasis n).coord s))) s)
      (Submodule.mem_map_of_mem hy)
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  intro a b hab v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, y, hy, rfl⟩ := hx
    have e := tco_diagE (ε := ε) E a b y s
    have e2 := tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y
    have h1 : E a b (tcoef ((fockBasis n).coord s) y) =
        tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a b y) -
          tcoef ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y := by
      rw [e]; abel
    show E a b (tcoef ((fockBasis n).coord s) y) ∈ coordSpan Z
    rw [h1, e2]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, _, hK a b hab y hy, rfl⟩) ?_
    refine Submodule.sum_mem _ fun s' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s', y, hy, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.PsCo.PcEF
