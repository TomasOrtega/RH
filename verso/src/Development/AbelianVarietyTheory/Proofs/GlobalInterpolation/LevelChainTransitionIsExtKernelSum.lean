import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

/- English proof (translation)
Introduce `D u X i M M' K φ Φ hK hΦ`. Use `⟨fun c' => ?_, fun g' p' => ?_⟩` and prove the remaining obligations. Use `show Formalism.ThetaLiftIndependence.kerOpM (X.C.wt i) (X.C.Kmap i) φ c' = _`. Unfold `Formalism.ThetaLiftIndependence.kerOpM`. Rewrite using `[Submodule.coe_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hΦ.1 c, K.Kmap_eq, Submodule.coe_smul]`. Simplify using `only [map_sum, map_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hK g']`.
-/
theorem isExt_KT : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (M' : PtModel X (i + 1)) (K : KerPt M M') (φ : Fn X i) (Φ : M.Pt → M.Val), K.TgtEq → M.IsExt φ Φ → M'.IsExt (KT X i φ) (fun p' => ∑ c, X.C.wt i c • K.k (M.rep c) p' (Φ (M.rep c))) := by
  intro D u X i M M' K φ Φ hK hΦ
  refine ⟨fun c' => ?_, fun g' p' => ?_⟩
  · show Formalism.ThetaLiftIndependence.kerOpM (X.C.wt i) (X.C.Kmap i) φ c' = _
    unfold Formalism.ThetaLiftIndependence.kerOpM
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hΦ.1 c, K.Kmap_eq, Submodule.coe_smul]
  · simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hK g']

end GlobalTheory.LvT
