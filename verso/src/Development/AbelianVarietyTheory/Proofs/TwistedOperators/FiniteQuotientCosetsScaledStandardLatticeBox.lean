import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.BoxCosets

/- English proof (translation)
Establish `e : ∀ c : kˣ, (box n c : Set (n → k)) = Set.pi Set.univ (fun _ => cball c)`. Introduce `c`. Use extensionality with `y`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`. Both sides reduce to the same expression.

Establish `hc : IsCompact (box n c₁ : Set (n → k))`. Rewrite using `[e]`. Conclude with `isCompact_univ_pi fun _ => isCompact_cball c₁`. Establish `ho : IsOpen (box n c₂ : Set (n → k))`. Rewrite using `[e]`.

Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball c₂`. Take `⟨t, -, ht⟩` from `hc.elim_nhds_subcover (fun x => (fun y => y - x) ⁻¹' (box n c₂ : Set (n → k))) (by`. Introduce `x _`. Use `(ho.preimage (continuous_id.sub continuous_const)).mem_nhds ?_` and prove the remaining obligations. Use the proof step `simp)`.

Use `(t.finite_toSet.image (fun x => (Submodule.Quotient.mk x : (n → k) ⧸ box n c₂))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `ht hy` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨x, hx, hxy⟩` from `this`.

Conclude with `⟨x, hx, ((Submodule.Quotient.eq _).2 hxy).symm⟩`.
-/
theorem finite_cosets (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ) :
    {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  have e : ∀ c : kˣ, (box n c : Set (n → k)) = Set.pi Set.univ (fun _ => cball c) := by
    intro c
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  have hc : IsCompact (box n c₁ : Set (n → k)) := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_cball c₁
  have ho : IsOpen (box n c₂ : Set (n → k)) := by
    rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball c₂
  obtain ⟨t, -, ht⟩ := hc.elim_nhds_subcover
    (fun x => (fun y => y - x) ⁻¹' (box n c₂ : Set (n → k))) (by
      intro x _
      refine (ho.preimage (continuous_id.sub continuous_const)).mem_nhds ?_
      simp)
  refine (t.finite_toSet.image (fun x => (Submodule.Quotient.mk x : (n → k) ⧸ box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hx, hxy⟩ := this
  exact ⟨x, hx, ((Submodule.Quotient.eq _).2 hxy).symm⟩

end GlobalTheory.BoxCosets
