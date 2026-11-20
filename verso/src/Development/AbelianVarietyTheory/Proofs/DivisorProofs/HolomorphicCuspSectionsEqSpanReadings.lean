import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspFormsStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Onto

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D T κ h hκ hl hn i σ hσ`. Take `⟨τ⟩ : Nonempty D.what₂.Tau` from `Fintype.card_pos_iff.1 (by`. Rewrite using `[D.what₂.card_Tau]`. Unfold `Ranks.f Ranks.n`. Use the proof step `positivity)`.

Establish `hni : (κ i).n = D.R.nV` using `(hκ i τ).2.2`. Apply `le_antisymm` to reduce the goal to its premises. Use `(GlobalTheory.T.holomorphicCuspSections_le_span_algebraicCuspForms D T h _ (inR i) (κ i) (hl i) (hni ▸ hn) σ hσ).trans (Submodule.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `⟨⟨f, hf⟩, rfl⟩`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, rfl⟩`. Conclude with `Submodule.mem_inf.2 ⟨((Formalism.L2.Pj.mem_cusp _ _ _ _ _ _).1 f.2).2 σ hσ, Formalism.L2.Pj.rdU_mem_offZero _ _⟩`.
-/
theorem holSub0_eq_span_readings : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) σ).X (laU (T.U ((i : ℕ) + 1) σ) (wtA (κ i)) (κ i).n) = Submodule.span ℂ (Set.range fun f : Cu T κ i => rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) := by
  intro D T κ h hκ hl hn i σ hσ
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  have hni : (κ i).n = D.R.nV := (hκ i τ).2.2
  apply le_antisymm
  · refine (GlobalTheory.T.holomorphicCuspSections_le_span_algebraicCuspForms D T h _ (inR i) (κ i) (hl i) (hni ▸ hn) σ hσ).trans (Submodule.span_mono ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    exact Submodule.mem_inf.2 ⟨((Formalism.L2.Pj.mem_cusp _ _ _ _ _ _).1 f.2).2 σ hσ, Formalism.L2.Pj.rdU_mem_offZero _ _⟩

end GlobalTheory.Onto
