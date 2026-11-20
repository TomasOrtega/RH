import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModCore

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI ModW ModW.MG

open Classical in

def modFun {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (hG : IsMatGroup G)
    (g : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  if h : g ∈ G then (Measure.modularCharacterFun (mk hG g h) : ℝ) else 1

/- English proof (translation)
Introduce `m G hG`. Use `⟨modFun G hG, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Simplify using `only [modFun, dif_pos hg]`. Conclude with `Measure.modularCharacterFun_pos (mk hG g hg)` after adjusting the coercions.

Introduce `a ha b hb`. Establish `hab : a * b ∈ G` using `hG.2.2.1 a ha b hb`. Simplify using `only [modFun, dif_pos ha, dif_pos hb, dif_pos hab]`. Establish `hmk : mk hG (a * b) hab = mk hG a ha * mk hG b hb` using `by ext1`. Simplify using `only [toM_mk, toM_mul]`.

Rewrite using `[hmk]`. Establish `h` using `(Measure.modularCharacter (G := MG G hG)).map_mul (mk hG a ha) (mk hG b hb)`. Conclude with `h` after adjusting the coercions. Introduce `c hc hcG g hg`. Establish `hcg : c * g * c⁻¹ ∈ G` using `(hcG g).2 hg`.

Simplify using `only [modFun, dif_pos hg, dif_pos hcg]`. Establish `hmk : mk hG (c * g * c⁻¹) hcg = conjE c hc hcG (mk hG g hg)` using `by ext1`. Both sides reduce to the same expression. Rewrite using `[hmk, modF_conj]`. Introduce `V hVG hV`.

Establish `hK : IsCompact ((fun y : MtM m => Matrix.of y) ⁻¹' V)` using `hV`. Establish `hW : IsCompact ((val : MG G hG → MtM m) ⁻¹' ((fun y : MtM m => Matrix.of y) ⁻¹' V))` using `isClosedEmbedding_val.isCompact_preimage hK`. Take `⟨M, hM⟩` from `modF_bdd _ hW`. Use `⟨M, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hvG : v ∈ G` using `hVG hv`.

Simplify using `only [modFun, dif_pos hvG]`. Apply `hM` to reduce the goal to its premises. Use `show Matrix.of (mk hG v hvG).1 ∈ V`. Conclude with `hv`. Introduce `h1 μ hμ`.

Use `rightInv_of (hG := hG) μ hμ (fun g => ?_)` and prove the remaining obligations. Establish `hg` using `h1 g.toM g.toM_mem`. Simplify using `only [modFun, dif_pos g.toM_mem, mk_toM] at hg`. Conclude with `hg` after adjusting the coercions.
-/
theorem exists_modular_function : ModExists := by
  intro m G hG
  refine ⟨modFun G hG, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro g hg
    simp only [modFun, dif_pos hg]
    exact_mod_cast Measure.modularCharacterFun_pos (mk hG g hg)
  ·
    intro a ha b hb
    have hab : a * b ∈ G := hG.2.2.1 a ha b hb
    simp only [modFun, dif_pos ha, dif_pos hb, dif_pos hab]
    have hmk : mk hG (a * b) hab = mk hG a ha * mk hG b hb := by
      ext1
      simp only [toM_mk, toM_mul]
    rw [hmk]
    have h := (Measure.modularCharacter (G := MG G hG)).map_mul (mk hG a ha) (mk hG b hb)
    exact_mod_cast h
  ·
    intro c hc hcG g hg
    have hcg : c * g * c⁻¹ ∈ G := (hcG g).2 hg
    simp only [modFun, dif_pos hg, dif_pos hcg]
    have hmk : mk hG (c * g * c⁻¹) hcg = conjE c hc hcG (mk hG g hg) := by
      ext1
      rfl
    rw [hmk, modF_conj]
  ·
    intro V hVG hV
    have hK : IsCompact ((fun y : MtM m => Matrix.of y) ⁻¹' V) := hV
    have hW : IsCompact ((val : MG G hG → MtM m) ⁻¹' ((fun y : MtM m => Matrix.of y) ⁻¹' V)) :=
      isClosedEmbedding_val.isCompact_preimage hK
    obtain ⟨M, hM⟩ := modF_bdd _ hW
    refine ⟨M, fun v hv => ?_⟩
    have hvG : v ∈ G := hVG hv
    simp only [modFun, dif_pos hvG]
    apply hM
    show Matrix.of (mk hG v hvG).1 ∈ V
    exact hv
  ·
    intro h1 μ hμ
    refine rightInv_of (hG := hG) μ hμ (fun g => ?_)
    have hg := h1 g.toM g.toM_mem
    simp only [modFun, dif_pos g.toM_mem, mk_toM] at hg
    exact_mod_cast hg

end PI.QuotSetU.UnitaryGroupMassFormula
