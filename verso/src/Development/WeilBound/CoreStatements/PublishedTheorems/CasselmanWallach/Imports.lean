import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.PCDense
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped ComplexOrder

namespace PositivityTheory.CW

/- English proof (translation)
Introduce `n ε H _ _ _ σ hU hI`. Establish `hHC` using `CompanionTheory.D.gk.HC.print_harishChandraModules`. Use `⟨fun v hv => GlobalTheory.CWGeneral.sm_of_isKFin hHC hU hI hv, fun v hv X hX => GlobalTheory.CWGeneral.isKFin_dRep_of_irred hHC hU hI hv hX, fun w hw S hS δ hδ => ?_⟩` and prove the remaining obligations. Establish `hG : Formalism.IndefR.Tow.SobPf.IsGRep (Formalism.REAL.Jm ε) σ` using `⟨hU.1.1, hU.1.2, hU.2.1, hU.2.2⟩`. Establish `hC : Formalism.IndefR.Datum.IsCartanInv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε)`.

Establish `hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε`. Apply the tactic sequence `ext i j; simp only [Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all`. Use `⟨Formalism.REAL.Jm_mul_self ε, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hJ, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]`. Rewrite using `[Formalism.REAL.Jm_mul_self]`.

Conclude with `Matrix.PosDef.one`. Use `set δ' : ℝ := δ / (S.length + 1) with hδ'`. Establish `hδ'0 : 0 < δ'` using `div_pos hδ (by positivity)`. Take `⟨v, hvS, hvK, hvw⟩` from `CompanionTheory.D.gk.HC.sobApprox_holds (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ hC hG w hw S hS δ' hδ'0`. Use `⟨v, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨W, hW, hvW, hst⟩` from `hvK`. Use `⟨W, hW, hvW, fun g hg x hx => hst g ⟨?_, hg.2⟩ x hx⟩` and prove the remaining obligations. Use `show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hg.1, Matrix.one_mul]`. Establish `hv' : Sm ε σ v` using `hvS`.

Establish `key : ∀ l ∈ S, ‖Dw σ l (w - v)‖ ≤ δ'`. Introduce `l hl`. Establish `e : Dw σ l (w - v) = Dw σ l w - Dw σ l v`. Use `Dw_add hU (hS l hl) (sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hv'))) hv'` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`.

Rewrite using `[this, add_sub_cancel_right]`. Rewrite using `[e, norm_sub_rev]`. Conclude with `(hvw l hl).le`. Establish `hL : (S.length : ℝ) * δ' < δ`. Rewrite using `[hδ', mul_div_assoc', div_lt_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Unfold `sobNorm`. Combine the equalities or inequalities in the displayed calculation. Take `⟨l, hl, rfl⟩` from `List.mem_map.1 hx`. Conclude with `key l hl)`.

Use `_ = S.length * δ' := by simp`. Use `_ < δ := hL`.
-/
theorem c5 : C5 := by
  intro n ε H _ _ _ σ hU hI
  have hHC := CompanionTheory.D.gk.HC.print_harishChandraModules
  refine ⟨fun v hv => GlobalTheory.CWGeneral.sm_of_isKFin hHC hU hI hv,
    fun v hv X hX => GlobalTheory.CWGeneral.isKFin_dRep_of_irred hHC hU hI hv hX, fun w hw S hS δ hδ => ?_⟩
  have hG : Formalism.IndefR.Tow.SobPf.IsGRep (Formalism.REAL.Jm ε) σ := ⟨hU.1.1, hU.1.2, hU.2.1, hU.2.2⟩
  have hC : Formalism.IndefR.Datum.IsCartanInv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) := by
    have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
      ext i j; simp only [Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
    refine ⟨Formalism.REAL.Jm_mul_self ε, ?_, ?_⟩
    · rw [hJ, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    · rw [Formalism.REAL.Jm_mul_self]; exact Matrix.PosDef.one
  set δ' : ℝ := δ / (S.length + 1) with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by positivity)
  obtain ⟨v, hvS, hvK, hvw⟩ := CompanionTheory.D.gk.HC.sobApprox_holds (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ hC hG w
    hw S hS δ' hδ'0
  refine ⟨v, ?_, ?_⟩
  · obtain ⟨W, hW, hvW, hst⟩ := hvK
    refine ⟨W, hW, hvW, fun g hg x hx => hst g ⟨?_, hg.2⟩ x hx⟩
    show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').1 hg.1, Matrix.one_mul]
  · have hv' : Sm ε σ v := hvS
    have key : ∀ l ∈ S, ‖Dw σ l (w - v)‖ ≤ δ' := by
      intro l hl
      have e : Dw σ l (w - v) = Dw σ l w - Dw σ l v := by
        have := Dw_add hU (hS l hl) (sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hv'))) hv'
        rw [sub_add_cancel] at this
        rw [this, add_sub_cancel_right]
      rw [e, norm_sub_rev]
      exact (hvw l hl).le
    have hL : (S.length : ℝ) * δ' < δ := by
      rw [hδ', mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    unfold sobNorm
    calc (S.map fun l => ‖l.foldr (dRep σ) (w - v)‖).sum
        ≤ (S.map fun l => ‖l.foldr (dRep σ) (w - v)‖).length • δ' :=
          List.sum_le_card_nsmul _ _ (fun x hx => by
            obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
            exact key l hl)
      _ = S.length * δ' := by simp
      _ < δ := hL

end PositivityTheory.CW
