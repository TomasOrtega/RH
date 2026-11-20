import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiBiUnion

noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨hlc, hcs⟩` from `hF`. Establish `hK : IsCompact (tsupport F)` using `hcs`. Establish `hc1 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 + z.1, z.2.2) : Sp k n)` using `by fun_prop`. Establish `hc2 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 - z.1, z.2.2) : Sp k n)` using `by fun_prop`. Establish `hev : ∀ᶠ w in nhds (0 : Matrix (Fin n) (Fin n) k), ∀ q ∈ tsupport F, F (q.1 + w, q.2) = F q ∧ F (q.1 - w, q.2) = F q`.

Use `hK.eventually_forall_of_forall_eventually ?_` and prove the remaining obligations. Introduce `q _`. Establish `e1` using `(hlc.comp_continuous hc1).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)`. Establish `e2` using `(hlc.comp_continuous hc2).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)`. Establish `e3` using `(hlc.comp_continuous continuous_snd).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)`.

Use `filter_upwards [e1, e2, e3] with z h1 h2 h3`. Simplify using `only [Function.comp_apply, add_zero, sub_zero] at h1 h2 h3`. Conclude with `⟨by rw [h1, h3], by rw [h2, h3]⟩`. Use `⟨_, hev, ?_⟩` and prove the remaining obligations. Introduce `w hw p`.

Distinguish the cases in `hp : p ∈ tsupport F`. Conclude with `(hw p hp).1`. Establish `h0 : F p = 0` using `image_eq_zero_of_notMem_tsupport hp`. Distinguish the cases in `hp' : ((p.1 + w, p.2) : Sp k n) ∈ tsupport F`. Use `(hw _ hp').2` as an intermediate fact.

Simplify using `only [add_sub_cancel_right] at this`. Rewrite `this`, the goal using `[h0]`. Conclude with `this.symm`. Rewrite using `[h0]`. Conclude with `image_eq_zero_of_notMem_tsupport hp'`.
-/
theorem unifLC {F : Sp k n → ℂ} (hF : F ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ) :
    ∃ W ∈ nhds (0 : Matrix (Fin n) (Fin n) k), ∀ w ∈ W, ∀ p : Sp k n, F (p.1 + w, p.2) = F p := by
  obtain ⟨hlc, hcs⟩ := hF
  have hK : IsCompact (tsupport F) := hcs
  have hc1 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 + z.1, z.2.2) : Sp k n) := by
    fun_prop
  have hc2 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 - z.1, z.2.2) : Sp k n) := by
    fun_prop
  have hev : ∀ᶠ w in nhds (0 : Matrix (Fin n) (Fin n) k), ∀ q ∈ tsupport F,
      F (q.1 + w, q.2) = F q ∧ F (q.1 - w, q.2) = F q := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro q _
    have e1 := (hlc.comp_continuous hc1).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    have e2 := (hlc.comp_continuous hc2).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    have e3 := (hlc.comp_continuous continuous_snd).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    filter_upwards [e1, e2, e3] with z h1 h2 h3
    simp only [Function.comp_apply, add_zero, sub_zero] at h1 h2 h3
    exact ⟨by rw [h1, h3], by rw [h2, h3]⟩
  refine ⟨_, hev, ?_⟩
  intro w hw p
  by_cases hp : p ∈ tsupport F
  · exact (hw p hp).1
  · have h0 : F p = 0 := image_eq_zero_of_notMem_tsupport hp
    by_cases hp' : ((p.1 + w, p.2) : Sp k n) ∈ tsupport F
    · have := (hw _ hp').2
      simp only [add_sub_cancel_right] at this
      rw [h0] at this ⊢
      exact this.symm
    · rw [h0]
      exact image_eq_zero_of_notMem_tsupport hp'

end PositivityTheory.RgUd.TP.Nil.Fib2

end
