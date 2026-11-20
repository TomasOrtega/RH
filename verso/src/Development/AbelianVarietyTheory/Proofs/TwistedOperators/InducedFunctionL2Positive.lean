import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.RealInd

/- English proof (translation)
Introduce `n ε D f hf g hg`. Take `⟨k, hk, hp⟩` from `GlobalTheory.RealIwasawa.exists_stab_mul_compact D.flag g`. Take `⟨u, hu, m, hm, x, t, ht, hpe⟩` from `exists_langlands_decomp D.flag D.pos hp`. Establish `hkK : k ∈ KG ε`. Establish `: k ∈ (KG ε : Set (UJ ε))` using `(KG_eq ε).symm ▸ hk`.

Conclude with `this`. Establish `hfk : f k ≠ 0`. Introduce `h0`. Apply `hg` to reduce the goal to its premises. Establish `e` using `(mem_indFun_top.1 hf).2 u hu m hm x t ht k`.

Rewrite `e` using `[← hpe, inv_mul_cancel_right, h0, map_zero, smul_zero]`. Conclude with `e`. Establish `hcont : Continuous fun k : KG ε => ‖f k‖ ^ 2` using `((mem_indFun_top.1 hf).1.comp continuous_subtype_val).norm.pow 2`. Use `haveI : (muK ε).IsOpenPosMeasure := by unfold muK; infer_instance`. Conclude with `hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := ⟨k, hkK⟩) (HasCompactSupport.of_compactSpace _) (fun _ => by positivity) (by simpa using hfk)`.
-/
theorem integral_norm_sq_pos_of_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε) (f : UJ ε → D.V), f ∈ D.fns →
    ∀ g, f g ≠ 0 → 0 < ∫ k : KG ε, ‖f k‖ ^ 2 ∂muK ε := by
  intro n ε D f hf g hg
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact D.flag g
  obtain ⟨u, hu, m, hm, x, t, ht, hpe⟩ := exists_langlands_decomp D.flag D.pos hp
  have hkK : k ∈ KG ε := by
    have : k ∈ (KG ε : Set (UJ ε)) := (KG_eq ε).symm ▸ hk
    exact this
  have hfk : f k ≠ 0 := by
    intro h0
    apply hg
    have e := (mem_indFun_top.1 hf).2 u hu m hm x t ht k
    rw [← hpe, inv_mul_cancel_right, h0, map_zero, smul_zero] at e
    exact e
  have hcont : Continuous fun k : KG ε => ‖f k‖ ^ 2 :=
    ((mem_indFun_top.1 hf).1.comp continuous_subtype_val).norm.pow 2
  haveI : (muK ε).IsOpenPosMeasure := by unfold muK; infer_instance
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := ⟨k, hkK⟩)
    (HasCompactSupport.of_compactSpace _) (fun _ => by positivity) (by simpa using hfk)

end GlobalTheory.RealInd
