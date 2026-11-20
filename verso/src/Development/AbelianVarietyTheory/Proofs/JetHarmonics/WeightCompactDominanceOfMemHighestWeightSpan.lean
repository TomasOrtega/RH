import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact ⟨fun _ _ => 0, by simp, by simp [Formalism.REAL.wordWeightShift]⟩`. Consider the case `cons p w ih`. Take `⟨c, hc, he⟩` from `ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))`. Establish `hp` using `hw p List.mem_cons_self`.

Use `⟨fun a b => c a b + (if a = p.2 then if b = p.1 then 1 else 0 else 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Distinguish the cases in `h0 : c a b = 0`. Distinguish the cases in `h1 : a = p.2`. Distinguish the cases in `h2 : b = p.1`.

Substitute `h1` using the available equality. Substitute `h2` using the available equality. Conclude with `⟨hp.2, hp.1.symm⟩`. Simplify using `[h0, h2] at hab`. Simplify using `[h0, h1] at hab`.

Conclude with `hc a b h0`. Establish `h1 : ∑ a, ∑ b, (((if a = p.2 then if b = p.1 then 1 else 0 else 0 : ℕ) : ℝ)) • PI.UpqRep.root a b = PI.UpqRep.root p.2 p.1`. Rewrite using `[Finset.sum_eq_single p.2]`. Rewrite using `[Finset.sum_eq_single p.1]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Introduce `a _ ha`. Simplify using `[ha]`.

Simplify using the standard rewrite rules. Simplify using `only [Nat.cast_add, add_smul, Finset.sum_add_distrib]`. Rewrite using `[h1, ← he]`. Simplify using `only [Formalism.REAL.wordWeightShift, PI.UpqRep.root]`. Normalize the expressions using the abelian group laws.
-/
theorem cdom_add_lowering_word {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ)
    (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    PI.UpqRep.CDom ε (Λ + Formalism.REAL.wordWeightShift w) Λ := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, by simp, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, he⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have hp := hw p List.mem_cons_self
    refine ⟨fun a b => c a b + (if a = p.2 then if b = p.1 then 1 else 0 else 0), ?_, ?_⟩
    · intro a b hab
      by_cases h0 : c a b = 0
      · by_cases h1 : a = p.2
        · by_cases h2 : b = p.1
          · subst h1; subst h2; exact ⟨hp.2, hp.1.symm⟩
          · simp [h0, h2] at hab
        · simp [h0, h1] at hab
      · exact hc a b h0
    · have h1 : ∑ a, ∑ b, (((if a = p.2 then if b = p.1 then 1 else 0 else 0 : ℕ) : ℝ)) •
          PI.UpqRep.root a b = PI.UpqRep.root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2]
        · rw [Finset.sum_eq_single p.1]
          · simp
          · intro b _ hb; simp [hb]
          · simp
        · intro a _ ha; simp [ha]
        · simp
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib]
      rw [h1, ← he]
      simp only [Formalism.REAL.wordWeightShift, PI.UpqRep.root]
      abel

/- English proof (translation)
Introduce `k W _ _ E Λ μ x v hg hu hΛ hv hv0 hμ`. Assume the negation of the conclusion as `hne`. Establish `hk` using `Formalism.REAL.isUnitary_kUnit _ E hu`. Establish `hr` using `Formalism.REAL.glRel_kRel (PI.UpqRep.allPos k) E hg`. Rewrite `hv` using `[Formalism.REAL.compact_span_eq_lowering hr hΛ]`.

Establish `key : ∀ z ∈ Formalism.REAL.lowSpan (PI.UpqRep.allPos k) E x, ⟪z, v⟫_ℂ = 0`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨w, hw, rfl⟩` from `hy`.

Use `Formalism.REAL.compact_weight_orthogonal W k _ E _ μ _ v hk (Formalism.REAL.word_action_weight hr hΛ.1 w (fun q hq => (hw q hq).1)) hμ ?_` and prove the remaining obligations. Introduce `heq`. Conclude with `hne (heq ▸ cdom_add_lowering_word _ Λ w hw)`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]`.

Consider the case `smul c y _ hy => rw [inner_smul_left, hy, mul_zero]`. Conclude with `hv0 (inner_self_eq_zero.mp (key v hv))`.
-/
theorem weight_cdom_of_mem_kSpan :
    ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (Λ μ : Fin k → ℝ) (x v : W), Formalism.REAL.GlRel E → Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E → Formalism.REAL.KHighest (PI.UpqRep.allPos k) E Λ x → v ∈ Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x → v ≠ 0 → Formalism.REAL.IsWeight E μ v → PI.UpqRep.CDom (PI.UpqRep.allPos k) μ Λ := by
  intro k W _ _ E Λ μ x v hg hu hΛ hv hv0 hμ
  by_contra hne
  have hk := Formalism.REAL.isUnitary_kUnit _ E hu
  have hr := Formalism.REAL.glRel_kRel (PI.UpqRep.allPos k) E hg
  rw [Formalism.REAL.compact_span_eq_lowering hr hΛ] at hv
  have key : ∀ z ∈ Formalism.REAL.lowSpan (PI.UpqRep.allPos k) E x, ⟪z, v⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      refine Formalism.REAL.compact_weight_orthogonal W k _ E _ μ _ v hk
        (Formalism.REAL.word_action_weight hr hΛ.1 w (fun q hq => (hw q hq).1)) hμ ?_
      intro heq
      exact hne (heq ▸ cdom_add_lowering_word _ Λ w hw)
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]
  exact hv0 (inner_self_eq_zero.mp (key v hv))

end GlobalTheory
