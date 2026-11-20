import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitV

namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

noncomputable section

/- English proof (translation)
Simplify using `[IR]`.
-/
theorem thickSplit_realSpan_bot {E : Type} [Field E] [NumberField E] [IsCMField E]
    {dim : (E →+* ℂ) → ℕ} : IR (⊥ : Submodule ℤ (Vsp dim)) = ⊥ := by simp [IR]

/- English proof (translation)
Introduce `E _ _ _ X DF P h`. Establish `h' : ¬ X.la1 < th (E` using `E) P.q P.R0 := h`. Establish `hph : P.ph = 0` using `by rw [Par.ph, PT.ph, if_neg h']`. Establish `hG` using `Good.bot X 0`. Establish `hfr0 : Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))) = 0`.

Rewrite using `[thickSplit_realSpan_bot]`. Conclude with `finrank_bot ℝ _`. Use `⟨bot_le, ?_, hG.stable, hG.iso, ?_, ⟨0, Nat.zero_le _, by rw [hfr0]; ring⟩, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x _ k hk hkx`. Rewrite `hkx`, the goal using `[Submodule.mem_bot]`.

Establish `: (k : ℝ) • x = 0` using `by rw [Int.cast_smul_eq_zsmul]; exact hkx`. Conclude with `(smul_eq_zero.1 this).resolve_left (by exact_mod_cast hk)`. Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_bot]`. Substitute `hx` using the available equality.

Conclude with `X.eps_iso 0 (Submodule.zero_mem _) (fun α => by rw [act_eq_actE, actE_zero_right]; exact Hf_im_zero_left _)`. Simplify using `only [ne_eq, not_true_eq_false, false_iff]`. Conclude with `h`. Introduce `x hx _ hxI`. Rewrite using `[thickSplit_realSpan_bot, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]`.

Rewrite `hxI` using `[Submodule.mem_bot]`. Conclude with `(le_of_not_gt h).trans (sq_le_Qy_of_le_firstMinimum X hx hxI)`. Introduce `x _ u hu hne`. It suffices to derive a contradiction. Use `hu.1` as an intermediate fact.

Rewrite `this` using `[thickSplit_realSpan_bot, Submodule.mem_bot]`. Conclude with `hne this`. Use `haveI : IsEmpty (Fin (Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))))) := by`. Rewrite using `[hfr0]`. Use `infer_instance`.

Conclude with `⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type, fun j => isEmptyElim j⟩`. Introduce `k x u _ _`. Rewrite using `[hph]`. Conclude with `Finset.sum_nonneg (fun j _ => by positivity)`.
-/
theorem thickSplit_bot :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF),
      ¬ X.la1 < P.th → IsSplit P ⊥ := by
  intro E _ _ _ X DF P h
  have h' : ¬ X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 0 := by rw [Par.ph, PT.ph, if_neg h']
  have hG := Good.bot X 0
  have hfr0 : Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))) = 0 := by
    rw [thickSplit_realSpan_bot]; exact finrank_bot ℝ _
  refine ⟨bot_le, ?_, hG.stable, hG.iso, ?_, ⟨0, Nat.zero_le _, by rw [hfr0]; ring⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x _ k hk hkx
    rw [Submodule.mem_bot] at hkx ⊢
    have : (k : ℝ) • x = 0 := by rw [Int.cast_smul_eq_zsmul]; exact hkx
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hk)
  · intro x hx
    rw [Submodule.mem_bot] at hx
    subst hx
    exact X.eps_iso 0 (Submodule.zero_mem _)
      (fun α => by rw [act_eq_actE, actE_zero_right]; exact Hf_im_zero_left _)
  · simp only [ne_eq, not_true_eq_false, false_iff]
    exact h
  · intro x hx _ hxI
    rw [thickSplit_realSpan_bot, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]
    rw [Submodule.mem_bot] at hxI
    exact (le_of_not_gt h).trans (sq_le_Qy_of_le_firstMinimum X hx hxI)
  · intro x _ u hu hne
    exfalso
    have := hu.1
    rw [thickSplit_realSpan_bot, Submodule.mem_bot] at this
    exact hne this
  · haveI : IsEmpty (Fin (Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))))) := by
      rw [hfr0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  · intro k x u _ _
    rw [hph]
    exact Finset.sum_nonneg (fun j _ => by positivity)

end

end GlobalTheory
