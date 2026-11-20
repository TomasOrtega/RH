import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem small_tendsto {x : ℕ → ℂ} (h : Small (1 / 2) x) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨C, N, h⟩ := h
  refine squeeze_zero_norm h ?_
  have h1 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one N (r := (1 / 2 : ℝ)) (by norm_num [abs_of_pos])).comp
    (tendsto_add_atTop_nat 1)
  have h2 := h1.const_mul (C * 2)
  rw [mul_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [add_comm (k : ℝ) 1]
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sat_card {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {D : CD E n} {w : Pl E} {B : Multiset ℂˣ}
    (h : D.Sat w B) : B.card = n := by
  obtain ⟨b, hb, rfl⟩ := h
  refine Eq.trans ?_ D.sum
  rw [Multiset.card_sum]
  exact Finset.sum_congr rfl fun i _ => (hb i).card

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem off_cofinite {E : Type} [Field E] [NumberField E] [IsCMField E] (hP : Places) (Z : Finset (Pl E)) :
    ∀ᶠ w : Pl E in cofinite, Off Z w := by
  have h1 : ∀ᶠ w : Pl E in cofinite, w ∉ Z := Z.eventually_cofinite_notMem
  have h2 : ∀ᶠ w : Pl E in cofinite, w ∉ Z.image cPl := (Z.image cPl).eventually_cofinite_notMem
  filter_upwards [h1, h2] with w a b
  exact ⟨a, fun h => b (Finset.mem_image.2 ⟨_, h, ((hP E).2.1 w).1⟩)⟩

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
