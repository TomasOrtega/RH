import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryGroupStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ParabolicUnipotentGL

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CWB

open PositivityTheory.CW

namespace WordFiltrationCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

abbrev wd (l : List (Fin n × Fin n)) : Module.End ℂ V := (l.map fun p => E p.1 p.2).prod

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans h, hx⟩`.
-/
theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k :=
  Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans h, hx⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨[], by simp, by simp⟩`.
-/
theorem one_mem : (1 : Module.End ℂ V) ∈ U E 0 :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩`.
-/
theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main <;> assumption`.
-/
theorem mul_mem {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) :=
  by apply _root_.UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main <;> assumption

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.ParabolicUnipotentGL.main <;> assumption`.
-/
theorem bracket_mem (hE : IsGlRep E) {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y - y * x ∈ U E (j + k - 1) :=
  by apply _root_.UpperTheory.Reformulated.B.ParabolicUnipotentGL.main <;> assumption

end WordFiltrationCommute

/- English proof (translation)
Introduce `n ε V _ _ E hM`. Establish `hE : IsGlRep E` using `hM.gl`. Establish `hC : casimirK ε E ∈ U E 2`. Unfold `casimirK`. Use `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations.

Conclude with `WordFiltrationCommute.U_mono E (by norm_num : 1 + 1 ≤ 2) (WordFiltrationCommute.mul_mem E (WordFiltrationCommute.gen_mem E a b) (WordFiltrationCommute.gen_mem E b a))`. Use `⟨fun j k h => WordFiltrationCommute.U_mono E h, WordFiltrationCommute.one_mem E, WordFiltrationCommute.gen_mem E, fun j k x hx y hy => WordFiltrationCommute.mul_mem E hx hy, fun j k x hx y hy => WordFiltrationCommute.bracket_mem E hE hx hy, hC, fun a b => ?_⟩` and prove the remaining obligations. Establish `hZ` using `WordFiltrationCommute.bracket_mem E hE hC (WordFiltrationCommute.gen_mem E a b)`. Unfold `Z`. Conclude with `WordFiltrationCommute.U_mono E (by norm_num : 2 + 1 - 1 ≤ 2) hZ`.
-/
theorem word_filtration_of_length : A1 := by
  intro n ε V _ _ E hM
  have hE : IsGlRep E := hM.gl
  have hC : casimirK ε E ∈ U E 2 := by
    unfold casimirK
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    exact WordFiltrationCommute.U_mono E (by norm_num : 1 + 1 ≤ 2) (WordFiltrationCommute.mul_mem E (WordFiltrationCommute.gen_mem E a b) (WordFiltrationCommute.gen_mem E b a))
  refine ⟨fun j k h => WordFiltrationCommute.U_mono E h, WordFiltrationCommute.one_mem E, WordFiltrationCommute.gen_mem E,
    fun j k x hx y hy => WordFiltrationCommute.mul_mem E hx hy, fun j k x hx y hy => WordFiltrationCommute.bracket_mem E hE hx hy, hC,
    fun a b => ?_⟩
  have hZ := WordFiltrationCommute.bracket_mem E hE hC (WordFiltrationCommute.gen_mem E a b)
  unfold Z
  exact WordFiltrationCommute.U_mono E (by norm_num : 2 + 1 - 1 ≤ 2) hZ

end PositivityTheory.CWB

end
