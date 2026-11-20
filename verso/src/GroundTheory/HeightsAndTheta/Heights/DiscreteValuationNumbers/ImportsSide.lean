import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `f hf b`. Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.mp hf`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hI x hx b) (hJ y hy b)`.
-/
theorem IsMultiHomogIdeal.sup {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
    {I J : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) (hJ : IsMultiHomogIdeal J) :
    IsMultiHomogIdeal (I ⊔ J) := by
  intro f hf b
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.add_mem_sup (hI x hx b) (hJ y hy b)

/- English proof (translation)
Introduce `O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs hH W U hU`. Assume the negation of the conclusion as `hne`. Establish `hW : divCycle P s W ≠ 0` using `left_ne_zero_of_mul hne`. Establish `hWU : idealCycle (W ⊔ divisorIdeal P f g) U ≠ 0` using `right_ne_zero_of_mul hne`. Establish `hWm : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W`.

Unfold `divCycle at hW`. Use `split_ifs at hW with h`. Conclude with `h`. Conclude with `absurd rfl hW`. Establish `hUm : U ∈ (W ⊔ divisorIdeal P f g).minimalPrimes ∧ IsRelevant U`.

Unfold `idealCycle at hWU`. Use `split_ifs at hWU with h`. Conclude with `h`. Conclude with `absurd rfl hWU`. Establish `hWp : W.IsPrime` using `hWm.1.1.1`.

Establish `hUp : U.IsPrime` using `hUm.1.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hWm.1.1.2`. Establish `hWU' : W ≤ U` using `le_sup_left.trans hUm.1.1.2`. Establish `hDU : divisorIdeal P f g ≤ U` using `le_sup_right.trans hUm.1.1.2`. Establish `hWmh : IsMultiHomogIdeal W` using `MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P s c hP hs) hWm.1`.

Take `⟨bf, bg, hbf, hbg, -⟩` from `hD.1.degrees`. Establish `hDm : IsMultiHomogIdeal (divisorIdeal P f g)` using `ColonMultiHomog.proof O K ι _ g bg (SupSpanMultiHomog.proof O K ι P f bf hP hbf) hbg`. Establish `hUmh : IsMultiHomogIdeal U` using `MinimalPrimeMultiHomog.proof O K ι _ U (hWmh.sup hDm) hUm.1`. Apply `hU` to reduce the goal to its premises. Use `⟨hUp, hUmh, hUm.2, ?_, hPW.trans hWU'⟩` and prove the remaining obligations.

Distinguish the cases in `hϖW : (C ϖ : MRing ι O) ∈ W`. Conclude with `hWU' hϖW`. Assume the negation of the conclusion as `hϖU`. Establish `hV` using `hH W hW hϖW`. Take `⟨u, v, hu, hv, huv⟩` from `hV.unit_off_special U hUp hWU' hUm.2 hϖU`.

Take `⟨u', v', hu', huv'⟩` from `hD.2 U hUp (hPW.trans hWU') hUm.2`. Establish `hv'D : v' ∈ divisorIdeal P f g`. Unfold `divisorIdeal`. Rewrite using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Establish `e : v' * g = u' * f - (u' * f - v' * g)` using `by ring`.

Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))) (Ideal.mem_sup_left huv')`. Establish `hmem : g * (u * v' - u' * v) ∈ W`. Establish `e : g * (u * v' - u' * v) = u' * (u * f - v * g) - u * (u' * f - v' * g)` using `by ring`. Rewrite using `[e]`.

Conclude with `W.sub_mem (W.mul_mem_left _ huv) (W.mul_mem_left _ (hPW huv'))`. Establish `hdiff : u * v' - u' * v ∈ U` using `hWU' ((hWp.mem_or_mem hmem).resolve_left hV.den_not_mem)`. Establish `hv'U : v' ∈ U` using `hDU hv'D`. Establish `hu'v : u' * v ∈ U`. Establish `e : u' * v = u * v' - (u * v' - u' * v)` using `by ring`.

Rewrite using `[e]`. Conclude with `U.sub_mem (U.mul_mem_left _ hv'U) hdiff`. Conclude with `(hUp.mem_or_mem hu'v).elim hu' hv`.
-/
theorem RightTermSupport.proof : RightTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs hH W U hU
  by_contra hne
  have hW : divCycle P s W ≠ 0 := left_ne_zero_of_mul hne
  have hWU : idealCycle (W ⊔ divisorIdeal P f g) U ≠ 0 := right_ne_zero_of_mul hne
  have hWm : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  have hUm : U ∈ (W ⊔ divisorIdeal P f g).minimalPrimes ∧ IsRelevant U := by
    unfold idealCycle at hWU
    split_ifs at hWU with h
    · exact h
    · exact absurd rfl hWU
  have hWp : W.IsPrime := hWm.1.1.1
  have hUp : U.IsPrime := hUm.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hWm.1.1.2
  have hWU' : W ≤ U := le_sup_left.trans hUm.1.1.2
  have hDU : divisorIdeal P f g ≤ U := le_sup_right.trans hUm.1.1.2
  have hWmh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P s c hP hs) hWm.1
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.1.degrees
  have hDm : IsMultiHomogIdeal (divisorIdeal P f g) :=
    ColonMultiHomog.proof O K ι _ g bg (SupSpanMultiHomog.proof O K ι P f bf hP hbf) hbg
  have hUmh : IsMultiHomogIdeal U :=
    MinimalPrimeMultiHomog.proof O K ι _ U (hWmh.sup hDm) hUm.1
  apply hU
  refine ⟨hUp, hUmh, hUm.2, ?_, hPW.trans hWU'⟩
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · exact hWU' hϖW
  by_contra hϖU
  have hV := hH W hW hϖW
  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_special U hUp hWU' hUm.2 hϖU
  obtain ⟨u', v', hu', huv'⟩ := hD.2 U hUp (hPW.trans hWU') hUm.2
  have hv'D : v' ∈ divisorIdeal P f g := by
    unfold divisorIdeal
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have e : v' * g = u' * f - (u' * f - v' * g) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      (Ideal.mem_sup_left huv')
  have hmem : g * (u * v' - u' * v) ∈ W := by
    have e : g * (u * v' - u' * v) = u' * (u * f - v * g) - u * (u' * f - v' * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left _ huv) (W.mul_mem_left _ (hPW huv'))
  have hdiff : u * v' - u' * v ∈ U :=
    hWU' ((hWp.mem_or_mem hmem).resolve_left hV.den_not_mem)
  have hv'U : v' ∈ U := hDU hv'D
  have hu'v : u' * v ∈ U := by
    have e : u' * v = u * v' - (u * v' - u' * v) := by ring
    rw [e]
    exact U.sub_mem (U.mul_mem_left _ hv'U) hdiff
  exact (hUp.mem_or_mem hu'v).elim hu' hv

end GroundTheory.Heights₂.Heights.NumbersDVR
