import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOffZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOnZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalLimitGlue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

/- English proof (translation)
Unfold `varInt`. Use `split_ifs with h`. Establish `h0 : chartDens W h.choose f φ = fun _ => 0`. Use function extensionality and compare the values at `y`. Unfold `chartDens sheetSum`.

Use `finsum_eq_zero_of_forall_eq_zero fun x => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_dif]`. Distinguish the cases in `hx : x ∈ fibre W h.choose y`. Rewrite using `[dif_pos hx] split_ifs`. Use `show f x * _ = 0`.

Rewrite using `[hf x hx.1, zero_mul]`. Both sides reduce to the same expression. Rewrite using `[dif_neg hx]`. Simplify using `[chartInt, h0]`. Both sides reduce to the same expression.
-/
theorem varInt_eq_zero_of_vanish {n k : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) (hf : ∀ x ∈ zeroSet W, f x = 0) :
    varInt W k f φ = 0 := by
  classical
  unfold varInt
  split_ifs with h
  · have h0 : chartDens W h.choose f φ = fun _ => 0 := by
      funext y
      unfold chartDens sheetSum
      refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
      rw [finsum_eq_dif]
      by_cases hx : x ∈ fibre W h.choose y
      · rw [dif_pos hx]
        split_ifs
        · show f x * _ = 0
          rw [hf x hx.1, zero_mul]
        · rfl
      · rw [dif_neg hx]
    simp [chartInt, h0]
  · rfl

/- English proof (translation)
Introduce `n d J u f φ hJ hdim hu hf hfc hφ`. Use `set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS`. Establish `hW : ∀ W ∈ S, W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0`. Introduce `W hWm`. Establish `hle : J ⊔ Ideal.span {linForm u} ≤ W` using `hWm.1.2`.

Use `⟨hWm.1.1, fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩` and prove the remaining obligations. Use `hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))` as an intermediate fact. Simplify `this` using `[linForm, linEval]`. Establish `hφW : ∀ W ∈ S, ∀ i, SmoothNear (zeroSet W) (φ i)` using `fun W hWm i => by`. Take `⟨U, hU, hSU, hC⟩` from `hφ i`.

Conclude with `⟨U, hU, (hW W hWm).2.1.trans hSU, hC⟩`. Establish `hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0})`. Use `IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)` and prove the remaining obligations. Establish `: zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0}`. Use extensionality with `x`.

Simplify using `[zeroSet]`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const`. Conclude with `continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)`. Use `tendsto_of_forall_local (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ)) (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S), (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) ?_ ?_ ?_ f hf hfc` and prove the remaining obligations.

Introduce `g₁ g₂ h1 h1c h2 h2c filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)`. Use `hAdd n (d + 1) J g₁ g₂ _ hJ h1.continuous h1c h2.continuous h2c fun i => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)`. Simplify using `using hφ j`.

Introduce `g₁ g₂ h1 h1c h2 h2c`. Rewrite using `[← finsum_mem_add_distrib (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]`. Use `finsum_mem_congr rfl fun W hWm => ?_` and prove the remaining obligations. Rewrite using `[hAdd n d W g₁ g₂ φ (hW W hWm).1 h1.continuous h1c h2.continuous h2c (hφW W hWm), mul_add]`. Introduce `p`.

Distinguish the cases in `hp : p ∈ zeroSet J ∩ {x | linEval u x = 0}`. Conclude with `hOn n d J u φ p hJ hdim hu hφ hp.1 hp.2`. Use `⟨_, hclosed.isOpen_compl.mem_nhds hp, fun g hg hgc hgN => ?_⟩` and prove the remaining obligations. Establish `h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S), (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) = 0`. Use `finsum_eq_zero_of_forall_eq_zero fun W => ?_` and prove the remaining obligations.

Rewrite using `[finsum_eq_dif]`. Distinguish the cases in `hWm : W ∈ S`. Rewrite using `[dif_pos hWm, varInt_eq_zero_of_vanish W g φ fun x hx => image_eq_zero_of_notMem_tsupport fun hxs => hgN hxs ⟨(hW W hWm).2.1 hx, (hW W hWm).2.2 x hx⟩, mul_zero]`. Rewrite using `[dif_neg hWm]`. Simplify using `only [h0]`.

Conclude with `hOff n d J u g φ hJ hdim hu hg hgc hφ (Set.disjoint_left.2 fun x hx hx' => hgN hx hx')`.
-/
theorem LelongLimit.proof (hOff : LelongLimitOffZero.Statement) (hOn : LelongLimitOnZero.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimit.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ
  set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS
  have hW : ∀ W ∈ S, W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by
    intro W hWm
    have hle : J ⊔ Ideal.span {linForm u} ≤ W := hWm.1.2
    refine ⟨hWm.1.1,
      fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩
    have := hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
    simpa [linForm, linEval] using this
  have hφW : ∀ W ∈ S, ∀ i, SmoothNear (zeroSet W) (φ i) := fun W hWm i => by
    obtain ⟨U, hU, hSU, hC⟩ := hφ i
    exact ⟨U, hU, (hW W hWm).2.1.trans hSU, hC⟩
  have hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0}) := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  refine tendsto_of_forall_local (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ))
    (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S),
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) ?_ ?_ ?_ f hf hfc
  · intro g₁ g₂ h1 h1c h2 h2c
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine hAdd n (d + 1) J g₁ g₂ _ hJ h1.continuous h1c h2.continuous h2c fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using hφ j
  · intro g₁ g₂ h1 h1c h2 h2c
    rw [← finsum_mem_add_distrib (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]
    refine finsum_mem_congr rfl fun W hWm => ?_
    rw [hAdd n d W g₁ g₂ φ (hW W hWm).1 h1.continuous h1c h2.continuous h2c (hφW W hWm), mul_add]
  · intro p
    by_cases hp : p ∈ zeroSet J ∩ {x | linEval u x = 0}
    · exact hOn n d J u φ p hJ hdim hu hφ hp.1 hp.2
    · refine ⟨_, hclosed.isOpen_compl.mem_nhds hp, fun g hg hgc hgN => ?_⟩
      have h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) = 0 := by
        refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
        rw [finsum_eq_dif]
        by_cases hWm : W ∈ S
        · rw [dif_pos hWm, varInt_eq_zero_of_vanish W g φ fun x hx =>
            image_eq_zero_of_notMem_tsupport fun hxs =>
              hgN hxs ⟨(hW W hWm).2.1 hx, (hW W hWm).2.2 x hx⟩, mul_zero]
        · rw [dif_neg hWm]
      simp only [h0]
      exact hOff n d J u g φ hJ hdim hu hg hgc hφ (Set.disjoint_left.2 fun x hx hx' => hgN hx hx')

end GroundTheory.Heights₂.Heights
