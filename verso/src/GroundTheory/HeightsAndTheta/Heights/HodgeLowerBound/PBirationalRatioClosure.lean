import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBirationalRatioClosure
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace BirationalRatioClosure

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm ↦ ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Use `congr 1`. Establish `h1 : (∏ p, y p ^ m p) = ∏ p : Σ k, ι k, (y ⟨p.1, c p.1⟩ ^ m p * (y p / y ⟨p.1, c p.1⟩) ^ m p)`.

Use `Finset.prod_congr rfl fun p _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, mul_div_cancel₀ _ (hc p.1)]`. Rewrite using `[h1, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Use `show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = y ⟨k, c k⟩ ^ d k`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hg m hm k]`.
-/
theorem aeval_eq_prod_mul (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g = (∏ k, y ⟨k, c k⟩ ^ d k) * aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [mul_left_comm]
  congr 1
  have h1 : (∏ p, y p ^ m p) =
      ∏ p : Σ k, ι k, (y ⟨p.1, c p.1⟩ ^ m p * (y p / y ⟨p.1, c p.1⟩) ^ m p) := by
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [← mul_pow, mul_div_cancel₀ _ (hc p.1)]
  rw [h1, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = y ⟨k, c k⟩ ^ d k
  rw [Finset.prod_pow_eq_pow_sum, hg m hm k]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, algebraMap_int_eq, eq_intCast]`. Conclude with `intCast_mem _ a`. Consider the case `add p q hp hq`.

Rewrite using `[map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, aeval_X]`. Conclude with `mul_mem hp (Subfield.subset_closure ⟨i, rfl⟩)`.
-/
theorem aeval_mem_closure (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (g : MRing ι) :
    aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g ∈ Subfield.closure (coneRatios y c) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ a
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    exact mul_mem hp (Subfield.subset_closure ⟨i, rfl⟩)

/- English proof (translation)
Introduce `K _ ι _ Ω _ y c hy hc`. Use `eq_top_iff.2 fun s _ ↦ ?_` and prove the remaining obligations. Take `⟨d, g, h, hg, hh, hh0, hgs⟩` from `hy s`. Establish `hP : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (hc k)`. Rewrite `hgs` using `[aeval_eq_prod_mul y c hc hg, aeval_eq_prod_mul y c hc hh]`.

Rewrite `hh0` using `[aeval_eq_prod_mul y c hc hh]`. Establish `hr` using `right_ne_zero_of_mul hh0`. Establish `hs : s = aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g / aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) h`. Rewrite using `[eq_div_iff hr]`. Conclude with `(mul_left_cancel₀ hP (hgs.trans (mul_left_comm _ _ _))).symm`.

Rewrite using `[hs]`. Conclude with `div_mem (aeval_mem_closure y c g) (aeval_mem_closure y c h)`.
-/
theorem full : BirationalRatioClosure.Statement := by
  intro K _ ι _ Ω _ y c hy hc
  refine eq_top_iff.2 fun s _ ↦ ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hy s
  have hP : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (hc k)
  rw [aeval_eq_prod_mul y c hc hg, aeval_eq_prod_mul y c hc hh] at hgs
  rw [aeval_eq_prod_mul y c hc hh] at hh0
  have hr := right_ne_zero_of_mul hh0
  have hs : s = aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g / aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) h := by
    rw [eq_div_iff hr]
    exact (mul_left_cancel₀ hP (hgs.trans (mul_left_comm _ _ _))).symm
  rw [hs]
  exact div_mem (aeval_mem_closure y c g) (aeval_mem_closure y c h)

end BirationalRatioClosure

end GroundTheory.Heights₂.Heights.LowerBoundFree
