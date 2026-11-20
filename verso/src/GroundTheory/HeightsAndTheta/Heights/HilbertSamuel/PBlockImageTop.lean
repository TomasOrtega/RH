import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockImageTop

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

/- English proof (translation)
Introduce `m hm k`. Take `⟨t, -, ht⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)`. Rewrite `ht` using `[C_mul_X_eq_monomial]`. Establish `hmt` using `Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)`. Substitute `hmt` using the available equality.

Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Simplify using `[blockDeg, Finsupp.single_apply]`. Simplify using `[blockDeg, hk, Sigma.ext_iff]`.
-/
theorem isMultiHomog_blockForms (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

/- English proof (translation)
Establish `hf : ∀ j, mConeMap y (blockForms k₀ M j) = MvPolynomial.C (x j) * MvPolynomial.X k₀`. Introduce `j`. Rewrite using `[h.1 j, map_sum, Finset.sum_mul]`. Simplify using `[blockForms, mConeMap, map_sum, mul_assoc]`. Establish `hX : mConeMap y (X ⟨k₀, i⟩) = MvPolynomial.C (y ⟨k₀, i⟩) * MvPolynomial.X k₀`.

Simplify using `[mConeMap]`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, map_sub, map_sum]`. Simplify using `only [map_mul, hf]`. Rewrite using `[hX, h.2 i, map_sum, Finset.sum_mul, sub_eq_zero]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `[mConeMap, mul_assoc]`.
-/
theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (i : ι k₀) :
    X ⟨k₀, i⟩ - ∑ j, C (N i j) * blockForms k₀ M j ∈ mCoordIdeal y := by
  have hf : ∀ j, mConeMap y (blockForms k₀ M j) = MvPolynomial.C (x j) * MvPolynomial.X k₀ := by
    intro j
    rw [h.1 j, map_sum, Finset.sum_mul]
    simp [blockForms, mConeMap, map_sum, mul_assoc]
  have hX : mConeMap y (X ⟨k₀, i⟩) = MvPolynomial.C (y ⟨k₀, i⟩) * MvPolynomial.X k₀ := by
    simp [mConeMap]
  rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_sum]
  simp only [map_mul, hf]
  rw [hX, h.2 i, map_sum, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mConeMap, mul_assoc]

/- English proof (translation)
Introduce `k₂ i`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k₀)]`. Use `Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Establish `hspan : ∑ j, C (N (i k₀) j) * blockForms k₀ M j ∈ Ideal.span (Set.range fun j : GlobalTheory κ k₂ => blockForms k₀ M ⟨k₂, j⟩)`.

Use `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j.2, ?_⟩)` and prove the remaining obligations. Consider the cases of `k₂`. Both sides reduce to the same expression. Use `Ideal.add_mem _ (Ideal.mem_sup_left (sub_mem_mCoordIdeal h (i k₀))) (Ideal.mem_sup_right hspan)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem isBasePtFree_blockForms {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) :
    IsBasePtFree (mCoordIdeal y) (blockForms k₀ M) := by
  intro k₂ i
  refine ⟨1, ?_⟩
  rw [pow_one, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k₀)]
  refine Ideal.mul_mem_right _ _ ?_
  have hspan : ∑ j, C (N (i k₀) j) * blockForms k₀ M j ∈
      Ideal.span (Set.range fun j : GlobalTheory κ k₂ => blockForms k₀ M ⟨k₂, j⟩) := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j.2, ?_⟩)
    cases k₂
    rfl
  have := Ideal.add_mem _ (Ideal.mem_sup_left (sub_mem_mCoordIdeal h (i k₀))) (Ideal.mem_sup_right hspan)
  rwa [sub_add_cancel] at this

/- English proof (translation)
Use `hm.mono fun z hz => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz ()`. Conclude with `fun h0 => hi (congrFun h0 _)`.
-/
theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `[formApply, blockForms, blockMapC]`.
-/
theorem formApply_blockForms (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) :
    formApply (blockForms k₀ M) z = blockMapC k₀ M z := by
  funext q
  simp [formApply, blockForms, blockMapC]

end BlockImageTop

open BlockImageTop in

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ κ _ I y k₀ A M N x m hI hP hB hx hBI ha hA hm hh`. Take `⟨G, J, hJ, hJ1⟩` from `hDeg D K ι Ω κ y k₀ M N x hP hB hx hBI`. Establish `himg` using `hIm K ι Ω κ y k₀ M N x hBI`. Establish `key` using `hCM I hI K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) G J (fun _ => HermLine.ofCone m) (fun _ => A) hP (isMultiHomog_blockForms k₀ M) (isBasePtFree_blockForms hBI) (by rw [himg]; exact hx) hJ (fun _ => isSmoothHerm_ofCone hm) (fun _ …`. Rewrite using `[ha]`.

Apply the tactic sequence `by_cases hk : k = k₀ <;> simp [unitDeg, blockDeg, HermLine.ofCone, hk])`. Use the proof step `(fun _ z hz => by rw [hh z hz, formApply_blockForms]; rfl)`. Rewrite `key` using `[himg, hJ1]`. Simplify `key` using `[top]`.
-/
theorem BlockImageTop.proof (hCM : GraphChangeOfModel.Statement) (hIm : BlockGraphImage.Statement)
    (hDeg : BlockGraphDeg.Statement) : BlockImageTop.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ I y k₀ A M N x m hI hP hB hx hBI ha hA hm hh
  obtain ⟨G, J, hJ, hJ1⟩ := hDeg D K ι Ω κ y k₀ M N x hP hB hx hBI
  have himg := hIm K ι Ω κ y k₀ M N x hBI
  have key := hCM I hI K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) G J
    (fun _ => HermLine.ofCone m) (fun _ => A) hP (isMultiHomog_blockForms k₀ M) (isBasePtFree_blockForms hBI)
    (by rw [himg]; exact hx) hJ (fun _ => isSmoothHerm_ofCone hm) (fun _ => hA)
    (fun _ k => by
      rw [ha]
      by_cases hk : k = k₀ <;> simp [unitDeg, blockDeg, HermLine.ofCone, hk])
    (fun _ z hz => by rw [hh z hz, formApply_blockForms]; rfl)
  rw [himg, hJ1] at key
  simpa [top] using key

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
