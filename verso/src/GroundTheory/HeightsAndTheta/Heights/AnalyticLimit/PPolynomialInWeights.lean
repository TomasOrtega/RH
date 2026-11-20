import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceStatements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm (hessC maDens mdisc)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith
  MIntegrable)

noncomputable section

section Expansion

variable {D : ℕ} {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/- English proof (translation)
Set `f : Fin D → ι → (Fin D → ℂ) → ℝ` to `fun k o y' => (B k o).φ ((A.chart j).symm y) ((A.chart j).symm y')`. Establish `hS : ∀ k, hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y = ∑ o, (x o : ℂ) • hessC (f k o) y` using `fun k => by`. Repeatedly rewrite using `[hΦ]`. Conclude with `hessC_finset_sum _ _ (f k) y fun o _ => ReciprocityTheory.AnForm.M.potential_contDiffAt A (B k o) (hB k o) j hy`. Take `⟨M, hM⟩` from `ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)`.

Establish `hL : locDens A Φ j y = (D.factorial : ℝ) * (2 / Real.pi) ^ D * (M fun k => ∑ o, (x o : ℂ) • hessC (f k o) y).re`. Simplify using `only [locDens, maDens, hS, hM]`. Establish `hR : ∀ σ : Fin D → ι, locDens A (fun k => B k (σ k)) j y = (D.factorial : ℝ) * (2 / Real.pi) ^ D * (M fun k => hessC (f k (σ k)) y).re` using `fun σ => by`. Rewrite using `[hM]`. Both sides reduce to the same expression.

Rewrite using `[hL, MultilinearMap.map_sum, Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ, hR, smul_eq_mul, ← Complex.ofReal_prod, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locDens_expand (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (B : Fin D → ι → LocPot X)
    (hB : ∀ k o, IsPotential A (B k o)) (x : ι → ℝ)
    (hΦ : ∀ k b z, (Φ k).φ b z = ∑ o, x o * (B k o).φ b z) (j : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart j).target) :
    locDens A Φ j y = ∑ σ : Fin D → ι, (∏ k, x (σ k)) * locDens A (fun k => B k (σ k)) j y := by
  let f : Fin D → ι → (Fin D → ℂ) → ℝ := fun k o y' =>
    (B k o).φ ((A.chart j).symm y) ((A.chart j).symm y')
  have hS : ∀ k, hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ o, (x o : ℂ) • hessC (f k o) y := fun k => by
    simp_rw [hΦ]
    exact hessC_finset_sum _ _ (f k) y fun o _ =>
      ReciprocityTheory.AnForm.M.potential_contDiffAt A (B k o) (hB k o) j hy
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have hL : locDens A Φ j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (M fun k => ∑ o, (x o : ℂ) • hessC (f k o) y).re := by
    simp only [locDens, maDens, hS, hM]
  have hR : ∀ σ : Fin D → ι, locDens A (fun k => B k (σ k)) j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (M fun k => hessC (f k (σ k)) y).re := fun σ => by
    rw [hM]
    rfl
  rw [hL, MultilinearMap.map_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.map_smul_univ, hR, smul_eq_mul, ← Complex.ofReal_prod, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Introduce `j K hKt hK`. Conclude with `(((hw j).mul (ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j)).mono hKt).integrableOn_compact hK`.
-/
theorem mIntegrable_of_continuousOn (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (hΦ : ∀ k, IsPotential A (Φ k)) (w : X → ℝ)
    (hw : ∀ j, ContinuousOn (fun y => w ((A.chart j).symm y)) (A.chart j).target) :
    MIntegrable A Φ w := by
  intro j K hKt hK
  exact (((hw j).mul (ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j)).mono hKt).integrableOn_compact hK

/- English proof (translation)
Unfold `mInt`. Use `split_ifs with h`. Unfold `integralWith`. Establish `hI : ∀ (o : ι) (σ : Fin D → ι) (j : Fin A.n), IntegrableOn (fun y => h.some.χ j ((A.chart j).symm y) * w o ((A.chart j).symm y) * locDens A (fun k => B k (σ k)) j y) (A.chart j).target` using `fun o σ j => ReciprocityTheory.AnForm.M.integrableOn_weight A h.some _ _ (mIntegrable_of_continuousOn A _ (fun k => hB k (σ k)) _ (hw o)) j`. Establish `hj : ∀ j, ∫ y in (A.chart j).target, h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y = ∑ o, ∑ σ : Fin D → ι, (x o * ∏ k, x (σ k)) * ∫ y in (A.chart j).target, h.some.χ j ((A.chart j).symm y) * w o ((A.chart j).symm y) * locDens A (fun k => B k (σ k)) j …`.

Introduce `j`. Combine the equalities or inequalities in the displayed calculation. Use `setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_` and prove the remaining obligations. Rewrite using `[hg, locDens_expand A Φ B hB x hΦ j hy, mul_assoc, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun o _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[integral_finsetSum _ fun o _ => integrable_finsetSum _ fun σ _ => (hI o σ j).const_mul _]`.

Use `Finset.sum_congr rfl fun o _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finsetSum _ fun σ _ => (hI o σ j).const_mul _]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Conclude with `integral_const_mul _ _`. Rewrite using `[Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun o _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Simplify using the standard rewrite rules.
-/
theorem mInt_expand [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (B : Fin D → ι → LocPot X) (hB : ∀ k o, IsPotential A (B k o)) (x : ι → ℝ)
    (hΦ : ∀ k b z, (Φ k).φ b z = ∑ o, x o * (B k o).φ b z) (g : X → ℝ) (w : ι → X → ℝ)
    (hw : ∀ o j, ContinuousOn (fun y => w o ((A.chart j).symm y)) (A.chart j).target)
    (hg : ∀ p, g p = ∑ o, x o * w o p) :
    mInt A Φ g =
      ∑ o, ∑ σ : Fin D → ι, (x o * ∏ k, x (σ k)) * mInt A (fun k => B k (σ k)) (w o) := by
  unfold mInt
  split_ifs with h
  · unfold integralWith
    have hI : ∀ (o : ι) (σ : Fin D → ι) (j : Fin A.n), IntegrableOn (fun y =>
        h.some.χ j ((A.chart j).symm y) * w o ((A.chart j).symm y) *
          locDens A (fun k => B k (σ k)) j y) (A.chart j).target := fun o σ j =>
      ReciprocityTheory.AnForm.M.integrableOn_weight A h.some _ _
        (mIntegrable_of_continuousOn A _ (fun k => hB k (σ k)) _ (hw o)) j
    have hj : ∀ j, ∫ y in (A.chart j).target,
        h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
        ∑ o, ∑ σ : Fin D → ι, (x o * ∏ k, x (σ k)) * ∫ y in (A.chart j).target,
          h.some.χ j ((A.chart j).symm y) * w o ((A.chart j).symm y) *
            locDens A (fun k => B k (σ k)) j y := by
      intro j
      calc ∫ y in (A.chart j).target,
            h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y
          = ∫ y in (A.chart j).target, ∑ o, ∑ σ : Fin D → ι, (x o * ∏ k, x (σ k)) *
              (h.some.χ j ((A.chart j).symm y) * w o ((A.chart j).symm y) *
                locDens A (fun k => B k (σ k)) j y) := by
            refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
            rw [hg, locDens_expand A Φ B hB x hΦ j hy, mul_assoc, Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            ring
        _ = _ := by
            rw [integral_finsetSum _ fun o _ =>
              integrable_finsetSum _ fun σ _ => (hI o σ j).const_mul _]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [integral_finsetSum _ fun σ _ => (hI o σ j).const_mul _]
            refine Finset.sum_congr rfl fun σ _ => ?_
            exact integral_const_mul _ _
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
  · simp

/- English proof (translation)
Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.totalDegree_C, zero_add]`. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.totalDegree_X, add_comm]`. Use `Nat.add_le_add_right ((MvPolynomial.totalDegree_finsetProd _ _).trans ?_) 1` and prove the remaining obligations.

Simplify using `[MvPolynomial.totalDegree_X]`.
-/
theorem totalDegree_C_mul_X_mul_prod_le {κ : Type} (c : ℝ) (o : κ) (σ : Fin D → κ) :
    (MvPolynomial.C c * (MvPolynomial.X o * ∏ i, MvPolynomial.X (σ i)) :
      MvPolynomial κ ℝ).totalDegree ≤ D + 1 := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, add_comm]
  refine Nat.add_le_add_right ((MvPolynomial.totalDegree_finsetProd _ _).trans ?_) 1
  simp [MvPolynomial.totalDegree_X]

end Expansion

/- English proof (translation)
Introduce `X _ _ _ D A F a ha t ht`. Set `P : Option (Fin F.m) → LocPot X` to `fun o => o.elim a fun i => (F.R i).θ + LocPot.ofFun ((F.sys i).ph t)`. Set `Q : Option (Fin F.m) → LocPot X` to `fun o => o.elim a fun i => (F.R i).θ`. Set `w : Option (Fin F.m) → X → ℝ` to `fun o => o.elim (fun _ => 0) fun i => (F.sys i).ph t`. Set `B : ℕ → Fin D → Option (Fin F.m) → LocPot X` to `fun k i => if (i : ℕ) < k then P else Q`.

Establish `hsm : ∀ i, A.Smooth ((F.sys i).ph t)` using `fun i => (F.sys i).smooth t ht.1 (ht.2 i)`. Establish `hP : ∀ o, IsPotential A (P o)`. Introduce and unpack `(_ | i)`. Conclude with `ha`. Conclude with `ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hsm i))`.

Establish `hQ : ∀ o, IsPotential A (Q o)`. Introduce and unpack `(_ | i)`. Conclude with `ha`. Conclude with `(F.R i).θ_pot`. Establish `hB : ∀ k i o, IsPotential A (B k i o)`.

Introduce `k i o`. Distinguish the cases in `hik : (i : ℕ) < k`. Simplify using `only [B, if_pos hik]`. Conclude with `hP o`. Simplify using `only [B, if_neg hik]`.

Conclude with `hQ o`. Establish `hw : ∀ o j, ContinuousOn (fun y => w o ((A.chart j).symm y)) (A.chart j).target`. Introduce and unpack `(_ | i) j`. Conclude with `continuousOn_const`. Use `((hsm i) j).continuousOn` as an intermediate fact.

Rewrite `this` using `[Set.preimage_univ, Set.inter_univ]`. Conclude with `this`. Establish `hPφ : ∀ x b z, (F.coefForm a x t).φ b z = ∑ o, x o * (P o).φ b z`. Introduce `x b z`. Use `show (F.chernForm (fun i => x (some i)) t).φ b z + x none * a.φ b z = _`.

Rewrite using `[Family.chernForm, lincomb_φ, Fintype.sum_option, add_comm]`. Both sides reduce to the same expression. Establish `hQφ : ∀ x b z, (F.coefRefForm a x).φ b z = ∑ o, x o * (Q o).φ b z`. Introduce `x b z`. Use `show (lincomb F.m (fun i => x (some i)) (fun i => (F.R i).θ)).φ b z + x none * a.φ b z = _`.

Rewrite using `[lincomb_φ, Fintype.sum_option, add_comm]`. Both sides reduce to the same expression. Use `⟨∑ k ∈ Finset.range (D + 1), ∑ o, ∑ σ : Fin D → Option (Fin F.m), MvPolynomial.C (mInt A (fun i => B k i (σ i)) (w o)) * (MvPolynomial.X o * ∏ i, MvPolynomial.X (σ i)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `MvPolynomial.totalDegree_finsetSum_le fun k _ => MvPolynomial.totalDegree_finsetSum_le fun o _ => MvPolynomial.totalDegree_finsetSum_le fun σ _ => totalDegree_C_mul_X_mul_prod_le _ _ _`. Introduce `x`.

Simplify using `only [map_sum, map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X]`. Unfold `Family.weightEnergy`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mInt_expand A _ (B k) (hB k) x ?_ _ w hw ?_]`. Use `Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Introduce `i b z`. Distinguish the cases in `hik : (i : ℕ) < k`. Simplify using `only [B, if_pos hik]`. Conclude with `hPφ x b z`.

Simplify using `only [B, if_neg hik]`. Conclude with `hQφ x b z`. Introduce `p`. Simplify using `[Family.coefWeight, Fintype.sum_option, w]`.
-/
theorem PolynomialInWeights.proof : PolynomialInWeights.Statement := by
  intro X _ _ _ D A F a ha t ht
  classical
  let P : Option (Fin F.m) → LocPot X := fun o =>
    o.elim a fun i => (F.R i).θ + LocPot.ofFun ((F.sys i).ph t)
  let Q : Option (Fin F.m) → LocPot X := fun o => o.elim a fun i => (F.R i).θ
  let w : Option (Fin F.m) → X → ℝ := fun o => o.elim (fun _ => 0) fun i => (F.sys i).ph t
  let B : ℕ → Fin D → Option (Fin F.m) → LocPot X := fun k i => if (i : ℕ) < k then P else Q
  have hsm : ∀ i, A.Smooth ((F.sys i).ph t) := fun i => (F.sys i).smooth t ht.1 (ht.2 i)
  have hP : ∀ o, IsPotential A (P o) := by
    rintro (_ | i)
    · exact ha
    · exact ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot
        (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hsm i))
  have hQ : ∀ o, IsPotential A (Q o) := by
    rintro (_ | i)
    · exact ha
    · exact (F.R i).θ_pot
  have hB : ∀ k i o, IsPotential A (B k i o) := by
    intro k i o
    by_cases hik : (i : ℕ) < k
    · simp only [B, if_pos hik]; exact hP o
    · simp only [B, if_neg hik]; exact hQ o
  have hw : ∀ o j, ContinuousOn (fun y => w o ((A.chart j).symm y)) (A.chart j).target := by
    rintro (_ | i) j
    · exact continuousOn_const
    · have := ((hsm i) j).continuousOn
      rw [Set.preimage_univ, Set.inter_univ] at this
      exact this
  have hPφ : ∀ x b z, (F.coefForm a x t).φ b z = ∑ o, x o * (P o).φ b z := by
    intro x b z
    show (F.chernForm (fun i => x (some i)) t).φ b z + x none * a.φ b z = _
    rw [Family.chernForm, lincomb_φ, Fintype.sum_option, add_comm]
    rfl
  have hQφ : ∀ x b z, (F.coefRefForm a x).φ b z = ∑ o, x o * (Q o).φ b z := by
    intro x b z
    show (lincomb F.m (fun i => x (some i)) (fun i => (F.R i).θ)).φ b z + x none * a.φ b z = _
    rw [lincomb_φ, Fintype.sum_option, add_comm]
    rfl
  refine ⟨∑ k ∈ Finset.range (D + 1), ∑ o, ∑ σ : Fin D → Option (Fin F.m),
    MvPolynomial.C (mInt A (fun i => B k i (σ i)) (w o)) *
      (MvPolynomial.X o * ∏ i, MvPolynomial.X (σ i)), ?_, ?_⟩
  · exact MvPolynomial.totalDegree_finsetSum_le fun k _ =>
      MvPolynomial.totalDegree_finsetSum_le fun o _ =>
        MvPolynomial.totalDegree_finsetSum_le fun σ _ => totalDegree_C_mul_X_mul_prod_le _ _ _
  · intro x
    simp only [map_sum, map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X]
    unfold Family.weightEnergy
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mInt_expand A _ (B k) (hB k) x ?_ _ w hw ?_]
    · refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun σ _ => ?_
      ring
    · intro i b z
      by_cases hik : (i : ℕ) < k
      · simp only [B, if_pos hik]; exact hPφ x b z
      · simp only [B, if_neg hik]; exact hQφ x b z
    · intro p
      simp [Family.coefWeight, Fintype.sum_option, w]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
