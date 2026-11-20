import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsVeroneseGraph
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecondVeronese
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageTop
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIMultilin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace VeroneseTop

/- English proof (translation)
Establish `h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1), f p = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p`. Use `Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `using hp`. Introduce `p hp`.

Simplify using `using hp`. Introduce `p _`. Both sides reduce to the same expression. Introduce `p _`. Both sides reduce to the same expression.

Introduce `p _`. Conclude with `hf p.1 p.2`. Establish `h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then 0 else f p)`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_filter]`. Use `congr 1`.

Use extensionality with `p`. Simplify using `[lt_iff_le_and_ne]`. Establish `h3 : Finset.univ.filter (fun p : Fin n × Fin n => ¬ p.1 ≤ p.2) = Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)`. Use extensionality with `p`. Simplify using the standard rewrite rules.

Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n => p.1 ≤ p.2), h3, h1, h2, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem sum_le_weighted {n : ℕ} (f : Fin n × Fin n → ℝ) (hf : ∀ i j, f (i, j) = f (j, i)) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then (1 : ℝ) else 2) * f p =
      ∑ p, f p := by
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1), f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simpa using hp
    · intro p hp
      simpa using hp
    · intro p _
      rfl
    · intro p _
      rfl
    · intro p _
      exact hf p.1 p.2
  have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then 0 else f p) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_filter]
    congr 1
    ext p
    simp [lt_iff_le_and_ne]
  have h3 : Finset.univ.filter (fun p : Fin n × Fin n => ¬ p.1 ≤ p.2) =
      Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1) := by
    ext p
    simp
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n => p.1 ≤ p.2), h3, h1, h2,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[Fintype.sum_sigma, Fintype.sum_unique]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]`. Use `_ = ∑ p : Fin (D + 1) × Fin (D + 1), a p.1 * a p.2 := sum_le_weighted (fun p => a p.1 * a p.2) (fun i j => mul_comm _ _)`. Use `_ = (∑ i, a i) ^ 2 := by`.

Rewrite using `[sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]`.
-/
theorem sum_wt_mul {D : ℕ} (a : Fin (D + 1) → ℝ) :
    ∑ q : Ix (Veronese.Idx D), Veronese.wt q * (a q.2.1.1 * a q.2.1.2) = (∑ i, a i) ^ 2 := by
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  calc ∑ y : Veronese.Idx D, Veronese.wt (⟨default, y⟩ : Ix (Veronese.Idx D)) * (a y.1.1 * a y.1.2)
      = ∑ y : Veronese.Idx D, (if y.1.1 = y.1.2 then (1 : ℝ) else 2) * (a y.1.1 * a y.1.2) := rfl
    _ = ∑ p ∈ Finset.univ.filter (fun p : Fin (D + 1) × Fin (D + 1) => p.1 ≤ p.2),
          (if p.1 = p.2 then (1 : ℝ) else 2) * (a p.1 * a p.2) := by
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    _ = ∑ p : Fin (D + 1) × Fin (D + 1), a p.1 * a p.2 :=
      sum_le_weighted (fun p => a p.1 * a p.2) (fun i j => mul_comm _ _)
    _ = (∑ i, a i) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]

/- English proof (translation)
Use `show ‖WithLp.toLp 2 z‖ ^ 2 = _`. Rewrite using `[EuclideanSpace.norm_sq_eq]`.
-/
theorem fs_sq {J : Type} [Fintype J] (z : J → ℂ) : (fsMetric J).ρ z ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  show ‖WithLp.toLp 2 z‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]

/- English proof (translation)
The claim follows from `norm_nonneg (WithLp.toLp 2 z)`.
-/
theorem fs_nonneg {J : Type} [Fintype J] (z : J → ℂ) : 0 ≤ (fsMetric J).ρ z :=
  norm_nonneg (WithLp.toLp 2 z)

/- English proof (translation)
The claim follows from `fs_nonneg (Veronese.scale D u)`.
-/
theorem metric_nonneg (D : ℕ) (u : Ix (Veronese.Idx D) → ℂ) : 0 ≤ (Veronese.metric D).ρ u :=
  fs_nonneg (Veronese.scale D u)

/- English proof (translation)
Use `show (fsMetric _).ρ (Veronese.scale D u) ^ 2 = _`. Rewrite using `[fs_sq]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `hw : 0 ≤ Veronese.wt q` using `(Veronese.wt_pos q).le`. Rewrite using `[Veronese.scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hw]`.
-/
theorem metric_sq (D : ℕ) (u : Ix (Veronese.Idx D) → ℂ) :
    (Veronese.metric D).ρ u ^ 2 = ∑ q, Veronese.wt q * ‖u q‖ ^ 2 := by
  show (fsMetric _).ρ (Veronese.scale D u) ^ 2 = _
  rw [fs_sq]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hw : 0 ≤ Veronese.wt q := (Veronese.wt_pos q).le
  rw [Veronese.scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hw]

/- English proof (translation)
Simplify using `[formApply, Veronese.forms]`.
-/
theorem formApply_forms (D : ℕ) (w : Ix (Fin (D + 1)) → ℂ) (q : Ix (Veronese.Idx D)) :
    formApply (Veronese.forms D) w q = w ⟨(), q.2.1.1⟩ * w ⟨(), q.2.1.2⟩ := by
  simp [formApply, Veronese.forms]

/- English proof (translation)
Establish `h0 : 0 ≤ (Veronese.metric D).ρ (formApply (Veronese.forms D) w)` using `metric_nonneg D _`. Establish `h1 : 0 ≤ (fsMetric (Ix (Fin (D + 1)))).ρ w * (fsMetric (Ix (Fin (D + 1)))).ρ w` using `mul_nonneg (fs_nonneg w) (fs_nonneg w)`. Use `(sq_eq_sq₀ h0 h1).1 ?_` and prove the remaining obligations. Establish `hw : (fsMetric (Ix (Fin (D + 1)))).ρ w * (fsMetric (Ix (Fin (D + 1)))).ρ w = ∑ i : Fin (D + 1), ‖w ⟨(), i⟩‖ ^ 2`. Rewrite using `[← sq, fs_sq, Fintype.sum_sigma, Fintype.sum_unique]`.

Rewrite using `[hw, metric_sq, ← sum_wt_mul]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[formApply_forms, norm_mul, mul_pow]`.
-/
theorem metric_forms (D : ℕ) (w : Ix (Fin (D + 1)) → ℂ) :
    (Veronese.metric D).ρ (formApply (Veronese.forms D) w) =
      (fsMetric (Ix (Fin (D + 1)))).ρ w * (fsMetric (Ix (Fin (D + 1)))).ρ w := by
  have h0 : 0 ≤ (Veronese.metric D).ρ (formApply (Veronese.forms D) w) :=
    metric_nonneg D _
  have h1 : 0 ≤ (fsMetric (Ix (Fin (D + 1)))).ρ w * (fsMetric (Ix (Fin (D + 1)))).ρ w :=
    mul_nonneg (fs_nonneg w) (fs_nonneg w)
  refine (sq_eq_sq₀ h0 h1).1 ?_
  have hw : (fsMetric (Ix (Fin (D + 1)))).ρ w * (fsMetric (Ix (Fin (D + 1)))).ρ w =
      ∑ i : Fin (D + 1), ‖w ⟨(), i⟩‖ ^ 2 := by
    rw [← sq, fs_sq, Fintype.sum_sigma, Fintype.sum_unique]
  rw [hw, metric_sq, ← sum_wt_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [formApply_forms, norm_mul, mul_pow]

/- English proof (translation)
Establish `h` using `Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1) (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)`. Establish `e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1`. Use function extensionality and compare the values at `k`. Consider the cases of `k`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem isMultiHomog_forms (D : ℕ) (q : Ix (Veronese.Idx D)) :
    IsMultiHomog (Veronese.forms D q) ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) := by
  have h := Inter.AvoidRing.isMultiHomog_mul
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1)
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)
  have e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1 := by
    funext k
    cases k
    simp
  rw [e]
  exact h

/- English proof (translation)
Introduce `k₂ i`. Use `⟨2, Ideal.mem_sup_right (Ideal.subset_span ⟨⟨(i (), i ()), le_rfl⟩, ?_⟩)⟩` and prove the remaining obligations. Consider the cases of `k₂`. Simplify using `[Veronese.forms, pow_two]`.
-/
theorem isBasePtFree_forms (D : ℕ) : IsBasePtFree (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) := by
  intro k₂ i
  refine ⟨2, Ideal.mem_sup_right (Ideal.subset_span ⟨⟨(i (), i ()), le_rfl⟩, ?_⟩)⟩
  cases k₂
  simp [Veronese.forms, pow_two]

/- English proof (translation)
Establish `hTT : IsSmoothHerm (T.tensor T)` using `hT.mul hT`. Establish `intersection_update_fsHerm_neg_one : ∀ L : Fin n → HermLine ι, (∀ i, IsSmoothHerm (L i)) → ∀ j : Fin n, F P n (Function.update L j (T.tensor T)) = 2 * F P n (Function.update L j T)`. Introduce `L hL j`. Consider the cases of `n with`. Consider the case `zero => exact j.elim0`.

Consider the case `succ m`. Establish `e : ∀ X : HermLine ι, IsSmoothHerm X → F P (m + 1) (Function.update L j X) = F P (m + 1) (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X)`. Introduce `X hX`. Rewrite using `[← Inter.ThmIMultilin.update_comp_swap]`. Conclude with `(hF.1 P (m + 1) _ _ hP (Inter.ThmIMultilin.smooth_update hL j hX)).symm`.

Rewrite using `[e _ hTT, e T hT, hF.2.1 P m _ T T hP (fun i => hL _) hT hT]`. Expand and normalize the polynomial expressions, which then agree. Establish `step : ∀ k, k ≤ n → F P n (fun i => if (i : ℕ) < k then T.tensor T else T) = 2 ^ k * F P n (fun _ => T)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `_`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `hk`.

Establish `hL : ∀ i : Fin n, IsSmoothHerm (if (i : ℕ) < k then T.tensor T else T)`. Introduce `i`. Use `split_ifs`. Conclude with `hTT`. Conclude with `hT`.

Establish `h1 : (fun i : Fin n => if (i : ℕ) < k + 1 then T.tensor T else T) = Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ (T.tensor T)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = ⟨k, hk⟩`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Establish `h' : (i : ℕ) ≠ k` using `fun e => h (Fin.ext e)`. Rewrite using `[Function.update_of_ne h]`. Distinguish the cases in `hi : (i : ℕ) < k`. Simplify using `[hi, show (i : ℕ) < k + 1 by omega]`. Simplify using `[hi, show ¬ (i : ℕ) < k + 1 by omega]`.

Establish `h2 : Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ T = fun i : Fin n => if (i : ℕ) < k then T.tensor T else T`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = ⟨k, hk⟩`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne h]`. Rewrite using `[h1, intersection_update_fsHerm_neg_one _ hL, h2, ih (by omega), pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn` using `step n le_rfl`. Simplify using `only [Fin.is_lt, if_true] at hn`.

Conclude with `hn`.
-/
theorem tensor_self {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hF : IsIntersectionFamily F)
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) {T : HermLine ι} (hT : IsSmoothHerm T) :
    F P n (fun _ => T.tensor T) = 2 ^ n * F P n (fun _ => T) := by
  have hTT : IsSmoothHerm (T.tensor T) := hT.mul hT
  have intersection_update_fsHerm_neg_one : ∀ L : Fin n → HermLine ι, (∀ i, IsSmoothHerm (L i)) → ∀ j : Fin n,
      F P n (Function.update L j (T.tensor T)) = 2 * F P n (Function.update L j T) := by
    intro L hL j
    cases n with
    | zero => exact j.elim0
    | succ m =>
      have e : ∀ X : HermLine ι, IsSmoothHerm X →
          F P (m + 1) (Function.update L j X) =
            F P (m + 1) (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
        intro X hX
        rw [← Inter.ThmIMultilin.update_comp_swap]
        exact (hF.1 P (m + 1) _ _ hP (Inter.ThmIMultilin.smooth_update hL j hX)).symm
      rw [e _ hTT, e T hT, hF.2.1 P m _ T T hP (fun i => hL _) hT hT]
      ring
  have step : ∀ k, k ≤ n →
      F P n (fun i => if (i : ℕ) < k then T.tensor T else T) = 2 ^ k * F P n (fun _ => T) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hL : ∀ i : Fin n, IsSmoothHerm (if (i : ℕ) < k then T.tensor T else T) := by
        intro i
        split_ifs
        · exact hTT
        · exact hT
      have h1 : (fun i : Fin n => if (i : ℕ) < k + 1 then T.tensor T else T) =
          Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ (T.tensor T) := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp
        · have h' : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
          rw [Function.update_of_ne h]
          by_cases hi : (i : ℕ) < k
          · simp [hi, show (i : ℕ) < k + 1 by omega]
          · simp [hi, show ¬ (i : ℕ) < k + 1 by omega]
      have h2 : Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ T =
          fun i : Fin n => if (i : ℕ) < k then T.tensor T else T := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp
        · rw [Function.update_of_ne h]
      rw [h1, intersection_update_fsHerm_neg_one _ hL, h2, ih (by omega), pow_succ]
      ring
  have hn := step n le_rfl
  simp only [Fin.is_lt, if_true] at hn
  exact hn

end VeroneseTop

open VeroneseTop in

/- English proof (translation)
Introduce `D hD I hI`. Take `⟨G, J, hJ, hJ1⟩` from `hDeg D hD`. Establish `hfs : IsSmoothHerm (HermLine.ofCone (fsMetric (Ix (Fin (D + 1)))))` using `BlockImageTop.isSmoothHerm_ofCone ProjLine.isSmoothMetric_fs`. Establish `hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1)` using `IndefiniteRowSideFullHecke.Inter.isArithVar_bot D`. Establish `key` using `hCM I hI Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D) (fun _ _ => 2) G J (fun _ => HermLine.ofCone (Veronese.metric D)) (fun _ => (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))).tensor (HermLine.ofCone (fsMetric (Ix (Fin (D + …`.

Rewrite `key` using `[hIm D, hJ1]`. Establish `h2` using `tensor_self (hI Unit (GlobalTheory (Fin (D + 1)))) hP hfs`. Rewrite `key` using `[Int.cast_one, one_mul]`. Rewrite using `[top, hhOf, ← key, ← h2]`.
-/
theorem VeroneseTop.proof (hCM : GraphChangeOfModel.Statement) (hA : VeroneseArith.Statement)
    (hIm : VeroneseGraphImage.Statement) (hDeg : VeroneseGraphDeg.Statement) : VeroneseTop.Statement := by
  intro D hD I hI
  obtain ⟨G, J, hJ, hJ1⟩ := hDeg D hD
  have hfs : IsSmoothHerm (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))) :=
    BlockImageTop.isSmoothHerm_ofCone ProjLine.isSmoothMetric_fs
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot D
  have key := hCM I hI Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D)
    (fun _ _ => 2) G J (fun _ => HermLine.ofCone (Veronese.metric D))
    (fun _ => (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))).tensor (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))))
    hP (isMultiHomog_forms D) (isBasePtFree_forms D) (by rw [hIm D]; exact hA D hD) hJ
    (fun _ => BlockImageTop.isSmoothHerm_ofCone (Veronese.isSmoothMetric_metric D)) (fun _ => hfs.mul hfs)
    (fun _ k => by cases k; simp [HermLine.tensor, HermLine.ofCone])
    (fun _ z _ => (metric_forms D z).symm)
  rw [hIm D, hJ1] at key
  have h2 := tensor_self (hI Unit (GlobalTheory (Fin (D + 1)))) hP hfs
  rw [Int.cast_one, one_mul] at key
  rw [top, hhOf, ← key, ← h2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
