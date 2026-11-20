import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.SimplexMem

noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def simp' (q : ℕ) : Set (Fin q → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

/- English proof (translation)
Establish `: simp' q = (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1}`. Use extensionality with `t`. Simplify using `[simp']`. Rewrite using `[this]`. Conclude with `(isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)`.
-/
theorem isClosed_simp' (q : ℕ) : IsClosed (simp' q) := by
  have : simp' q = (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by
    ext t; simp [simp']
  rw [this]
  exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)

/- English proof (translation)
Use `(isCompact_univ_pi fun _ => isCompact_Icc (a := (0:ℝ)) (b := 1)).of_isClosed_subset (isClosed_simp' q) ?_` and prove the remaining obligations. Introduce `t ht j _`. Conclude with `⟨ht.1 j, le_trans (Finset.single_le_sum (fun i _ => ht.1 i) (Finset.mem_univ j)) ht.2⟩`.
-/
theorem isCompact_simp' (q : ℕ) : IsCompact (simp' q) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0:ℝ)) (b := 1)).of_isClosed_subset (isClosed_simp' q) ?_
  intro t ht j _
  exact ⟨ht.1 j, le_trans (Finset.single_le_sum (fun i _ => ht.1 i) (Finset.mem_univ j)) ht.2⟩

/- English proof (translation)
Establish `e : y 0 + ∑ j, t j • (y j.succ - y 0) = ∑ i : Fin (q + 1), (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Use `hU.sum_mem (fun i _ => ?_) ?_ (fun i _ => hy i)` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`. Combine the linear relations using `[ht.2]`. Simplify using `only [Fin.cons_succ]`.

Conclude with `ht.1 j`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using the standard rewrite rules.
-/
private theorem simplex_point_mem_of_convex_of_mem_simp' {U : Set V} (hU : Convex ℝ U) {q : ℕ} {y : Fin (q + 1) → V}
    (hy : ∀ j, y j ∈ U) {t : Fin q → ℝ} (ht : t ∈ simp' q) :
    y 0 + ∑ j, t j • (y j.succ - y 0) ∈ U := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i : Fin (q + 1), (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul,
      one_smul]
    abel
  rw [e]
  refine hU.sum_mem (fun i _ => ?_) ?_ (fun i _ => hy i)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      linarith [ht.2]
    · simp only [Fin.cons_succ]
      exact ht.1 j
  · rw [Fin.sum_univ_succ]
    simp

/- English proof (translation)
Establish `hg : Continuous fun t : Fin q → ℝ => y 0 + ∑ j, t j • (y j.succ - y 0)` using `by fun_prop`. Establish `hc : ContinuousOn (fun t : Fin q → ℝ => ω (y 0 + ∑ j, t j • (y j.succ - y 0))) (simp' q)` using `hω.comp hg.continuousOn fun t ht => simplex_point_mem_of_convex_of_mem_simp' hU hy ht`. Conclude with `(hc.eval_const _).integrableOn_compact (isCompact_simp' q)`.
-/
theorem integrableOn_simp {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ω : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (hω : ContinuousOn ω U) {y : Fin (q + 1) → V} (hy : ∀ j, y j ∈ U) :
    IntegrableOn (fun t : Fin q → ℝ => ω (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0)
      (simp' q) := by
  have hg : Continuous fun t : Fin q → ℝ => y 0 + ∑ j, t j • (y j.succ - y 0) := by fun_prop
  have hc : ContinuousOn (fun t : Fin q → ℝ => ω (y 0 + ∑ j, t j • (y j.succ - y 0))) (simp' q) :=
    hω.comp hg.continuousOn fun t ht => simplex_point_mem_of_convex_of_mem_simp' hU hy ht
  exact (hc.eval_const _).integrableOn_compact (isCompact_simp' q)

/- English proof (translation)
Unfold `intS'`. Use `setIntegral_congr_fun (isClosed_simp' q).measurableSet fun t ht => ?_` and prove the remaining obligations. Simplify using `only [h _ (simplex_point_mem_of_convex_of_mem_simp' hU hy ht)]`.
-/
theorem intS'_congr {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ω ω' : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (h : ∀ x ∈ U, ω x = ω' x) {y : Fin (q + 1) → V} (hy : ∀ j, y j ∈ U) :
    intS' ω y = intS' ω' y := by
  unfold intS'
  refine setIntegral_congr_fun (isClosed_simp' q).measurableSet fun t ht => ?_
  simp only [h _ (simplex_point_mem_of_convex_of_mem_simp' hU hy ht)]

/- English proof (translation)
Unfold `intS'`. Establish `e : ∀ t : Fin q → ℝ, ((∑ i ∈ s, a i • ω i) (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0) = ∑ i ∈ s, a i * ω i (y 0 + ∑ j, t j • (y j.succ - y 0)) (fun j => y j.succ - y 0)`. Introduce `t`. Simplify using `[Finset.sum_apply, ContinuousAlternatingMap.sum_apply]`. Repeatedly rewrite using `[e]`.

Establish `hs` using `integral_finset_sum (μ := volume.restrict (simp' q)) s fun i hi => (integrableOn_simp hU (hω i hi) hy).const_mul (a i)`. Unfold `simp' at hs`. Rewrite using `[hs]`. Repeatedly rewrite using `[integral_const_mul]`.
-/
theorem intS'_sum {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ι : Type} (s : Finset ι) (a : ι → ℝ)
    (ω : ι → V → V [⋀^Fin q]→L[ℝ] ℝ) (hω : ∀ i ∈ s, ContinuousOn (ω i) U) {y : Fin (q + 1) → V}
    (hy : ∀ j, y j ∈ U) :
    intS' (∑ i ∈ s, a i • ω i) y = ∑ i ∈ s, a i * intS' (ω i) y := by
  unfold intS'
  have e : ∀ t : Fin q → ℝ, ((∑ i ∈ s, a i • ω i) (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0)
      = ∑ i ∈ s, a i * ω i (y 0 + ∑ j, t j • (y j.succ - y 0)) (fun j => y j.succ - y 0) := by
    intro t
    simp [Finset.sum_apply, ContinuousAlternatingMap.sum_apply]
  simp_rw [e]
  have hs := integral_finset_sum (μ := volume.restrict (simp' q)) s
    fun i hi => (integrableOn_simp hU (hω i hi) hy).const_mul (a i)
  unfold simp' at hs
  rw [hs]
  simp_rw [integral_const_mul]

end PositivityTheory.KB.WhittakerCocycle

end
