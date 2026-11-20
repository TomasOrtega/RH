import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

/- English proof (translation)
Unfold `PositivityTheory.Rg.BcB.E2.Point`. Introduce `B _ _ _ _ S _ _ e p hp`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Use `choose b hb using hne`.

Set `c : S → B` to `fun s => b s - algebraMap ℂ B (p (b s))`. Establish `hpc : ∀ s, p (c s) = 0` using `fun s => by`. Simplify using `only [c, map_sub]`. Rewrite using `[AlgHomClass.commutes]`. Simplify using the standard rewrite rules.

Establish `hec : ∀ s, e (c s) s ≠ 0` using `fun s => by`. Establish `h1 : e (c s) s = e (b s) s - p (b s)`. Simplify using `only [c, map_sub, ContinuousMap.sub_apply]`. Rewrite using `[AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]`. Rewrite using `[h1]`.

Conclude with `sub_ne_zero.2 (hb s)`. Set `g : S → B` to `fun s => star (c s) * c s`. Establish `hpg : ∀ s, p (g s) = 0` using `fun s => by simp [g, hpc]`. Establish `heg : ∀ s t, e (g s) t = ((‖e (c s) t‖ ^ 2 : ℝ) : ℂ)` using `fun s t => by`. Simplify using `only [g, map_mul, map_star, ContinuousMap.mul_apply, ContinuousMap.star_apply]`.

Rewrite using `[Complex.ofReal_pow]`. Conclude with `Complex.conj_mul' _`. Take `⟨F, hF⟩` from `isCompact_univ.elim_finite_subcover (fun s => {t : S | e (c s) t ≠ 0}) (fun s => isOpen_compl_singleton.preimage (e (c s)).continuous) (fun t _ => Set.mem_iUnion.2 ⟨t, hec t⟩)`. Set `G : B` to `∑ s ∈ F, g s`. Set `v : S → ℝ` to `fun t => ∑ s ∈ F, ‖e (c s) t‖ ^ 2`.

Establish `hpG : p G = 0` using `by simp [G, hpg]`. Establish `heG : ∀ t, e G t = (v t : ℂ)` using `fun t => by`. Simplify using `only [G, v, map_sum, ContinuousMap.sum_apply, heg]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hv : ∀ t, 0 < v t` using `fun t => by`. Take `⟨s, hsF, hs⟩` from `Set.mem_iUnion₂.1 (hF (Set.mem_univ t))`. Establish `hs' : e (c s) t ≠ 0` using `hs`. Conclude with `Finset.sum_pos' (fun i _ => by positivity) ⟨s, hsF, pow_pos (norm_pos_iff.2 hs') 2⟩`. Establish `hvM : ∀ t, v t ≤ ‖e G‖` using `fun t => by`.

Establish `h1` using `ContinuousMap.norm_coe_le_norm (e G) t`. Rewrite `h1` using `[heG, Complex.norm_real, Real.norm_of_nonneg (hv t).le]`. Conclude with `h1`. Establish `hM : 0 ≤ ‖e G‖` using `norm_nonneg _`. Establish `key` using `hp (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)`.

Establish `hp1 : p (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) = 1` using `by simp [hpG]`. Rewrite `key` using `[hp1, norm_one]`. Establish `hlt : ‖e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)‖ < 1`. Rewrite using `[ContinuousMap.norm_lt_iff _ one_pos]`. Introduce `t`.

Establish `ht : e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) t = ((1 - v t / (‖e G‖ + 1) : ℝ) : ℂ)`. Simplify using `only [map_sub, map_one, map_smul, ContinuousMap.sub_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply, heG, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ht, Complex.norm_real, Real.norm_eq_abs, abs_lt]`.

Establish `h2 : v t / (‖e G‖ + 1) < 1`. Rewrite using `[div_lt_one (by linarith)]`. Combine the linear relations using `[hvM t]`. Establish `h3 : 0 < v t / (‖e G‖ + 1)` using `div_pos (hv t) (by linarith)`. Apply the tactic sequence `constructor <;> linarith`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem point : Point := by
  unfold PositivityTheory.Rg.BcB.E2.Point
  intro B _ _ _ _ S _ _ e p hp
  by_contra hne
  push Not at hne
  choose b hb using hne
  let c : S → B := fun s => b s - algebraMap ℂ B (p (b s))
  have hpc : ∀ s, p (c s) = 0 := fun s => by
    simp only [c, map_sub]
    rw [AlgHomClass.commutes]
    simp
  have hec : ∀ s, e (c s) s ≠ 0 := fun s => by
    have h1 : e (c s) s = e (b s) s - p (b s) := by
      simp only [c, map_sub, ContinuousMap.sub_apply]
      rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one]
    rw [h1]
    exact sub_ne_zero.2 (hb s)
  let g : S → B := fun s => star (c s) * c s
  have hpg : ∀ s, p (g s) = 0 := fun s => by simp [g, hpc]
  have heg : ∀ s t, e (g s) t = ((‖e (c s) t‖ ^ 2 : ℝ) : ℂ) := fun s t => by
    simp only [g, map_mul, map_star, ContinuousMap.mul_apply, ContinuousMap.star_apply]
    rw [Complex.ofReal_pow]
    exact Complex.conj_mul' _
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun s => {t : S | e (c s) t ≠ 0})
    (fun s => isOpen_compl_singleton.preimage (e (c s)).continuous)
    (fun t _ => Set.mem_iUnion.2 ⟨t, hec t⟩)
  let G : B := ∑ s ∈ F, g s
  let v : S → ℝ := fun t => ∑ s ∈ F, ‖e (c s) t‖ ^ 2
  have hpG : p G = 0 := by simp [G, hpg]
  have heG : ∀ t, e G t = (v t : ℂ) := fun t => by
    simp only [G, v, map_sum, ContinuousMap.sum_apply, heg]
    push_cast
    rfl
  have hv : ∀ t, 0 < v t := fun t => by
    obtain ⟨s, hsF, hs⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ t))
    have hs' : e (c s) t ≠ 0 := hs
    exact Finset.sum_pos' (fun i _ => by positivity) ⟨s, hsF, pow_pos (norm_pos_iff.2 hs') 2⟩
  have hvM : ∀ t, v t ≤ ‖e G‖ := fun t => by
    have h1 := ContinuousMap.norm_coe_le_norm (e G) t
    rw [heG, Complex.norm_real, Real.norm_of_nonneg (hv t).le] at h1
    exact h1
  have hM : 0 ≤ ‖e G‖ := norm_nonneg _
  have key := hp (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)
  have hp1 : p (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) = 1 := by simp [hpG]
  rw [hp1, norm_one] at key
  have hlt : ‖e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)‖ < 1 := by
    rw [ContinuousMap.norm_lt_iff _ one_pos]
    intro t
    have ht : e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) t = ((1 - v t / (‖e G‖ + 1) : ℝ) : ℂ) := by
      simp only [map_sub, map_one, map_smul, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        ContinuousMap.smul_apply, heG, smul_eq_mul]
      push_cast
      ring
    rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    have h2 : v t / (‖e G‖ + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith [hvM t]
    have h3 : 0 < v t / (‖e G‖ + 1) := div_pos (hv t) (by linarith)
    constructor <;> linarith
  linarith

end PositivityTheory.Rg.BcB.E2.P
