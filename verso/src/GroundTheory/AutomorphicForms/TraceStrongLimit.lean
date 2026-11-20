import Mathlib
import GroundTheory.AutomorphicForms.TraceNormComp

namespace GroundTheory.Automorphic

open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section FinProj

variable {ι : Type*} [Fintype ι]

def finProj (u : ι → H) : H →L[ℂ] H := ∑ i, rankOne ℂ (u i) (u i)

/- English proof (translation)
Simplify using `[finProj, rankOne_apply]`.
-/
theorem finProj_apply (u : ι → H) (x : H) : finProj u x = ∑ i, ⟪u i, x⟫_ℂ • u i := by
  simp [finProj, rankOne_apply]

/- English proof (translation)
Rewrite using `[finProj_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem finProj_mem_span (u : ι → H) (x : H) : finProj u x ∈ Submodule.span ℂ (Set.range u) := by
  rw [finProj_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable {u : ι → H}

/- English proof (translation)
Rewrite using `[finProj_apply]`. Conclude with `hu.inner_right_fintype _ j`.
-/
theorem inner_finProj_right (hu : Orthonormal ℂ u) (x : H) (j : ι) :
    ⟪u j, finProj u x⟫_ℂ = ⟪u j, x⟫_ℂ := by
  rw [finProj_apply]
  exact hu.inner_right_fintype _ j

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hg`. Rewrite using `[sum_inner]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, inner_sub_right, inner_finProj_right hu, sub_self, mul_zero]`.
-/
theorem inner_sub_finProj_eq_zero (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ⟪g, x - finProj u x⟫_ℂ = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hg
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_smul_left, inner_sub_right, inner_finProj_right hu, sub_self, mul_zero]

/- English proof (translation)
Establish `hmem : finProj u x - g ∈ Submodule.span ℂ (Set.range u)` using `Submodule.sub_mem _ (finProj_mem_span u x) hg`. Establish `h0 : ⟪x - finProj u x, finProj u x - g⟫_ℂ = 0`. Rewrite using `[← inner_conj_symm, inner_sub_finProj_eq_zero hu x hmem, map_zero]`. Establish `h` using `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0`. Rewrite `h` using `[sub_add_sub_cancel]`.

Rewrite using `[mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), h]`. Conclude with `le_add_of_nonneg_right (mul_self_nonneg _)`.
-/
theorem norm_sub_finProj_le (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ‖x - finProj u x‖ ≤ ‖x - g‖ := by
  have hmem : finProj u x - g ∈ Submodule.span ℂ (Set.range u) :=
    Submodule.sub_mem _ (finProj_mem_span u x) hg
  have h0 : ⟪x - finProj u x, finProj u x - g⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_sub_finProj_eq_zero hu x hmem, map_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sub_add_sub_cancel] at h
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

/- English proof (translation)
Simplify using `using norm_sub_finProj_le hu x (Submodule.zero_mem _)`.
-/
theorem norm_sub_finProj_le_norm (hu : Orthonormal ℂ u) (x : H) : ‖x - finProj u x‖ ≤ ‖x‖ := by
  simpa using norm_sub_finProj_le hu x (Submodule.zero_mem _)

/- English proof (translation)
Establish `h : (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) = fun β => ∑ i, ⟪u i, b β⟫_ℂ * ⟪b β, S (u i)⟫_ℂ`. Use extensionality with `β`. Rewrite using `[finProj_apply, map_sum, inner_sum]`. Simplify using `only [map_smul, inner_smul_right]`. Rewrite using `[h]`.

Conclude with `hasSum_sum fun i _ => b.hasSum_inner_mul_inner (u i) (S (u i))`.
-/
theorem hasSum_inner_comp_finProj (u : ι → H) (S : H →L[ℂ] H) {κ : Type*}
    (b : HilbertBasis κ ℂ H) :
    HasSum (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) (∑ i, ⟪u i, S (u i)⟫_ℂ) := by
  have h : (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) =
      fun β => ∑ i, ⟪u i, b β⟫_ℂ * ⟪b β, S (u i)⟫_ℂ := by
    ext β
    rw [finProj_apply, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right]
  rw [h]
  exact hasSum_sum fun i _ => b.hasSum_inner_mul_inner (u i) (S (u i))

/- English proof (translation)
The claim follows from `(hasSum_inner_comp_finProj u S (stdHilbertBasis ℂ H)).tsum_eq`.
-/
theorem trace_comp_finProj [CompleteSpace H] (u : ι → H) (S : H →L[ℂ] H) :
    trace (S.comp (finProj u)) = ∑ i, ⟪u i, S (u i)⟫_ℂ :=
  (hasSum_inner_comp_finProj u S (stdHilbertBasis ℂ H)).tsum_eq

end FinProj

section Limits

variable [CompleteSpace H]

/- English proof (translation)
Take `⟨A, B, hA, hB, rfl⟩` from `hT.exists_comp`. Use `set Q : α → H →L[ℂ] H := fun a => ContinuousLinearMap.id ℂ H - P a with hQ`. Establish `hdiff : ∀ a, trace (A.comp B) - trace ((A.comp B).comp (P a)) = trace (((Q a).comp A).comp B)`. Introduce `a`. Establish `hsplit : A.comp B = (A.comp B).comp (P a) + (A.comp B).comp (Q a)`.

Rewrite using `[← comp_add]`. Simplify using `[hQ]`. Establish `h1 : trace (A.comp B) = trace ((A.comp B).comp (P a)) + trace ((A.comp B).comp (Q a))` using `by conv_lhs => rw [hsplit]`. Conclude with `trace_add (hT.comp_right _) (hT.comp_right _)`. Rewrite using `[h1, add_sub_cancel_left, ← trace_comp_comm hT (Q a), comp_assoc]`.

Set `b` to `stdHilbertBasis ℂ H`. Establish `hQA : ∀ a, IsHilbertSchmidt ((Q a).comp A)` using `fun a => hA.comp_left _`. Establish `hsq : ∀ a, hsNorm ((Q a).comp A) ^ 2 = ∑' e, ‖A (b e) - P a (A (b e))‖ ^ 2`. Introduce `a`. Rewrite using `[((hQA a).hasSum_norm_sq b).tsum_eq.symm]`.

Both sides reduce to the same expression. Establish `hlim2 : Tendsto (fun a => hsNorm ((Q a).comp A) ^ 2) F (𝓝 0)`. Repeatedly rewrite using `[hsq]`. Establish `h` using `tendsto_tsum_of_dominated_convergence (𝓕 := F) (f := fun a e => ‖A (b e) - P a (A (b e))‖ ^ 2) (g := fun _ => (0 : ℝ)) (bound := fun e => ‖A (b e)‖ ^ 2) (hA.hasSum_norm_sq b).summable ?_ ?_`. Simplify using `using h`.

Introduce `e`. Use `((tendsto_const_nhds (x := A (b e))).sub (hP (A (b e)))).norm.pow 2` as an intermediate fact. Simplify using `using this`. Use `Eventually.of_forall fun a e => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hP1 a _) 2`. Establish `hlim : Tendsto (fun a => hsNorm ((Q a).comp A)) F (𝓝 0)`. Establish `h` using `(Real.continuous_sqrt.tendsto 0).comp hlim2`. Simplify using `only [Real.sqrt_zero] at h`. Use `h.congr fun a => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply]`. Conclude with `Real.sqrt_sq (hsNorm_nonneg _)`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hbound : ∀ a, ‖trace ((A.comp B).comp (P a)) - trace (A.comp B)‖ ≤ hsNorm ((Q a).comp A) * hsNorm B`. Introduce `a`.

Rewrite using `[norm_sub_rev, hdiff a]`. Establish `hfin : traceNorm (((Q a).comp A).comp B) ≠ ∞` using `(isTraceClass_comp (hQA a) hB).ne`. Establish `h1 : ‖trace (((Q a).comp A).comp B)‖ ≤ (traceNorm (((Q a).comp A).comp B)).toReal`. Rewrite using `[← toReal_enorm]`. Conclude with `ENNReal.toReal_mono hfin (enorm_trace_le _)`.

Conclude with `h1.trans (traceNorm_comp_le (hQA a) hB)`. Use `squeeze_zero (fun a => norm_nonneg _) hbound ?_` and prove the remaining obligations. Simplify using `using hlim.mul_const (hsNorm B)`.
-/
theorem tendsto_trace_comp {α : Type*} {F : Filter α} {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (P : α → H →L[ℂ] H) (hP1 : ∀ a x, ‖x - P a x‖ ≤ ‖x‖)
    (hP : ∀ x, Tendsto (fun a => P a x) F (𝓝 x)) :
    Tendsto (fun a => trace (T.comp (P a))) F (𝓝 (trace T)) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  set Q : α → H →L[ℂ] H := fun a => ContinuousLinearMap.id ℂ H - P a with hQ

  have hdiff : ∀ a, trace (A.comp B) - trace ((A.comp B).comp (P a)) =
      trace (((Q a).comp A).comp B) := by
    intro a
    have hsplit : A.comp B = (A.comp B).comp (P a) + (A.comp B).comp (Q a) := by
      rw [← comp_add]; simp [hQ]
    have h1 : trace (A.comp B) =
        trace ((A.comp B).comp (P a)) + trace ((A.comp B).comp (Q a)) := by
      conv_lhs => rw [hsplit]
      exact trace_add (hT.comp_right _) (hT.comp_right _)
    rw [h1, add_sub_cancel_left, ← trace_comp_comm hT (Q a), comp_assoc]

  let b := stdHilbertBasis ℂ H
  have hQA : ∀ a, IsHilbertSchmidt ((Q a).comp A) := fun a => hA.comp_left _
  have hsq : ∀ a, hsNorm ((Q a).comp A) ^ 2 = ∑' e, ‖A (b e) - P a (A (b e))‖ ^ 2 := by
    intro a
    rw [((hQA a).hasSum_norm_sq b).tsum_eq.symm]
    rfl
  have hlim2 : Tendsto (fun a => hsNorm ((Q a).comp A) ^ 2) F (𝓝 0) := by
    simp_rw [hsq]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := F)
      (f := fun a e => ‖A (b e) - P a (A (b e))‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun e => ‖A (b e)‖ ^ 2) (hA.hasSum_norm_sq b).summable ?_ ?_
    · simpa using h
    · intro e
      have := ((tendsto_const_nhds (x := A (b e))).sub (hP (A (b e)))).norm.pow 2
      simpa using this
    · refine Eventually.of_forall fun a e => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP1 a _) 2
  have hlim : Tendsto (fun a => hsNorm ((Q a).comp A)) F (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim2
    simp only [Real.sqrt_zero] at h
    refine h.congr fun a => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (hsNorm_nonneg _)

  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ a, ‖trace ((A.comp B).comp (P a)) - trace (A.comp B)‖ ≤
      hsNorm ((Q a).comp A) * hsNorm B := by
    intro a
    rw [norm_sub_rev, hdiff a]
    have hfin : traceNorm (((Q a).comp A).comp B) ≠ ∞ := (isTraceClass_comp (hQA a) hB).ne
    have h1 : ‖trace (((Q a).comp A).comp B)‖ ≤ (traceNorm (((Q a).comp A).comp B)).toReal := by
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hfin (enorm_trace_le _)
    exact h1.trans (traceNorm_comp_le (hQA a) hB)
  refine squeeze_zero (fun a => norm_nonneg _) hbound ?_
  simpa using hlim.mul_const (hsNorm B)

end Limits

end

end GroundTheory.Automorphic
