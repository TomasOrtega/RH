import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

noncomputable section
namespace GlobalTheory.Chamber.NonProp

variable {k : ℕ}

/- English proof (translation)
The claim follows from `Submodule.sub_starProjection_mem_orthogonal _`.
-/
theorem wt_mem_orth (T : Finset (SV k)) (u : SV k) : wt T u ∈ (aP T)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

/- English proof (translation)
The claim follows from `Submodule.inner_left_of_mem_orthogonal hx (wt_mem_orth T u)`.
-/
theorem inner_wt_of_mem {T : Finset (SV k)} (u : SV k) {x : A0 k} (hx : x ∈ aP T) : ⟪wt T u, x⟫_ℝ = 0 :=
  Submodule.inner_left_of_mem_orthogonal hx (wt_mem_orth T u)

/- English proof (translation)
The claim follows from `Submodule.starProjection_apply_mem _ _`.
-/
theorem pr_mem (T : Finset (SV k)) (x : A0 k) : pr T x ∈ aP T := Submodule.starProjection_apply_mem _ _

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨u, hu, rfl⟩`.
-/
theorem vec_mem {T : Finset (SV k)} {u : SV k} (hu : u ∈ T) : vec u ∈ aP T :=
  Submodule.subset_span ⟨u, hu, rfl⟩

/- English proof (translation)
Establish `: vec u = wt T u + pr T (vec u)` using `by simp [wt]`. Use `conv_lhs => rw [this]`. Rewrite using `[inner_add_right, inner_wt_of_mem u (pr_mem T _), add_zero, real_inner_self_eq_norm_sq]`.
-/
theorem inner_wt_vec (T : Finset (SV k)) (u : SV k) : ⟪wt T u, vec u⟫_ℝ = ‖wt T u‖ ^ 2 := by
  have : vec u = wt T u + pr T (vec u) := by simp [wt]
  conv_lhs => rw [this]
  rw [inner_add_right, inner_wt_of_mem u (pr_mem T _), add_zero, real_inner_self_eq_norm_sq]

/- English proof (translation)
The claim follows from `sub_mem (vec_mem hu) (vecSpan_mono (Finset.erase_subset u S) (pr_mem _ _))`.
-/
theorem rt_mem {S : Finset (SV k)} {u : SV k} (hu : u ∈ S) : rt S u ∈ aP S :=
  sub_mem (vec_mem hu) (vecSpan_mono (Finset.erase_subset u S) (pr_mem _ _))

/- English proof (translation)
Introduce `k Q S hQ hSQ`. Establish `hS : IsPar S` using `hQ.mono hSQ`. Establish `rt_ne : ∀ v ∈ S, rt S v ≠ 0` using `fun v hv => hS.wt_ne_zero (Finset.erase_subset v S) (by simp [hv])`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv v' hv' hne r e`.

Establish `h1 : ⟪rt S v', vec v'⟫_ℝ = ‖rt S v'‖ ^ 2` using `inner_wt_vec _ _`. Establish `h2 : ⟪rt S v, vec v'⟫_ℝ = 0` using `inner_wt_of_mem v (vec_mem (Finset.mem_erase.2 ⟨fun h => hne h.symm, hv'⟩))`. Establish `h3 : ⟪rt S v', vec v'⟫_ℝ = 0` using `by rw [e, real_inner_smul_left, h2, mul_zero]`. Rewrite `h1` using `[h3]`. Establish `: 0 < ‖rt S v'‖` using `norm_pos_iff.2 (rt_ne v' hv')`.

Use polynomial arithmetic with `[h1]`. Introduce `v hv v' hv' hne r e`. Rewrite `hv`, `hv'` using `[Finset.mem_sdiff]`. Apply `hQ.vec_notMem hv'.1` to reduce the goal to its premises. Establish `hsub : insert v S ⊆ Q.erase v'`.

Introduce `x hx`. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `Finset.mem_erase.2 ⟨hne, hv.1⟩`. Conclude with `Finset.mem_erase.2 ⟨fun h => hv'.2 (h ▸ hx), hSQ hx⟩`. Apply `vecSpan_mono hsub` to reduce the goal to its premises.

Establish `hv'eq : vec v' = wt S v' + pr S (vec v')` using `by simp [wt]`. Rewrite using `[hv'eq, e]`. Use `add_mem (Submodule.smul_mem _ _ (sub_mem (vec_mem (Finset.mem_insert_self _ _)) ?_)) ?_` and prove the remaining obligations. Conclude with `vecSpan_mono (Finset.subset_insert _ _) (pr_mem _ _)`. Conclude with `vecSpan_mono (Finset.subset_insert _ _) (pr_mem _ _)`.

Introduce `v hv v' hv' r`. Establish `wne : wt S v ≠ 0` using `hQ.wt_ne_zero hSQ hv`. Establish `h0 : ⟪wt S v, rt S v'⟫_ℝ = 0` using `inner_wt_of_mem v (rt_mem hv')`. Use `⟨fun e => rt_ne v' hv' ?_, fun e => wne ?_⟩` and prove the remaining obligations. Use `congrArg (fun x => ⟪x, rt S v'⟫_ℝ) e` as an intermediate fact.

Simplify using `only [real_inner_smul_left, h0, mul_zero] at this`. Conclude with `inner_self_eq_zero.1 this`. Use `congrArg (fun x => ⟪wt S v, x⟫_ℝ) e` as an intermediate fact. Simplify using `only [real_inner_smul_right, h0, mul_zero] at this`. Conclude with `inner_self_eq_zero.1 this`.
-/
theorem nonprop : ∀ {k : ℕ} {Q S : Finset (SV k)}, IsPar Q → S ⊆ Q →
  (∀ v ∈ S, ∀ v' ∈ S, v ≠ v' → ∀ r : ℝ, rt S v' ≠ r • rt S v) ∧
  (∀ v ∈ Q \ S, ∀ v' ∈ Q \ S, v ≠ v' → ∀ r : ℝ, wt S v' ≠ r • wt S v) ∧
  (∀ v ∈ Q \ S, ∀ v' ∈ S, ∀ r : ℝ, rt S v' ≠ r • wt S v ∧ wt S v ≠ r • rt S v') := by
  intro k Q S hQ hSQ
  have hS : IsPar S := hQ.mono hSQ
  have rt_ne : ∀ v ∈ S, rt S v ≠ 0 := fun v hv =>
    hS.wt_ne_zero (Finset.erase_subset v S) (by simp [hv])
  refine ⟨?_, ?_, ?_⟩
  · intro v hv v' hv' hne r e
    have h1 : ⟪rt S v', vec v'⟫_ℝ = ‖rt S v'‖ ^ 2 := inner_wt_vec _ _
    have h2 : ⟪rt S v, vec v'⟫_ℝ = 0 :=
      inner_wt_of_mem v (vec_mem (Finset.mem_erase.2 ⟨fun h => hne h.symm, hv'⟩))
    have h3 : ⟪rt S v', vec v'⟫_ℝ = 0 := by rw [e, real_inner_smul_left, h2, mul_zero]
    rw [h3] at h1
    have : 0 < ‖rt S v'‖ := norm_pos_iff.2 (rt_ne v' hv')
    nlinarith [h1]
  · intro v hv v' hv' hne r e
    rw [Finset.mem_sdiff] at hv hv'
    apply hQ.vec_notMem hv'.1
    have hsub : insert v S ⊆ Q.erase v' := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_erase.2 ⟨hne, hv.1⟩
      · exact Finset.mem_erase.2 ⟨fun h => hv'.2 (h ▸ hx), hSQ hx⟩
    apply vecSpan_mono hsub
    have hv'eq : vec v' = wt S v' + pr S (vec v') := by simp [wt]
    rw [hv'eq, e]
    refine add_mem (Submodule.smul_mem _ _ (sub_mem (vec_mem (Finset.mem_insert_self _ _)) ?_)) ?_
    · exact vecSpan_mono (Finset.subset_insert _ _) (pr_mem _ _)
    · exact vecSpan_mono (Finset.subset_insert _ _) (pr_mem _ _)
  · intro v hv v' hv' r
    have wne : wt S v ≠ 0 := hQ.wt_ne_zero hSQ hv
    have h0 : ⟪wt S v, rt S v'⟫_ℝ = 0 := inner_wt_of_mem v (rt_mem hv')
    refine ⟨fun e => rt_ne v' hv' ?_, fun e => wne ?_⟩
    · have := congrArg (fun x => ⟪x, rt S v'⟫_ℝ) e
      simp only [real_inner_smul_left, h0, mul_zero] at this
      exact inner_self_eq_zero.1 this
    · have := congrArg (fun x => ⟪wt S v, x⟫_ℝ) e
      simp only [real_inner_smul_right, h0, mul_zero] at this
      exact inner_self_eq_zero.1 this

end GlobalTheory.Chamber.NonProp
