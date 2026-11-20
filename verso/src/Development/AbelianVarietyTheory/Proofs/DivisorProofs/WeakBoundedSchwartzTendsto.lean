import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivApply
open Filter Topology

namespace GlobalTheory

namespace SchwartzWeakSeq

/- English proof (translation)
Set `e` to `(Module.finBasis ℂ G).equivFunL`. Establish `he : Tendsto (fun j => e (a j)) atTop (𝓝 (e a₀))`. Rewrite using `[tendsto_pi_nhds]`. Introduce `i`. Conclude with `h ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)`.

Establish `h3` using `(e.symm.continuous.tendsto _).comp he`. Simplify `h3` using `[Function.comp_def]`.
-/
theorem tendsto_of_forall_clm {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {a : ℕ → G} {a₀ : G}
    (h : ∀ φ : G →L[ℂ] ℂ, Tendsto (fun j => φ (a j)) atTop (𝓝 (φ a₀))) :
    Tendsto a atTop (𝓝 a₀) := by
  let e := (Module.finBasis ℂ G).equivFunL
  have he : Tendsto (fun j => e (a j)) atTop (𝓝 (e a₀)) := by
    rw [tendsto_pi_nhds]
    intro i
    exact h ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
  have h3 := (e.symm.continuous.tendsto _).comp he
  simpa [Function.comp_def] using h3

/- English proof (translation)
Establish `h1 : Module.Finite ℝ (MultilinearMap ℝ (fun _ : Fin n => V) ℂ)` using `inferInstance`. Establish `h2 : Module.Finite ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ)` using `Module.Finite.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ)) ContinuousMultilinearMap.toMultilinearMap_injective`. Conclude with `Module.Finite.of_restrictScalars_finite ℝ ℂ _`.
-/
theorem finiteDimensional_multilinear {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) :
    FiniteDimensional ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ) := by
  have h1 : Module.Finite ℝ (MultilinearMap ℝ (fun _ : Fin n => V) ℂ) := inferInstance
  have h2 : Module.Finite ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ) :=
    Module.Finite.of_injective
      (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
      ContinuousMultilinearMap.toMultilinearMap_injective
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

/- English proof (translation)
Establish `hd : Differentiable ℝ (iteratedFDeriv ℝ n g)` using `(g.smooth (n + 1)).differentiable_iteratedFDeriv (by norm_cast; omega)`. Establish `hb : ∀ z ∈ (Set.univ : Set V), ‖fderiv ℝ (iteratedFDeriv ℝ n g) z‖ ≤ SchwartzMap.seminorm ℂ 0 (n + 1) g`. Introduce `z _`. Rewrite using `[norm_fderiv_iteratedFDeriv]`. Conclude with `g.norm_iteratedFDeriv_le_seminorm ℂ (n + 1) z`.

Conclude with `convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z) hb (Set.mem_univ y) (Set.mem_univ x)`.
-/
theorem norm_iteratedFDeriv_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SchwartzMap V ℂ) (n : ℕ) (x y : V) :
    ‖iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y‖ ≤
      SchwartzMap.seminorm ℂ 0 (n + 1) g * ‖x - y‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    (g.smooth (n + 1)).differentiable_iteratedFDeriv (by norm_cast; omega)
  have hb : ∀ z ∈ (Set.univ : Set V),
      ‖fderiv ℝ (iteratedFDeriv ℝ n g) z‖ ≤ SchwartzMap.seminorm ℂ 0 (n + 1) g := by
    intro z _
    rw [norm_fderiv_iteratedFDeriv]
    exact g.norm_iteratedFDeriv_le_seminorm ℂ (n + 1) z
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z) hb
    (Set.mem_univ y) (Set.mem_univ x)

/- English proof (translation)
Use `set δ := ε / (2 * (L + 1)) with hδdef`. Establish `hδ : 0 < δ` using `by positivity`. Take `⟨t, ht, hcov⟩` from `Metric.totallyBounded_iff.1 hK.totallyBounded δ hδ`. Establish `hev : ∀ᶠ j in atTop, ∀ c ∈ t, ‖h j c‖ < ε / 2`. Rewrite using `[Filter.eventually_all_finite ht]`.

Introduce `c _`. Conclude with `(tendsto_zero_iff_norm_tendsto_zero.1 (hp c)).eventually (gt_mem_nhds (by linarith))`. Use `filter_upwards [hev] with j hj x hx`. Take `⟨c, hc, hxc⟩` from `Set.mem_iUnion₂.1 (hcov hx)`. Establish `h1` using `hL j x c`.

Establish `h2 : ‖x - c‖ < δ` using `by rwa [Metric.mem_ball, dist_eq_norm] at hxc`. Establish `h3 : L * ‖x - c‖ ≤ (L + 1) * δ` using `by nlinarith [norm_nonneg (x - c)]`. Apply the tactic sequence `have h4 : (L + 1) * δ = ε / 2 := by rw [hδdef]; field_simp; try ring`. Establish `h5` using `norm_sub_norm_le (h j x) (h j c)`. Establish `h6` using `hj c hc`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eventually_norm_lt_on_compact {V G : Type} [NormedAddCommGroup V] [NormedAddCommGroup G]
    (h : ℕ → V → G) (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ j x y, ‖h j x - h j y‖ ≤ L * ‖x - y‖)
    (hp : ∀ x, Tendsto (fun j => h j x) atTop (𝓝 0)) (K : Set V) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ j in atTop, ∀ x ∈ K, ‖h j x‖ < ε := by
  set δ := ε / (2 * (L + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded δ hδ
  have hev : ∀ᶠ j in atTop, ∀ c ∈ t, ‖h j c‖ < ε / 2 := by
    rw [Filter.eventually_all_finite ht]
    intro c _
    exact (tendsto_zero_iff_norm_tendsto_zero.1 (hp c)).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hev] with j hj x hx
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (hcov hx)
  have h1 := hL j x c
  have h2 : ‖x - c‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hxc
  have h3 : L * ‖x - c‖ ≤ (L + 1) * δ := by nlinarith [norm_nonneg (x - c)]
  have h4 : (L + 1) * δ = ε / 2 := by rw [hδdef]; field_simp; try ring
  have h5 := norm_sub_norm_le (h j x) (h j c)
  have h6 := hj c hc
  linarith

end SchwartzWeakSeq

open SchwartzWeakSeq in

/- English proof (translation)
Rewrite using `[(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]`. Introduce and unpack `⟨k, n⟩ ε hε`. Use `haveI := finiteDimensional_multilinear (V := V) n`. Use `haveI : ProperSpace V := FiniteDimensional.proper_real V`. Establish `hpt : ∀ x, Tendsto (fun j => iteratedFDeriv ℝ n (⇑(f j - f₀)) x) atTop (𝓝 0)`.

Introduce `x`. Establish `h1 : Tendsto (fun j => SchwInt.iterEvalCLM n x (f j)) atTop (𝓝 (SchwInt.iterEvalCLM n x f₀))` using `tendsto_of_forall_clm fun φ => hw (φ.comp (SchwInt.iterEvalCLM n x))`. Establish `h2` using `h1.sub_const (SchwInt.iterEvalCLM n x f₀)`. Establish `he : ∀ j, iteratedFDeriv ℝ n (⇑(f j - f₀)) x = SchwInt.iterEvalCLM n x (f j) - SchwInt.iterEvalCLM n x f₀` using `fun j => by`. Rewrite using `[← map_sub]`.

Both sides reduce to the same expression. Repeatedly rewrite using `[he]`. Simplify using `using h2`. Take `⟨B1, hB1⟩` from `hb (k + 1) n`. Take `⟨B2, hB2⟩` from `hb 0 (n + 1)`.

Use `set M := B1 + SchwartzMap.seminorm ℂ (k + 1) n f₀ with hMdef`. Use `set L := B2 + SchwartzMap.seminorm ℂ 0 (n + 1) f₀ with hLdef`. Establish `hM : ∀ j, SchwartzMap.seminorm ℂ (k + 1) n (f j - f₀) ≤ M` using `fun j => (map_sub_le_add _ _ _).trans (by linarith [(hB1 ⟨j, rfl⟩ : SchwartzMap.seminorm ℂ (k + 1) n (f j) ≤ B1)])`. Establish `hL : ∀ j, SchwartzMap.seminorm ℂ 0 (n + 1) (f j - f₀) ≤ L` using `fun j => (map_sub_le_add _ _ _).trans (by linarith [(hB2 ⟨j, rfl⟩ : SchwartzMap.seminorm ℂ 0 (n + 1) (f j) ≤ B2)])`. Establish `hM0 : 0 ≤ M` using `(apply_nonneg _ _).trans (hM 0)`.

Establish `hL0 : 0 ≤ L` using `(apply_nonneg _ _).trans (hL 0)`. Use `set R := 2 * M / ε + 1 with hRdef`. Establish `hR : 0 < R` using `by positivity`. Establish `hMR : M < ε / 2 * R`. Apply the tactic sequence `have : ε / 2 * R = M + ε / 2 := by rw [hRdef]; field_simp; try ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLip : ∀ j x y, ‖iteratedFDeriv ℝ n (⇑(f j - f₀)) x - iteratedFDeriv ℝ n (⇑(f j - f₀)) y‖ ≤ L * ‖x - y‖` using `fun j x y => (norm_iteratedFDeriv_sub_le _ n x y).trans (mul_le_mul_of_nonneg_right (hL j) (norm_nonneg _))`. Use `set δ := ε / (2 * (R ^ k + 1)) with hδdef`. Establish `hδ : 0 < δ` using `by positivity`. Establish `hunif` using `eventually_norm_lt_on_compact (fun j => iteratedFDeriv ℝ n (⇑(f j - f₀))) L hL0 hLip hpt (Metric.closedBall 0 R) (isCompact_closedBall 0 R) δ hδ`.

Use `filter_upwards [hunif] with j hj`. Establish `hle : SchwartzMap.seminorm ℂ k n (f j - f₀) ≤ ε / 2`. Use `SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : ‖x‖ ≤ R`. Establish `h1` using `hj x (by simpa using hx)`.

Establish `hRk : 0 ≤ R ^ k` using `by positivity`. Establish `h2 : ‖x‖ ^ k ≤ R ^ k` using `pow_le_pow_left₀ (norm_nonneg _) hx k`. Apply the tactic sequence `have h3 : (R ^ k + 1) * δ = ε / 2 := by rw [hδdef]; field_simp; try ring`. Combine the equalities or inequalities in the displayed calculation. Use `push_neg at hx`.

Establish `h1` using `SchwartzMap.le_seminorm ℂ (k + 1) n (f j - f₀) x`. Establish `h2 : ‖x‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(f j - f₀)) x‖) ≤ M`. Rewrite using `[← mul_assoc, ← pow_succ']`. Conclude with `h1.trans (hM j)`. Establish `ha : 0 ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(f j - f₀)) x‖` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `hle.trans_lt (half_lt_self hε)`.
-/
theorem schwartz_tendsto_of_weak_of_bdd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f : ℕ → SchwartzMap V ℂ) (f₀ : SchwartzMap V ℂ)
    (hw : ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Tendsto (fun j => T (f j)) atTop (𝓝 (T f₀)))
    (hb : ∀ k n : ℕ, BddAbove (Set.range fun j => SchwartzMap.seminorm ℂ k n (f j))) :
    Tendsto f atTop (𝓝 f₀) := by
  rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  haveI := finiteDimensional_multilinear (V := V) n
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hpt : ∀ x, Tendsto (fun j => iteratedFDeriv ℝ n (⇑(f j - f₀)) x) atTop (𝓝 0) := by
    intro x
    have h1 : Tendsto (fun j => SchwInt.iterEvalCLM n x (f j)) atTop
        (𝓝 (SchwInt.iterEvalCLM n x f₀)) :=
      tendsto_of_forall_clm fun φ => hw (φ.comp (SchwInt.iterEvalCLM n x))
    have h2 := h1.sub_const (SchwInt.iterEvalCLM n x f₀)
    have he : ∀ j, iteratedFDeriv ℝ n (⇑(f j - f₀)) x =
        SchwInt.iterEvalCLM n x (f j) - SchwInt.iterEvalCLM n x f₀ := fun j => by
      rw [← map_sub]; rfl
    simp_rw [he]
    simpa using h2
  obtain ⟨B1, hB1⟩ := hb (k + 1) n
  obtain ⟨B2, hB2⟩ := hb 0 (n + 1)
  set M := B1 + SchwartzMap.seminorm ℂ (k + 1) n f₀ with hMdef
  set L := B2 + SchwartzMap.seminorm ℂ 0 (n + 1) f₀ with hLdef
  have hM : ∀ j, SchwartzMap.seminorm ℂ (k + 1) n (f j - f₀) ≤ M := fun j =>
    (map_sub_le_add _ _ _).trans (by linarith [(hB1 ⟨j, rfl⟩ : SchwartzMap.seminorm ℂ (k + 1) n (f j) ≤ B1)])
  have hL : ∀ j, SchwartzMap.seminorm ℂ 0 (n + 1) (f j - f₀) ≤ L := fun j =>
    (map_sub_le_add _ _ _).trans (by linarith [(hB2 ⟨j, rfl⟩ : SchwartzMap.seminorm ℂ 0 (n + 1) (f j) ≤ B2)])
  have hM0 : 0 ≤ M := (apply_nonneg _ _).trans (hM 0)
  have hL0 : 0 ≤ L := (apply_nonneg _ _).trans (hL 0)
  set R := 2 * M / ε + 1 with hRdef
  have hR : 0 < R := by positivity
  have hMR : M < ε / 2 * R := by
    have : ε / 2 * R = M + ε / 2 := by rw [hRdef]; field_simp; try ring
    linarith
  have hLip : ∀ j x y, ‖iteratedFDeriv ℝ n (⇑(f j - f₀)) x - iteratedFDeriv ℝ n (⇑(f j - f₀)) y‖
      ≤ L * ‖x - y‖ := fun j x y =>
    (norm_iteratedFDeriv_sub_le _ n x y).trans (mul_le_mul_of_nonneg_right (hL j) (norm_nonneg _))
  set δ := ε / (2 * (R ^ k + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hunif := eventually_norm_lt_on_compact (fun j => iteratedFDeriv ℝ n (⇑(f j - f₀))) L hL0
    hLip hpt (Metric.closedBall 0 R) (isCompact_closedBall 0 R) δ hδ
  filter_upwards [hunif] with j hj
  have hle : SchwartzMap.seminorm ℂ k n (f j - f₀) ≤ ε / 2 := by
    refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
    by_cases hx : ‖x‖ ≤ R
    · have h1 := hj x (by simpa using hx)
      have hRk : 0 ≤ R ^ k := by positivity
      have h2 : ‖x‖ ^ k ≤ R ^ k := pow_le_pow_left₀ (norm_nonneg _) hx k
      have h3 : (R ^ k + 1) * δ = ε / 2 := by rw [hδdef]; field_simp; try ring
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(f j - f₀)) x‖ ≤ R ^ k * δ :=
            mul_le_mul h2 h1.le (norm_nonneg _) hRk
        _ ≤ (R ^ k + 1) * δ := by nlinarith
        _ = ε / 2 := h3
    · push_neg at hx
      have h1 := SchwartzMap.le_seminorm ℂ (k + 1) n (f j - f₀) x
      have h2 : ‖x‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(f j - f₀)) x‖) ≤ M := by
        rw [← mul_assoc, ← pow_succ']; exact h1.trans (hM j)
      have ha : 0 ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(f j - f₀)) x‖ := by positivity
      nlinarith
  exact hle.trans_lt (half_lt_self hε)

end GlobalTheory
