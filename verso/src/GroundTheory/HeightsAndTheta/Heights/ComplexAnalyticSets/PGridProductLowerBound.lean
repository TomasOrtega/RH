import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGridProductLowerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology MvPolynomial

/- English proof (translation)
Use `set P : MvPolynomial σ ℂ := ∏ m, ∑ i, X i * C (v m i) with hP`. Establish `hlin : ∀ m, ∑ i, X i * C (v m i) ≠ (0 : MvPolynomial σ ℂ)`. Introduce `m h`. Take `⟨i, hi⟩` from `Function.ne_iff.1 (hv m)`. Use `congrArg (eval (Pi.single i 1)) h` as an intermediate fact.

Simplify using `[Pi.single_apply] at this`. Conclude with `hi this`. Establish `hP0 : P ≠ 0` using `Finset.prod_ne_zero_iff.2 fun m _ => hlin m`. Set `S : σ → Finset ℂ` to `fun _ => Finset.univ.image fun j : Fin (N + 1) => ((j : ℕ) : ℂ)`. Establish `hS : ∀ i, (S i).card = N + 1` using `fun i => by`.

Simplify using `only [S]`. Rewrite using `[Finset.card_image_of_injective _ fun a b h => Fin.ext (by exact_mod_cast h)]`. Simplify using the standard rewrite rules. Establish `htot : P.totalDegree ≤ k`. Use `(totalDegree_finsetProd _ _).trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hdeg : ∀ i, P.degreeOf i < (S i).card` using `fun i => by`. Rewrite using `[hS i]`. Conclude with `Nat.lt_succ_of_le (((degreeOf_le_totalDegree _ _).trans htot).trans hk)`. Assume the negation of the conclusion as `hne`.

Use `push Not at hne`. Use `hP0 (eq_zero_of_eval_zero_at_prod_finset P S hdeg fun x hx => ?_)` and prove the remaining obligations. Use `choose u _ hu using fun i => Finset.mem_image.1 (hx i)`. Use `hne u` as an intermediate fact. Simplify using `only [hu] at this`.

Simplify `this` using `[hP, map_prod]`.
-/
theorem GridProductLowerBound.exists_grid_prod_ne_zero {σ : Type} [Fintype σ] {N k : ℕ} (hk : k ≤ N)
    (v : Fin k → σ → ℂ) (hv : ∀ m, v m ≠ 0) :
    ∃ u : σ → Fin (N + 1), ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i ≠ 0 := by
  classical
  set P : MvPolynomial σ ℂ := ∏ m, ∑ i, X i * C (v m i) with hP
  have hlin : ∀ m, ∑ i, X i * C (v m i) ≠ (0 : MvPolynomial σ ℂ) := by
    intro m h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (hv m)
    have := congrArg (eval (Pi.single i 1)) h
    simp [Pi.single_apply] at this
    exact hi this
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun m _ => hlin m
  let S : σ → Finset ℂ := fun _ => Finset.univ.image fun j : Fin (N + 1) => ((j : ℕ) : ℂ)
  have hS : ∀ i, (S i).card = N + 1 := fun i => by
    simp only [S]
    rw [Finset.card_image_of_injective _ fun a b h => Fin.ext (by exact_mod_cast h)]
    simp
  have htot : P.totalDegree ≤ k := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ m, (∑ i, X i * C (v m i) : MvPolynomial σ ℂ).totalDegree ≤ ∑ _m : Fin k, 1 :=
          Finset.sum_le_sum fun m _ => totalDegree_finsetSum_le fun j _ =>
            (totalDegree_mul _ _).trans (by simp [totalDegree_X, totalDegree_C])
      _ = k := by simp
  have hdeg : ∀ i, P.degreeOf i < (S i).card := fun i => by
    rw [hS i]
    exact Nat.lt_succ_of_le (((degreeOf_le_totalDegree _ _).trans htot).trans hk)
  by_contra hne
  push Not at hne
  refine hP0 (eq_zero_of_eval_zero_at_prod_finset P S hdeg fun x hx => ?_)
  choose u _ hu using fun i => Finset.mem_image.1 (hx i)
  have := hne u
  simp only [hu] at this
  simpa [hP, map_prod] using this

/- English proof (translation)
Introduce `σ _ N Z z₀ hZ hz₀`. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, hεZ⟩ : ∃ ε > 0, ∀ x ∈ Z, ε ≤ dist z₀ x := by`. Rewrite `hz₀` using `[Metric.mem_closure_iff]`. Use `push Not at hz₀`. Conclude with `hz₀`.

Take `⟨R, hR⟩` from `hZ.subset_closedBall z₀`. Use `set K : Set (σ → ℂ) := Metric.closedBall 0 (R + ε / 2) \ Metric.ball 0 (ε / 2) with hK`. Establish `hKc : IsCompact K` using `(isCompact_closedBall _ _).diff Metric.isOpen_ball`. Establish `hK0 : ∀ w ∈ K, w ≠ 0`. Introduce and unpack `w hw rfl`.

Simplify using `[hK, hε] at hw`. Set `g : (k : ℕ) → (Fin k → σ → ℂ) → ℝ` to `fun k v => Finset.univ.sup' Finset.univ_nonempty fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖`. Establish `hbd : ∀ k, ∃ μ > (0 : ℝ), k ≤ N → ∀ v ∈ Set.univ.pi (fun _ : Fin k => K), μ ≤ g k v`. Introduce `k`. Distinguish the cases in `hk : k ≤ N`.

Break down `(Set.univ.pi fun _ : Fin k => K).eq_empty_or_nonempty with he | hne` into its components or cases. Conclude with `⟨1, one_pos, fun _ v hv => by simp [he] at hv⟩`. Establish `hgc : Continuous (g k)` using `Continuous.finset_sup'_apply (f := fun (u : σ → Fin (N + 1)) (v : Fin k → σ → ℂ) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖) _ fun u _ => continuous_norm.comp (continuous_finsetProd _ fun m _ => continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp (contin …`. Take `⟨v₀, hv₀, hmin⟩` from `(isCompact_univ_pi fun _ => hKc).exists_isMinOn hne hgc.continuousOn`. Take `⟨u, hu⟩` from `GridProductLowerBound.exists_grid_prod_ne_zero hk v₀ fun m => hK0 _ (hv₀ m (Set.mem_univ _))`.

Conclude with `⟨g k v₀, (norm_pos_iff.2 hu).trans_le (Finset.le_sup' (fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v₀ m i‖) (Finset.mem_univ u)), fun _ v hv => isMinOn_iff.1 hmin v hv⟩`. Conclude with `⟨1, one_pos, fun h => absurd h hk⟩`. Use `choose μf hμf0 hμf using hbd`. Use `⟨(Finset.range (N + 1)).inf' ⟨0, Finset.mem_range.2 N.succ_pos⟩ μf, (Finset.lt_inf'_iff _).2 fun k _ => hμf0 k, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩` and prove the remaining obligations. Introduce `z hz s hs hcard`.

Use `set e := s.equivFin`. Use `set v : Fin s.card → σ → ℂ := fun m => z - (e.symm m : σ → ℂ) with hvdef`. Establish `hv : v ∈ Set.univ.pi fun _ : Fin s.card => K`. Introduce `m _`. Establish `hx` using `hs (e.symm m).2`.

Establish `h1` using `hεZ _ hx`. Establish `h2` using `Metric.mem_closedBall.1 (hR hx)`. Establish `h3` using `Metric.mem_ball.1 hz`. Establish `h4` using `dist_triangle z₀ z (e.symm m : σ → ℂ)`. Establish `h5` using `dist_triangle z z₀ (e.symm m : σ → ℂ)`.

Rewrite `h4` using `[dist_comm z₀ z]`. Rewrite `h2` using `[dist_comm]`. Simplify using `only [hK, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, hvdef, ← dist_eq_norm, not_lt]`. Apply the tactic sequence `constructor <;> linarith`. Take `⟨u, -, hu⟩` from `Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖)`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `hprod : ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) = ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i`. Rewrite using `[← Finset.prod_coe_sort, ← e.symm.prod_comp]`. Both sides reduce to the same expression. Rewrite using `[hprod]`.

Establish `hle` using `(Finset.inf'_le μf (Finset.mem_range_succ_iff.2 hcard)).trans (hμf _ hcard v hv)`. Simplify using `only [g] at hle`. Rewrite `hle` using `[hu]`. Then use the resulting hypothesis.
-/
theorem GridProductLowerBound.proof : GridProductLowerBound.Statement := by
  classical
  intro σ _ N Z z₀ hZ hz₀
  obtain ⟨ε, hε, hεZ⟩ : ∃ ε > 0, ∀ x ∈ Z, ε ≤ dist z₀ x := by
    rw [Metric.mem_closure_iff] at hz₀
    push Not at hz₀
    exact hz₀
  obtain ⟨R, hR⟩ := hZ.subset_closedBall z₀
  set K : Set (σ → ℂ) := Metric.closedBall 0 (R + ε / 2) \ Metric.ball 0 (ε / 2) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hK0 : ∀ w ∈ K, w ≠ 0 := by
    rintro w hw rfl
    simp [hK, hε] at hw
  let g : (k : ℕ) → (Fin k → σ → ℂ) → ℝ := fun k v =>
    Finset.univ.sup' Finset.univ_nonempty fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖
  have hbd : ∀ k, ∃ μ > (0 : ℝ), k ≤ N → ∀ v ∈ Set.univ.pi (fun _ : Fin k => K), μ ≤ g k v := by
    intro k
    by_cases hk : k ≤ N
    · rcases (Set.univ.pi fun _ : Fin k => K).eq_empty_or_nonempty with he | hne
      · exact ⟨1, one_pos, fun _ v hv => by simp [he] at hv⟩
      have hgc : Continuous (g k) := Continuous.finset_sup'_apply
        (f := fun (u : σ → Fin (N + 1)) (v : Fin k → σ → ℂ) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖) _
        fun u _ => continuous_norm.comp (continuous_finsetProd _ fun m _ => continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((continuous_apply i).comp (continuous_apply m)))
      obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_univ_pi fun _ => hKc).exists_isMinOn hne hgc.continuousOn
      obtain ⟨u, hu⟩ := GridProductLowerBound.exists_grid_prod_ne_zero hk v₀
        fun m => hK0 _ (hv₀ m (Set.mem_univ _))
      exact ⟨g k v₀, (norm_pos_iff.2 hu).trans_le (Finset.le_sup' (fun u : σ → Fin (N + 1) =>
        ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v₀ m i‖) (Finset.mem_univ u)), fun _ v hv => isMinOn_iff.1 hmin v hv⟩
    · exact ⟨1, one_pos, fun h => absurd h hk⟩
  choose μf hμf0 hμf using hbd
  refine ⟨(Finset.range (N + 1)).inf' ⟨0, Finset.mem_range.2 N.succ_pos⟩ μf,
    (Finset.lt_inf'_iff _).2 fun k _ => hμf0 k, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  intro z hz s hs hcard
  set e := s.equivFin
  set v : Fin s.card → σ → ℂ := fun m => z - (e.symm m : σ → ℂ) with hvdef
  have hv : v ∈ Set.univ.pi fun _ : Fin s.card => K := by
    intro m _
    have hx := hs (e.symm m).2
    have h1 := hεZ _ hx
    have h2 := Metric.mem_closedBall.1 (hR hx)
    have h3 := Metric.mem_ball.1 hz
    have h4 := dist_triangle z₀ z (e.symm m : σ → ℂ)
    have h5 := dist_triangle z z₀ (e.symm m : σ → ℂ)
    rw [dist_comm z₀ z] at h4
    rw [dist_comm] at h2
    simp only [hK, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, hvdef, ← dist_eq_norm,
      not_lt]
    constructor <;> linarith
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖)
  refine ⟨u, ?_⟩
  have hprod : ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) = ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i := by
    rw [← Finset.prod_coe_sort, ← e.symm.prod_comp]
    rfl
  rw [hprod]
  have hle := (Finset.inf'_le μf (Finset.mem_range_succ_iff.2 hcard)).trans (hμf _ hcard v hv)
  simp only [g] at hle
  rwa [hu] at hle

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
