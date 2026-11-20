import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

/- English proof (translation)
Establish `hc : ContinuousAt G z₀` using `(hG.differentiableAt (hW.mem_nhds hz₀)).continuousAt`. Establish `hMpos : 0 < ‖G z₀‖ + 1` using `by positivity`. Establish `hb : ∀ᶠ z in 𝓝 z₀, ‖G z‖ < ‖G z₀‖ + 1` using `hc.norm.eventually (gt_mem_nhds (lt_add_one _))`. Distinguish the cases in `h0 : z₀ k = 0`. Take `⟨R, hR, hsub⟩` from `Metric.mem_nhds_iff.1 (Filter.inter_mem (hW.mem_nhds hz₀) hb)`.

Use `⟨(‖G z₀‖ + 1) / R, div_pos hMpos hR, Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hR) fun z hz => ?_⟩` and prove the remaining obligations. Establish `hmap : ∀ w ∈ Metric.ball (0 : ℂ) R, Function.update z k w ∈ Metric.ball z₀ R`. Introduce `w hw`. Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hR]`. Introduce `j`.

Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Rewrite using `[Function.update_self, h0]`. Conclude with `hw`. Rewrite using `[Function.update_of_ne hj]`.

Conclude with `lt_of_le_of_lt (dist_le_pi_dist z z₀ j) hz`. Establish `hupd : Differentiable ℂ (fun w : ℂ => Function.update z k w)`. Use `differentiable_pi.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality.

Simplify using `using differentiable_id`. Simplify `differentiable_const (z j)` using `[Function.update_of_ne hj]`. Establish `hg : DifferentiableOn ℂ (fun w => G (Function.update z k w)) (Metric.ball 0 R)` using `(hG.mono fun u hu => (hsub hu).1).comp hupd.differentiableOn hmap`. Establish `hg0 : G (Function.update z k 0) = 0` using `hv _ (hsub (hmap 0 (Metric.mem_ball_self hR))).1 (Function.update_self ..)`. Establish `hmaps : Set.MapsTo (fun w => G (Function.update z k w)) (Metric.ball 0 R) (Metric.closedBall ((fun w => G (Function.update z k w)) 0) (‖G z₀‖ + 1))`.

Introduce `w hw`. Simplify using `only [hg0, Metric.mem_closedBall, dist_zero_right]`. Conclude with `(hsub (hmap w hw)).2.le`. Establish `hzk : z k ∈ Metric.ball (0 : ℂ) R`. Use `(dist_le_pi_dist z z₀ k).trans_lt hz` as an intermediate fact.

Rewrite `this` using `[h0]`. Conclude with `this`. Use `Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmaps hzk` as an intermediate fact. Simplify using `only [Function.update_eq_self, hg0, dist_zero_right] at this`. Conclude with `this`.

Establish `hk : ∀ᶠ z in 𝓝 z₀, ‖z₀ k‖ / 2 < ‖z k‖` using `((continuous_apply k).norm.continuousAt (x := z₀)).eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.2 h0)))`. Establish `hk0 : 0 < ‖z₀ k‖` using `norm_pos_iff.2 h0`. Use `⟨2 * (‖G z₀‖ + 1) / ‖z₀ k‖, by positivity, (hb.and hk).mono fun z hz => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_norm_le_mul_coord {n : ℕ} {G : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hG : DifferentiableOn ℂ G W) {z₀ : Fin n → ℂ} (hz₀ : z₀ ∈ W) (k : Fin n)
    (hv : ∀ z ∈ W, z k = 0 → G z = 0) : ∃ L : ℝ, 0 < L ∧ ∀ᶠ z in 𝓝 z₀, ‖G z‖ ≤ L * ‖z k‖ := by
  have hc : ContinuousAt G z₀ := (hG.differentiableAt (hW.mem_nhds hz₀)).continuousAt
  have hMpos : 0 < ‖G z₀‖ + 1 := by positivity
  have hb : ∀ᶠ z in 𝓝 z₀, ‖G z‖ < ‖G z₀‖ + 1 := hc.norm.eventually (gt_mem_nhds (lt_add_one _))
  by_cases h0 : z₀ k = 0
  · obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (hW.mem_nhds hz₀) hb)
    refine ⟨(‖G z₀‖ + 1) / R, div_pos hMpos hR,
      Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hR) fun z hz => ?_⟩
    have hmap : ∀ w ∈ Metric.ball (0 : ℂ) R, Function.update z k w ∈ Metric.ball z₀ R := by
      intro w hw
      rw [Metric.mem_ball, dist_pi_lt_iff hR]
      intro j
      by_cases hj : j = k
      · subst hj
        rw [Function.update_self, h0]
        exact hw
      · rw [Function.update_of_ne hj]
        exact lt_of_le_of_lt (dist_le_pi_dist z z₀ j) hz
    have hupd : Differentiable ℂ (fun w : ℂ => Function.update z k w) := by
      refine differentiable_pi.2 fun j => ?_
      by_cases hj : j = k
      · subst hj
        simpa using differentiable_id
      · simpa [Function.update_of_ne hj] using differentiable_const (z j)
    have hg : DifferentiableOn ℂ (fun w => G (Function.update z k w)) (Metric.ball 0 R) :=
      (hG.mono fun u hu => (hsub hu).1).comp hupd.differentiableOn hmap
    have hg0 : G (Function.update z k 0) = 0 :=
      hv _ (hsub (hmap 0 (Metric.mem_ball_self hR))).1 (Function.update_self ..)
    have hmaps : Set.MapsTo (fun w => G (Function.update z k w)) (Metric.ball 0 R)
        (Metric.closedBall ((fun w => G (Function.update z k w)) 0) (‖G z₀‖ + 1)) := by
      intro w hw
      simp only [hg0, Metric.mem_closedBall, dist_zero_right]
      exact (hsub (hmap w hw)).2.le
    have hzk : z k ∈ Metric.ball (0 : ℂ) R := by
      have := (dist_le_pi_dist z z₀ k).trans_lt hz
      rw [h0] at this
      exact this
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmaps hzk
    simp only [Function.update_eq_self, hg0, dist_zero_right] at this
    exact this
  · have hk : ∀ᶠ z in 𝓝 z₀, ‖z₀ k‖ / 2 < ‖z k‖ :=
      ((continuous_apply k).norm.continuousAt (x := z₀)).eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.2 h0)))
    have hk0 : 0 < ‖z₀ k‖ := norm_pos_iff.2 h0
    refine ⟨2 * (‖G z₀‖ + 1) / ‖z₀ k‖, by positivity, (hb.and hk).mono fun z hz => ?_⟩
    calc ‖G z‖ ≤ ‖G z₀‖ + 1 := hz.1.le
      _ = 2 * (‖G z₀‖ + 1) / ‖z₀ k‖ * (‖z₀ k‖ / 2) := by field_simp
      _ ≤ 2 * (‖G z₀‖ + 1) / ‖z₀ k‖ * ‖z k‖ := mul_le_mul_of_nonneg_left hz.2.le (by positivity)

end GlobalTheory.ShFam

namespace GlobalTheory.ShFam

/- English proof (translation)
Introduce `D A N j S κ s x σ n a e hhol hinn y₀ hy₀`. Use `choose V t f hyV ht hf heq using fun i => (x.nrm_div σ i).2 y₀`. Use `set W : Set (Fin n → ℂ) := {z | z ∈ e.target ∧ ∀ i, e.symm z ∈ ptsIn (genStr s.T.Z) σ (V i).1} with hWdef`. Establish `hWo : IsOpen W` using `isOpen_iff_mem_nhds.2 fun z hz => by`. Establish `h1 : ∀ᶠ b in 𝓝 z, ∀ i, b ∈ e.target ∧ ⊤ ≤ (e.symm b).1 ⁻¹ᵁ (V i).1` using `Filter.eventually_all.2 fun i => (hhol (V i).1 (t i)).1.mem_nhds ⟨hz.1, hz.2 i⟩`.

Use `filter_upwards [h1, e.open_target.mem_nhds hz.1] with b hb hb'`. Conclude with `⟨hb', fun i => (hb i).2⟩`. Establish `hGd : DifferentiableOn ℂ (fun z => ∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z)) W`. Establish `h : ∀ i ∈ (Finset.univ : Finset (Fin x.m)), DifferentiableOn ℂ (fun z => ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z)) W` using `fun i _ => (hhol (V i).1 (t i)).2.mono fun z (hz : z ∈ W) => ⟨hz.1, hz.2 i⟩`. Establish `hu : ∀ u : Finset (Fin x.m), DifferentiableOn ℂ (fun z => ∏ i ∈ u, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z)) W`.

Introduce `u`. Proceed by induction on `u using Finset.induction_on with`. Consider the case `empty => simpa using differentiableOn_const (c := (1 : ℂ))`. Consider the case `insert i u hi ih`. Simplify using `only [Finset.prod_insert hi]`.

Conclude with `(h i (Finset.mem_univ i)).mul ih`. Conclude with `hu Finset.univ`. Establish `hz₀ : e y₀ ∈ W` using `⟨e.map_source hy₀, fun i => by rw [e.left_inv hy₀]; exact hyV i⟩`. Establish `hvan : ∀ k : Fin n, (k : ℕ) < a → ∀ z ∈ W, z k = 0 → ∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z) = 0`. Introduce `k hk z hz hzk`.

Establish `hs : e.symm z ∈ e.source` using `e.map_target hz.1`. Establish `hni : ¬ Inner (e.symm z)` using `fun h => (hinn _ hs).1 h k hk (by rw [e.right_inv hz.1]; exact hzk)`. Establish `hb : LiesIn (e.symm z) (genBd s.T.Z)` using `not_not.1 hni`. Take `⟨i, hi⟩` from `(x.liesIn_genBd_iff _).1 hb`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) ((ev_eq_zero_iff (ht i) (hz.2 i)).2 hi)`.

Establish `hL : ∀ k : Fin n, ∃ L : ℝ, 0 < L ∧ ∀ᶠ z in 𝓝 (e y₀), (k : ℕ) < a → ‖∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z)‖ ≤ L * ‖z k‖`. Introduce `k`. Distinguish the cases in `hk : (k : ℕ) < a`. Take `⟨L, hL0, hLe⟩` from `exists_norm_le_mul_coord hWo hGd hz₀ k (hvan k hk)`. Conclude with `⟨L, hL0, hLe.mono fun z hz _ => hz⟩`.

Conclude with `⟨1, one_pos, Filter.Eventually.of_forall fun z h => absurd h hk⟩`. Use `choose L hL0 hLe using hL`. Use `set Lt : ℝ := 1 + ∑ k, L k with hLt`. Establish `hLt0 : 0 < Lt`. Establish `: 0 ≤ ∑ k, L k` using `Finset.sum_nonneg fun k _ => (hL0 k).le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLk : ∀ k, L k ≤ Lt` using `fun k => by`. Use `Finset.single_le_sum (f := L) (fun k _ => (hL0 k).le) (Finset.mem_univ k)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set Q : ℝ := ∏ i, Real.exp (1 - f i y₀) with hQ`.

Establish `hQ0 : 0 < Q` using `Finset.prod_pos fun i _ => Real.exp_pos _`. Use `set K : ℝ := 2 * Real.log Lt + Real.log Q with hK`. Establish `hC : 0 ≤ 1 / 2 + |K| / 2` using `by positivity`. Use `⟨{y | Inner y → ∀ k : Fin n, (k : ℕ) < a → -Real.log ‖e y k‖ ≤ (1 / 2 + |K| / 2) * x.r σ y}, ?_, 1 / 2 + |K| / 2, hC, fun y hy => hy⟩` and prove the remaining obligations. Establish `hbd : ∀ᶠ y in 𝓝 y₀, ∀ k : Fin n, (k : ℕ) < a → ‖∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm (e y))‖ ≤ Lt * ‖e y k‖` using `(e.continuousAt hy₀).eventually (Filter.eventually_all.2 fun k => (hLe k).mono fun z hz hk => (hz hk).trans (mul_le_mul_of_nonneg_right (hLk k) (norm_nonneg _)))`.

Establish `hpts : ∀ᶠ y in 𝓝 y₀, ∀ i, y ∈ ptsIn (genStr s.T.Z) σ (V i).1` using `Filter.eventually_all.2 fun i => (isOpen_ptsIn _).mem_nhds (hyV i)`. Establish `hfy : ∀ᶠ y in 𝓝 y₀, ∀ i, f i y₀ - 1 < f i y` using `Filter.eventually_all.2 fun i => (((hf i).continuousOn (isOpen_ptsIn _)).continuousAt ((isOpen_ptsIn _).mem_nhds (hyV i))).eventually (lt_mem_nhds (sub_one_lt _))`. Use `filter_upwards [e.open_source.mem_nhds hy₀, hbd, hpts, hfy] with y hsrc hby hpy hfyy`. Introduce `hin k hk`. Establish `hyz : e.symm (e y) = y` using `e.left_inv hsrc`.

Rewrite `hby` using `[hyz]`. Establish `hek : e y k ≠ 0` using `(hinn y hsrc).1 hin k hk`. Establish `hek0 : 0 < ‖e y k‖` using `norm_pos_iff.2 hek`. Establish `hP0 : 0 < (∏ i, x.nrm σ i y) ^ 2` using `pow_pos (Finset.prod_pos fun i _ => x.nrm_pos hin i) 2`. Establish `hPeq : (∏ i, x.nrm σ i y) ^ 2 = ‖∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) y‖ ^ 2 * ∏ i, Real.exp (-f i y)`.

Rewrite using `[← Finset.prod_pow, Finset.prod_congr rfl fun i _ => heq i y (hpy i), Finset.prod_mul_distrib, norm_prod, Finset.prod_pow]`. Establish `hE : ∏ i, Real.exp (-f i y) ≤ Q` using `Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i _ => Real.exp_le_exp.2 (by linarith [hfyy i])`. Establish `hPle : (∏ i, x.nrm σ i y) ^ 2 ≤ (Lt * ‖e y k‖) ^ 2 * Q`. Rewrite using `[hPeq]`. Conclude with `mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hby k hk) 2) hE (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le) (sq_nonneg _)`.

Establish `hlog : Real.log ((∏ i, x.nrm σ i y) ^ 2) ≤ 2 * Real.log Lt + 2 * Real.log ‖e y k‖ + Real.log Q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.log_mul (by positivity) hQ0.ne', Real.log_pow, Real.log_mul hLt0.ne' hek0.ne']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hr : x.r σ y = Real.exp 1 - Real.log ((∏ i, x.nrm σ i y) ^ 2)` using `rfl`. Establish `hr1 : 1 ≤ x.r σ y` using `le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (x.exp_le_r σ y)`. Establish `hKa : K ≤ |K|` using `le_abs_self K`. Establish `hKr : |K| ≤ |K| * x.r σ y` using `le_mul_of_one_le_right (abs_nonneg K) hr1`. Establish `he : 0 ≤ Real.exp 1` using `(Real.exp_pos 1).le`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem negLog_coord_le_mul_r : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s)
    (σ : κ.c.F →+* ℂ) (n a : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)),
    IsHolTo e.target (fun z => (e.symm z).1) → (∀ y ∈ e.source, Inner y ↔ ∀ k : Fin n, (k : ℕ) < a → e y k ≠ 0) →
    ∀ y₀ ∈ e.source, ∃ U ∈ 𝓝 y₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, Inner y → ∀ k : Fin n, (k : ℕ) < a →
      -Real.log ‖e y k‖ ≤ C * x.r σ y := by
  intro D A N j S κ s x σ n a e hhol hinn y₀ hy₀
  choose V t f hyV ht hf heq using fun i => (x.nrm_div σ i).2 y₀
  set W : Set (Fin n → ℂ) := {z | z ∈ e.target ∧ ∀ i, e.symm z ∈ ptsIn (genStr s.T.Z) σ (V i).1} with hWdef
  have hWo : IsOpen W := isOpen_iff_mem_nhds.2 fun z hz => by
    have h1 : ∀ᶠ b in 𝓝 z, ∀ i, b ∈ e.target ∧ ⊤ ≤ (e.symm b).1 ⁻¹ᵁ (V i).1 :=
      Filter.eventually_all.2 fun i => (hhol (V i).1 (t i)).1.mem_nhds ⟨hz.1, hz.2 i⟩
    filter_upwards [h1, e.open_target.mem_nhds hz.1] with b hb hb'
    exact ⟨hb', fun i => (hb i).2⟩
  have hGd : DifferentiableOn ℂ (fun z => ∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z)) W := by
    have h : ∀ i ∈ (Finset.univ : Finset (Fin x.m)),
        DifferentiableOn ℂ (fun z => ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z)) W :=
      fun i _ => (hhol (V i).1 (t i)).2.mono fun z (hz : z ∈ W) => ⟨hz.1, hz.2 i⟩
    have hu : ∀ u : Finset (Fin x.m),
        DifferentiableOn ℂ (fun z => ∏ i ∈ u, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z)) W := by
      intro u
      induction u using Finset.induction_on with
      | empty => simpa using differentiableOn_const (c := (1 : ℂ))
      | insert i u hi ih =>
        simp only [Finset.prod_insert hi]
        exact (h i (Finset.mem_univ i)).mul ih
    exact hu Finset.univ
  have hz₀ : e y₀ ∈ W := ⟨e.map_source hy₀, fun i => by rw [e.left_inv hy₀]; exact hyV i⟩
  have hvan : ∀ k : Fin n, (k : ℕ) < a → ∀ z ∈ W, z k = 0 →
      ∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z) = 0 := by
    intro k hk z hz hzk
    have hs : e.symm z ∈ e.source := e.map_target hz.1
    have hni : ¬ Inner (e.symm z) := fun h =>
      (hinn _ hs).1 h k hk (by rw [e.right_inv hz.1]; exact hzk)
    have hb : LiesIn (e.symm z) (genBd s.T.Z) := not_not.1 hni
    obtain ⟨i, hi⟩ := (x.liesIn_genBd_iff _).1 hb
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((ev_eq_zero_iff (ht i) (hz.2 i)).2 hi)
  have hL : ∀ k : Fin n, ∃ L : ℝ, 0 < L ∧ ∀ᶠ z in 𝓝 (e y₀), (k : ℕ) < a →
      ‖∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm z)‖ ≤ L * ‖z k‖ := by
    intro k
    by_cases hk : (k : ℕ) < a
    · obtain ⟨L, hL0, hLe⟩ := exists_norm_le_mul_coord hWo hGd hz₀ k (hvan k hk)
      exact ⟨L, hL0, hLe.mono fun z hz _ => hz⟩
    · exact ⟨1, one_pos, Filter.Eventually.of_forall fun z h => absurd h hk⟩
  choose L hL0 hLe using hL
  set Lt : ℝ := 1 + ∑ k, L k with hLt
  have hLt0 : 0 < Lt := by
    have : 0 ≤ ∑ k, L k := Finset.sum_nonneg fun k _ => (hL0 k).le
    linarith
  have hLk : ∀ k, L k ≤ Lt := fun k => by
    have := Finset.single_le_sum (f := L) (fun k _ => (hL0 k).le) (Finset.mem_univ k)
    linarith
  set Q : ℝ := ∏ i, Real.exp (1 - f i y₀) with hQ
  have hQ0 : 0 < Q := Finset.prod_pos fun i _ => Real.exp_pos _
  set K : ℝ := 2 * Real.log Lt + Real.log Q with hK
  have hC : 0 ≤ 1 / 2 + |K| / 2 := by positivity
  refine ⟨{y | Inner y → ∀ k : Fin n, (k : ℕ) < a → -Real.log ‖e y k‖ ≤ (1 / 2 + |K| / 2) * x.r σ y}, ?_,
    1 / 2 + |K| / 2, hC, fun y hy => hy⟩
  have hbd : ∀ᶠ y in 𝓝 y₀, ∀ k : Fin n, (k : ℕ) < a →
      ‖∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (e.symm (e y))‖ ≤ Lt * ‖e y k‖ :=
    (e.continuousAt hy₀).eventually (Filter.eventually_all.2 fun k => (hLe k).mono fun z hz hk =>
      (hz hk).trans (mul_le_mul_of_nonneg_right (hLk k) (norm_nonneg _)))
  have hpts : ∀ᶠ y in 𝓝 y₀, ∀ i, y ∈ ptsIn (genStr s.T.Z) σ (V i).1 :=
    Filter.eventually_all.2 fun i => (isOpen_ptsIn _).mem_nhds (hyV i)
  have hfy : ∀ᶠ y in 𝓝 y₀, ∀ i, f i y₀ - 1 < f i y :=
    Filter.eventually_all.2 fun i => (((hf i).continuousOn (isOpen_ptsIn _)).continuousAt
      ((isOpen_ptsIn _).mem_nhds (hyV i))).eventually (lt_mem_nhds (sub_one_lt _))
  filter_upwards [e.open_source.mem_nhds hy₀, hbd, hpts, hfy] with y hsrc hby hpy hfyy
  intro hin k hk
  have hyz : e.symm (e y) = y := e.left_inv hsrc
  rw [hyz] at hby
  have hek : e y k ≠ 0 := (hinn y hsrc).1 hin k hk
  have hek0 : 0 < ‖e y k‖ := norm_pos_iff.2 hek
  have hP0 : 0 < (∏ i, x.nrm σ i y) ^ 2 := pow_pos (Finset.prod_pos fun i _ => x.nrm_pos hin i) 2
  have hPeq : (∏ i, x.nrm σ i y) ^ 2 =
      ‖∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) y‖ ^ 2 * ∏ i, Real.exp (-f i y) := by
    rw [← Finset.prod_pow, Finset.prod_congr rfl fun i _ => heq i y (hpy i), Finset.prod_mul_distrib, norm_prod,
      Finset.prod_pow]
  have hE : ∏ i, Real.exp (-f i y) ≤ Q :=
    Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i _ => Real.exp_le_exp.2 (by linarith [hfyy i])
  have hPle : (∏ i, x.nrm σ i y) ^ 2 ≤ (Lt * ‖e y k‖) ^ 2 * Q := by
    rw [hPeq]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hby k hk) 2) hE
      (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le) (sq_nonneg _)
  have hlog : Real.log ((∏ i, x.nrm σ i y) ^ 2) ≤ 2 * Real.log Lt + 2 * Real.log ‖e y k‖ + Real.log Q := by
    calc Real.log ((∏ i, x.nrm σ i y) ^ 2) ≤ Real.log ((Lt * ‖e y k‖) ^ 2 * Q) := Real.log_le_log hP0 hPle
      _ = 2 * Real.log Lt + 2 * Real.log ‖e y k‖ + Real.log Q := by
        rw [Real.log_mul (by positivity) hQ0.ne', Real.log_pow, Real.log_mul hLt0.ne' hek0.ne']
        push_cast
        ring
  have hr : x.r σ y = Real.exp 1 - Real.log ((∏ i, x.nrm σ i y) ^ 2) := rfl
  have hr1 : 1 ≤ x.r σ y := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (x.exp_le_r σ y)
  have hKa : K ≤ |K| := le_abs_self K
  have hKr : |K| ≤ |K| * x.r σ y := le_mul_of_one_le_right (abs_nonneg K) hr1
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  nlinarith

end GlobalTheory.ShFam
