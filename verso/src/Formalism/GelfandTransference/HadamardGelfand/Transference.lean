import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion

open Module Submodule

noncomputable section

namespace Formalism.HadamardInequality.P

/- English proof (translation)
Take `⟨q0, hq0, hq00⟩` from `(Submodule.ne_bot_iff Q).1 hne`. Establish `hcl : IsClosed (Q : Set E)`. Rewrite using `[← Submodule.coe_toAddSubgroup]`. Conclude with `AddSubgroup.isClosed_of_discrete`. Establish `hfin : (Metric.closedBall (0 : E) ‖q0‖ ∩ (Q : Set E)).Finite` using `Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall hcl`.

Use `set S := (Metric.closedBall (0 : E) ‖q0‖ ∩ (Q : Set E)) \ {0} with hS`. Establish `hSfin : S.Finite` using `hfin.sdiff`. Establish `hq0S : q0 ∈ S` using `⟨⟨by simp, hq0⟩, hq00⟩`. Take `⟨q, hqS, hmin⟩` from `Set.exists_min_image S (fun x => ‖x‖) hSfin ⟨q0, hq0S⟩`. Use `⟨q, hqS.1.2, hqS.2, fun q' hq' hq'0 => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hle : ‖q'‖ ≤ ‖q0‖`. Conclude with `hmin q' ⟨⟨by simpa using hle, hq'⟩, hq'0⟩`. Conclude with `(hmin q0 hq0S).trans (le_of_lt (not_le.1 hle))`.
-/
theorem tr_shortest {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Submodule ℤ E) [hQ : DiscreteTopology Q] (hne : Q ≠ ⊥) :
    ∃ q ∈ Q, q ≠ 0 ∧ ∀ q' ∈ Q, q' ≠ 0 → ‖q‖ ≤ ‖q'‖ := by
  obtain ⟨q0, hq0, hq00⟩ := (Submodule.ne_bot_iff Q).1 hne
  have hcl : IsClosed (Q : Set E) := by
    rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete
  have hfin : (Metric.closedBall (0 : E) ‖q0‖ ∩ (Q : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hcl
  set S := (Metric.closedBall (0 : E) ‖q0‖ ∩ (Q : Set E)) \ {0} with hS
  have hSfin : S.Finite := hfin.sdiff
  have hq0S : q0 ∈ S := ⟨⟨by simp, hq0⟩, hq00⟩
  obtain ⟨q, hqS, hmin⟩ := Set.exists_min_image S (fun x => ‖x‖) hSfin ⟨q0, hq0S⟩
  refine ⟨q, hqS.1.2, hqS.2, fun q' hq' hq'0 => ?_⟩
  by_cases hle : ‖q'‖ ≤ ‖q0‖
  · exact hmin q' ⟨⟨by simpa using hle, hq'⟩, hq'0⟩
  · exact (hmin q0 hq0S).trans (le_of_lt (not_le.1 hle))

/- English proof (translation)
Take `⟨hsat, hNS, -⟩` from `Formalism.F.saturation_properties E M N hMd hNM`. Use `set S := Formalism.F.satur M N with hSdef`. Establish `hSW : span ℝ (S : Set E) = W`. Rewrite using `[← hNW]`. Use `le_antisymm (span_le.2 fun x hx => (Submodule.mem_inf.1 hx).2) (span_mono hNS)` and prove the remaining obligations.

Establish `hQd : DiscreteTopology (Formalism.F.quot M S)` using `(Formalism.F.degree_quotient E M S hMd hsat).1`. Use `set Q := Formalism.F.quot M S with hQdef`. Establish `hmemQ : ∀ q, q ∈ Q ↔ ∃ m ∈ M, Wᗮ.starProjection m = q`. Introduce `q`. Simplify using `[hQdef, Formalism.F.quot, hSW]`.

Establish `hsubW : ∀ x, x - Wᗮ.starProjection x ∈ W`. Introduce `x`. Use `sub_starProjection_mem_orthogonal (K := Wᗮ) x` as an intermediate fact. Rewrite `this` using `[orthogonal_orthogonal]`. Then use the resulting hypothesis. Establish `hQne : Q ≠ ⊥`.

Introduce `hQ`. Apply `hW` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← hspan, span_le]`. Introduce `m hm`. Establish `h0 : Wᗮ.starProjection m = 0`.

Establish `: Wᗮ.starProjection m ∈ Q` using `(hmemQ _).2 ⟨m, hm, rfl⟩`. Rewrite `this` using `[hQ]`. Conclude with `(Submodule.mem_bot ℤ).1 this`. Use `hsubW m` as an intermediate fact. Rewrite `this` using `[h0, sub_zero]`. Then use the resulting hypothesis.

Take `⟨q, hqQ, hq0, hqmin⟩` from `tr_shortest Q hQne`. Take `⟨m, hm, rfl⟩` from `(hmemQ q).1 hqQ`. Conclude with `⟨m, hm, hq0, fun m' hm' h0 => hqmin _ ((hmemQ _).2 ⟨m', hm', rfl⟩) h0⟩`.
-/
theorem tr_step {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤)
    (W : Submodule ℝ E) (N : Submodule ℤ E) (hNM : N ≤ M) (hNW : span ℝ (N : Set E) = W)
    (hW : W ≠ ⊤) :
    ∃ m ∈ M, Wᗮ.starProjection m ≠ 0 ∧
      ∀ m' ∈ M, Wᗮ.starProjection m' ≠ 0 →
        ‖Wᗮ.starProjection m‖ ≤ ‖Wᗮ.starProjection m'‖ := by
  obtain ⟨hsat, hNS, -⟩ := Formalism.F.saturation_properties E M N hMd hNM
  set S := Formalism.F.satur M N with hSdef
  have hSW : span ℝ (S : Set E) = W := by
    rw [← hNW]
    refine le_antisymm (span_le.2 fun x hx => (Submodule.mem_inf.1 hx).2) (span_mono hNS)
  have hQd : DiscreteTopology (Formalism.F.quot M S) := (Formalism.F.degree_quotient E M S hMd hsat).1
  set Q := Formalism.F.quot M S with hQdef
  have hmemQ : ∀ q, q ∈ Q ↔ ∃ m ∈ M, Wᗮ.starProjection m = q := by
    intro q
    simp [hQdef, Formalism.F.quot, hSW]
  have hsubW : ∀ x, x - Wᗮ.starProjection x ∈ W := by
    intro x
    have := sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [orthogonal_orthogonal] at this
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hW
    rw [eq_top_iff, ← hspan, span_le]
    intro m hm
    have h0 : Wᗮ.starProjection m = 0 := by
      have : Wᗮ.starProjection m ∈ Q := (hmemQ _).2 ⟨m, hm, rfl⟩
      rw [hQ] at this
      exact (Submodule.mem_bot ℤ).1 this
    have := hsubW m
    rwa [h0, sub_zero] at this
  obtain ⟨q, hqQ, hq0, hqmin⟩ := tr_shortest Q hQne
  obtain ⟨m, hm, rfl⟩ := (hmemQ q).1 hqQ
  exact ⟨m, hm, hq0, fun m' hm' h0 => hqmin _ ((hmemQ _).2 ⟨m', hm', rfl⟩) h0⟩

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Use `⟨Fin.elim0, Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Establish `hr : Set.range (Fin.elim0 : Fin 0 → E) = ∅` using `Set.range_eq_empty _`. Rewrite `hw` using `[hr, Submodule.span_empty, Submodule.mem_bot]`. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using `[hw]`.

Consider the case `succ k ih`. Introduce `hk`. Take `⟨b, t, hbM, hli, ht0, hbn, hWs, hcov⟩` from `ih (by omega)`. Use `set W := span ℝ (Set.range b) with hWdef`. Use `set N := span ℤ (Set.range b) with hNdef`.

Establish `hNM : N ≤ M` using `span_le.2 (Set.range_subset_iff.2 hbM)`. Establish `hNW : span ℝ (N : Set E) = W` using `Submodule.span_span_of_tower ℤ ℝ (Set.range b)`. Establish `hNWle : ∀ z ∈ N, z ∈ W` using `fun z hz => by`. Rewrite using `[← hNW]`. Conclude with `Submodule.subset_span hz`.

Establish `hWrk : finrank ℝ W = k`. Rewrite using `[hWdef, finrank_span_eq_card hli, Fintype.card_fin]`. Establish `hWtop : W ≠ ⊤`. Introduce `h`. Establish `: finrank ℝ W = finrank ℝ E` using `by rw [h, finrank_top]`.

Use linear arithmetic over natural numbers and integers. Take `⟨m, hm, hq0, hqmin⟩` from `tr_step M hspan W N hNM hNW hWtop`. Use `set q := Wᗮ.starProjection m with hqdef`. Use `set S := ∑ l, t l ^ 2 with hSdef`. Establish `hqW : q ∈ Wᗮ` using `starProjection_apply_mem _ _`.

Establish `hwW : m - q ∈ W`. Use `sub_starProjection_mem_orthogonal (K := Wᗮ) m` as an intermediate fact. Rewrite `this` using `[orthogonal_orthogonal]`. Then use the resulting hypothesis. Take `⟨z, hzN, hz⟩` from `hcov (m - q) hwW`. Use `set b' := m - z with hb'`.

Establish `hb'M : b' ∈ M` using `M.sub_mem hm (hNM hzN)`. Establish `hdecomp : b' = q + (m - q - z)` using `by rw [hb']; abel`. Establish `hezW : m - q - z ∈ W` using `W.sub_mem hwW (hNWle z hzN)`. Establish `horth : ∀ e ∈ W, inner ℝ q e = 0` using `fun e he => by`. Rewrite using `[real_inner_comm]`.

Conclude with `Submodule.inner_right_of_mem_orthogonal he hqW`. Establish `hqpos : 0 < ‖q‖` using `norm_pos_iff.2 hq0`. Establish `hb'n : 4 * ‖b'‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 + S`. Rewrite using `[hdecomp, Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero (horth _ hezW)]`. Establish `: m - q - z = m - q - z` using `rfl`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hb'W : b' ∉ W`. Introduce `hW'`. Apply `hq0` to reduce the goal to its premises. Establish `hqW' : q ∈ W`.

Establish `: q = b' - (m - q - z)` using `by rw [hdecomp]; abel`. Rewrite using `[this]`. Conclude with `W.sub_mem hW' hezW`. Conclude with `inner_self_eq_zero.1 (horth q hqW')`. Establish `hsum : ∑ l, (Fin.snoc (α` using `fun _ => ℝ) t ‖q‖ l) ^ 2 = S + ‖q‖ ^ 2 := by`.

Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[hSdef]`. Use `⟨Fin.snoc b b', Fin.snoc (α := fun _ => ℝ) t ‖q‖, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `using hb'M`. Simplify using `using hbM j`. Conclude with `linearIndependent_finSnoc.2 ⟨hli, hb'W⟩`. Introduce `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `using hqpos`. Simplify using `using ht0 j`. Introduce `i`. Rewrite using `[hsum]`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `only [Fin.snoc_last]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Fin.snoc_castSucc]`. Use `hbn j` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg ‖q‖]`.

Introduce `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Use `⟨W, by simpa using hWrk, fun m' hm' h0 => ?_⟩` and prove the remaining obligations. Simplify using `using hqmin m' hm' h0`. Take `⟨W', hW'r, hW'm⟩` from `hWs j`.

Conclude with `⟨W', by simpa using hW'r, fun m' hm' h0 => by simpa using hW'm m' hm' h0⟩`. Introduce `w' hw'`. Rewrite using `[hsum]`. Rewrite `hw'` using `[Fin.range_snoc, Submodule.mem_span_insert]`. Take `⟨c0, w0, hw0, rfl⟩` from `hw'`.

Use `set c : ℤ := round c0 with hc`. Use `set s : ℝ := c0 - c with hs`. Establish `hsabs : |s| ≤ 1 / 2` using `abs_sub_round c0`. Establish `hs2 : s ^ 2 ≤ 1 / 4`. Use `sq_abs s` as an intermediate fact.

Use polynomial arithmetic with `[abs_nonneg s]`. Use `set w1 := w0 + s • (m - q - z) with hw1`. Establish `hw1W : w1 ∈ W` using `W.add_mem hw0 (W.smul_mem _ hezW)`. Take `⟨z1, hz1N, hz1⟩` from `hcov w1 hw1W`. Use `⟨c • b' + z1, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.range_snoc, Submodule.mem_span_insert]`. Conclude with `⟨c, z1, hz1N, rfl⟩`. Establish `heq : c0 • b' + w0 - (c • b' + z1) = s • q + (w1 - z1)`. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ, hw1, hs]`. Use `conv_lhs => rw [hdecomp]`.

Simplify using `only [sub_smul, smul_add, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hw1z1 : w1 - z1 ∈ W` using `W.sub_mem hw1W (hNWle z1 hz1N)`. Rewrite using `[heq, Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero (by`. Rewrite using `[real_inner_smul_left, horth _ hw1z1, mul_zero]), norm_smul, Real.norm_eq_abs,`.

Use the proof step `mul_pow, sq_abs]`. Establish `hqq : 0 ≤ ‖q‖ ^ 2` using `sq_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tr_chain {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) :
    ∀ k, k ≤ finrank ℝ E → ∃ (b : Fin k → E) (t : Fin k → ℝ), (∀ i, b i ∈ M) ∧
      LinearIndependent ℝ b ∧ (∀ i, 0 < t i) ∧
      (∀ i, 4 * ‖b i‖ ^ 2 ≤ 3 * t i ^ 2 + ∑ l, t l ^ 2) ∧
      (∀ i : Fin k, ∃ W : Submodule ℝ E, finrank ℝ W = i.val ∧
          ∀ m ∈ M, Wᗮ.starProjection m ≠ 0 → t i ≤ ‖Wᗮ.starProjection m‖) ∧
      (∀ w ∈ span ℝ (Set.range b), ∃ z ∈ span ℤ (Set.range b),
        4 * ‖w - z‖ ^ 2 ≤ ∑ l, t l ^ 2) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, linearIndependent_empty_type,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro w hw
    have hr : Set.range (Fin.elim0 : Fin 0 → E) = ∅ := Set.range_eq_empty _
    rw [hr, Submodule.span_empty, Submodule.mem_bot] at hw
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simp [hw]
  | succ k ih =>
    intro hk
    obtain ⟨b, t, hbM, hli, ht0, hbn, hWs, hcov⟩ := ih (by omega)
    set W := span ℝ (Set.range b) with hWdef
    set N := span ℤ (Set.range b) with hNdef
    have hNM : N ≤ M := span_le.2 (Set.range_subset_iff.2 hbM)
    have hNW : span ℝ (N : Set E) = W := Submodule.span_span_of_tower ℤ ℝ (Set.range b)
    have hNWle : ∀ z ∈ N, z ∈ W := fun z hz => by
      rw [← hNW]; exact Submodule.subset_span hz
    have hWrk : finrank ℝ W = k := by
      rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
    have hWtop : W ≠ ⊤ := by
      intro h
      have : finrank ℝ W = finrank ℝ E := by rw [h, finrank_top]
      omega
    obtain ⟨m, hm, hq0, hqmin⟩ := tr_step M hspan W N hNM hNW hWtop
    set q := Wᗮ.starProjection m with hqdef
    set S := ∑ l, t l ^ 2 with hSdef
    have hqW : q ∈ Wᗮ := starProjection_apply_mem _ _
    have hwW : m - q ∈ W := by
      have := sub_starProjection_mem_orthogonal (K := Wᗮ) m
      rwa [orthogonal_orthogonal] at this
    obtain ⟨z, hzN, hz⟩ := hcov (m - q) hwW
    set b' := m - z with hb'
    have hb'M : b' ∈ M := M.sub_mem hm (hNM hzN)
    have hdecomp : b' = q + (m - q - z) := by rw [hb']; abel
    have hezW : m - q - z ∈ W := W.sub_mem hwW (hNWle z hzN)
    have horth : ∀ e ∈ W, inner ℝ q e = 0 := fun e he => by
      rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal he hqW
    have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hb'n : 4 * ‖b'‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 + S := by
      rw [hdecomp, Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero (horth _ hezW)]
      have : m - q - z = m - q - z := rfl
      nlinarith
    have hb'W : b' ∉ W := by
      intro hW'
      apply hq0
      have hqW' : q ∈ W := by
        have : q = b' - (m - q - z) := by rw [hdecomp]; abel
        rw [this]; exact W.sub_mem hW' hezW
      exact inner_self_eq_zero.1 (horth q hqW')
    have hsum : ∑ l, (Fin.snoc (α := fun _ => ℝ) t ‖q‖ l) ^ 2 = S + ‖q‖ ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      simp [hSdef]
    refine ⟨Fin.snoc b b', Fin.snoc (α := fun _ => ℝ) t ‖q‖, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hb'M
      · simpa using hbM j
    · exact linearIndependent_finSnoc.2 ⟨hli, hb'W⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hqpos
      · simpa using ht0 j
    · intro i
      rw [hsum]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        linarith
      · simp only [Fin.snoc_castSucc]
        have := hbn j
        nlinarith [sq_nonneg ‖q‖]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · refine ⟨W, by simpa using hWrk, fun m' hm' h0 => ?_⟩
        simpa using hqmin m' hm' h0
      · obtain ⟨W', hW'r, hW'm⟩ := hWs j
        exact ⟨W', by simpa using hW'r, fun m' hm' h0 => by simpa using hW'm m' hm' h0⟩
    · intro w' hw'
      rw [hsum]
      rw [Fin.range_snoc, Submodule.mem_span_insert] at hw'
      obtain ⟨c0, w0, hw0, rfl⟩ := hw'
      set c : ℤ := round c0 with hc
      set s : ℝ := c0 - c with hs
      have hsabs : |s| ≤ 1 / 2 := abs_sub_round c0
      have hs2 : s ^ 2 ≤ 1 / 4 := by
        have := sq_abs s
        nlinarith [abs_nonneg s]
      set w1 := w0 + s • (m - q - z) with hw1
      have hw1W : w1 ∈ W := W.add_mem hw0 (W.smul_mem _ hezW)
      obtain ⟨z1, hz1N, hz1⟩ := hcov w1 hw1W
      refine ⟨c • b' + z1, ?_, ?_⟩
      · rw [Fin.range_snoc, Submodule.mem_span_insert]
        exact ⟨c, z1, hz1N, rfl⟩
      · have heq : c0 • b' + w0 - (c • b' + z1) = s • q + (w1 - z1) := by
          rw [← Int.cast_smul_eq_zsmul ℝ, hw1, hs]
          conv_lhs => rw [hdecomp]
          simp only [sub_smul, smul_add, smul_sub]
          abel
        have hw1z1 : w1 - z1 ∈ W := W.sub_mem hw1W (hNWle z1 hz1N)
        rw [heq, Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero (by
          rw [real_inner_smul_left, horth _ hw1z1, mul_zero]), norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs]
        have hqq : 0 ≤ ‖q‖ ^ 2 := sq_nonneg _
        nlinarith

/- English proof (translation)
Set `P : E →ₗ[ℝ] Wᗮ` to `(Wᗮ.orthogonalProjectionOnto : E →L[ℝ] Wᗮ).toLinearMap`. Establish `hP : ∀ x : E, ((P x : Wᗮ) : E) = Wᗮ.starProjection x` using `fun x => rfl`. Set `Q' : Submodule ℤ Wᗮ` to `M.map (P.restrictScalars ℤ)`. Establish `hmemQ : ∀ x : Wᗮ, x ∈ Q' ↔ ∃ m ∈ M, P m = x`. Introduce `x`.

Simplify using `[Q']`. Establish `hQnorm : ∀ x ∈ Q', x ≠ 0 → t ≤ ‖x‖`. Introduce `x hx hx0`. Take `⟨m, hm, rfl⟩` from `(hmemQ x).1 hx`. Establish `h1 : Wᗮ.starProjection m ≠ 0`.

Rewrite using `[← hP]`. Conclude with `hx0` after adjusting the coercions. Use `hmin m hm h1` as an intermediate fact. Rewrite `this` using `[← hP]`. Simplify using `using this`.

Establish `hQd : DiscreteTopology Q'` using `Formalism.NormUnitaryCountingLemmas.discreteTopology_of_norm_ge Q' ht hQnorm`. Establish `hQl : IsZLattice ℝ Q'` using `⟨by`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : (x : E) ∈ span ℝ (M : Set E)` using `by rw [hspan]; trivial`.

Establish `hPx : P (x : E) = x` using `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x`. Rewrite using `[← hPx]`. Establish `: P (x : E) ∈ (span ℝ (M : Set E)).map P` using `Submodule.mem_map_of_mem hx`. Rewrite `this` using `[Submodule.map_span]`. Use `span_mono ?_ this` and prove the remaining obligations.

Introduce and unpack `_ ⟨m, hm, rfl⟩`. Conclude with `(hmemQ _).2 ⟨m, hm, rfl⟩⟩`. Take `⟨hXd, hXl⟩` from `Formalism.H.dualIsLattice (Wᗮ) Q'`. Use `@hXl hXd` as an intermediate fact. Establish `hDD` using `Formalism.H.dualDual (Wᗮ) Q'`.

Take `⟨v, hvX, hvli, hvn⟩` from `Formalism.NormUnitaryCountingLemmas.Final.gn1 Wᗮ (Formalism.H.dual Q') hXd IsZLattice.span_top t ht (by`. Introduce `y hy0 hint`. Establish `hyQ : y ∈ Q'`. Rewrite using `[← hDD, LinearMap.BilinForm.mem_dualSubmodule]`. Introduce `x hx`.

Take `⟨z, hz⟩` from `hint x hx`. Rewrite using `[Submodule.mem_one]`. Conclude with `⟨z, by rw [algebraMap_int_eq, eq_intCast, ← hz]; exact real_inner_comm _ _⟩`. Conclude with `hQnorm y hyQ hy0)`. Use `⟨fun j => (v j : E), fun j => ?_, ?_, fun j => ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Establish `h` using `(LinearMap.BilinForm.mem_dualSubmodule _).1 (hvX j) (P x) ((hmemQ _).2 ⟨x, hx, rfl⟩)`. Take `⟨z, hz⟩` from `Submodule.mem_one.1 h`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[algebraMap_int_eq, eq_intCast]`.

Express the relevant statement in the definitionally equal form `(z : ℝ) = inner ℝ (v j) (P x) at hz`. Establish `e1 : inner ℝ x (v j : E) = inner ℝ (P x) (v j)` using `(Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (v j) x).symm`. Use `show inner ℝ x (v j : E) = z`. Rewrite using `[e1, real_inner_comm, hz]`. Conclude with `hvli.map' Wᗮ.subtype (Submodule.ker_subtype _)`.

Simplify using `using hvn j`.
-/
theorem tr_dual {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) (hspan : span ℝ (M : Set E) = ⊤)
    (W : Submodule ℝ E) {t : ℝ} (ht : 0 < t)
    (hmin : ∀ m ∈ M, Wᗮ.starProjection m ≠ 0 → t ≤ ‖Wᗮ.starProjection m‖) :
    ∃ y : Fin (finrank ℝ Wᗮ) → E, (∀ j, y j ∈ Formalism.HadamardInequality.zdual M) ∧ LinearIndependent ℝ y ∧
      ∀ j, ‖y j‖ ≤ (finrank ℝ Wᗮ : ℝ) ^ ((3 : ℝ) / 2) / t := by
  let P : E →ₗ[ℝ] Wᗮ := (Wᗮ.orthogonalProjectionOnto : E →L[ℝ] Wᗮ).toLinearMap
  have hP : ∀ x : E, ((P x : Wᗮ) : E) = Wᗮ.starProjection x := fun x => rfl
  let Q' : Submodule ℤ Wᗮ := M.map (P.restrictScalars ℤ)
  have hmemQ : ∀ x : Wᗮ, x ∈ Q' ↔ ∃ m ∈ M, P m = x := by
    intro x; simp [Q']
  have hQnorm : ∀ x ∈ Q', x ≠ 0 → t ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨m, hm, rfl⟩ := (hmemQ x).1 hx
    have h1 : Wᗮ.starProjection m ≠ 0 := by
      rw [← hP]; exact_mod_cast hx0
    have := hmin m hm h1
    rw [← hP] at this
    simpa using this
  have hQd : DiscreteTopology Q' := Formalism.NormUnitaryCountingLemmas.discreteTopology_of_norm_ge Q' ht hQnorm
  have hQl : IsZLattice ℝ Q' := ⟨by
    rw [eq_top_iff]
    intro x _
    have hx : (x : E) ∈ span ℝ (M : Set E) := by rw [hspan]; trivial
    have hPx : P (x : E) = x := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
    rw [← hPx]
    have : P (x : E) ∈ (span ℝ (M : Set E)).map P := Submodule.mem_map_of_mem hx
    rw [Submodule.map_span] at this
    refine span_mono ?_ this
    rintro _ ⟨m, hm, rfl⟩
    exact (hmemQ _).2 ⟨m, hm, rfl⟩⟩
  obtain ⟨hXd, hXl⟩ := Formalism.H.dualIsLattice (Wᗮ) Q'
  have := @hXl hXd
  have hDD := Formalism.H.dualDual (Wᗮ) Q'
  obtain ⟨v, hvX, hvli, hvn⟩ := Formalism.NormUnitaryCountingLemmas.Final.gn1 Wᗮ (Formalism.H.dual Q') hXd IsZLattice.span_top
    t ht (by
      intro y hy0 hint
      have hyQ : y ∈ Q' := by
        rw [← hDD, LinearMap.BilinForm.mem_dualSubmodule]
        intro x hx
        obtain ⟨z, hz⟩ := hint x hx
        rw [Submodule.mem_one]
        exact ⟨z, by rw [algebraMap_int_eq, eq_intCast, ← hz]; exact real_inner_comm _ _⟩
      exact hQnorm y hyQ hy0)
  refine ⟨fun j => (v j : E), fun j => ?_, ?_, fun j => ?_⟩
  · intro x hx
    have h := (LinearMap.BilinForm.mem_dualSubmodule _).1 (hvX j) (P x) ((hmemQ _).2 ⟨x, hx, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.1 h
    refine ⟨z, ?_⟩
    rw [algebraMap_int_eq, eq_intCast] at hz
    change (z : ℝ) = inner ℝ (v j) (P x) at hz
    have e1 : inner ℝ x (v j : E) = inner ℝ (P x) (v j) :=
      (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (v j) x).symm
    show inner ℝ x (v j : E) = z
    rw [e1, real_inner_comm, hz]
  · exact hvli.map' Wᗮ.subtype (Submodule.ker_subtype _)
  · simpa using hvn j

/- English proof (translation)
The claim follows from `csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hr, v, hv, hli, hn⟩`.
-/
theorem tr_succMin_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {i : ℕ} {r : ℝ} (v : Fin i → E) (hv : ∀ j, v j ∈ L)
    (hli : LinearIndependent ℝ v) (hr : 0 ≤ r) (hn : ∀ j, ‖v j‖ ≤ r) :
    Formalism.HadamardInequality.succMin L i ≤ r :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hr, v, hv, hli, hn⟩

/- English proof (translation)
The claim follows from `Real.sInf_nonneg fun _ hx => hx.1`.
-/
theorem tr_succMin_nonneg {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (i : ℕ) : 0 ≤ Formalism.HadamardInequality.succMin L i :=
  Real.sInf_nonneg fun _ hx => hx.1

/- English proof (translation)
Introduce `E _ _ _ M hMd hspan i hi1 hin`. Use `set n := finrank ℝ E with hn`. Use `set k := n + 1 - i with hk`. Establish `hkn : k ≤ n` using `by omega`. Establish `hk1 : 1 ≤ k` using `by omega`.

Take `⟨b, t, hbM, hli, ht0, hbn, hWs, -⟩` from `tr_chain M hspan k hkn`. Take `⟨j0, -, hj0⟩` from `Finset.exists_max_image Finset.univ t ⟨⟨0, by omega⟩, Finset.mem_univ _⟩`. Use `set T := t j0 with hT`. Establish `hTpos : 0 < T` using `ht0 j0`. Establish `htT : ∀ l, t l ^ 2 ≤ T ^ 2` using `fun l => pow_le_pow_left₀ (ht0 l).le (hj0 l (Finset.mem_univ _)) 2`.

Establish `hS : ∑ l, t l ^ 2 ≤ (k : ℝ) * T ^ 2`. Combine the equalities or inequalities in the displayed calculation. Use `set R := Real.sqrt (((k : ℝ) + 3) / 4 * T ^ 2) with hR`. Establish `hR0 : 0 ≤ R` using `Real.sqrt_nonneg _`. Establish `hbR : ∀ j, ‖b j‖ ≤ R`.

Introduce `j`. Establish `h1` using `hbn j`. Establish `h2` using `htT j`. Establish `h3 : ‖b j‖ ^ 2 ≤ ((k : ℝ) + 3) / 4 * T ^ 2` using `by nlinarith`. Use `Real.abs_le_sqrt h3` as an intermediate fact.

Rewrite `this` using `[abs_of_nonneg (norm_nonneg _)]`. Then use the resulting hypothesis. Establish `hMk : Formalism.HadamardInequality.succMin M k ≤ R` using `tr_succMin_le M b hbM hli hR0 hbR`. Take `⟨W, hWr, hWm⟩` from `hWs j0`. Take `⟨y, hyD, hyli, hyn⟩` from `tr_dual M hspan W hTpos hWm`. Establish `hfr : finrank ℝ W + finrank ℝ Wᗮ = n` using `Submodule.finrank_add_finrank_orthogonal W`.

Establish `hj0k` using `j0.2`. Establish `hij : i ≤ finrank ℝ Wᗮ` using `by omega`. Establish `hWn : finrank ℝ Wᗮ ≤ n` using `by omega`. Use `set A := (n : ℝ) ^ ((3 : ℝ) / 2) / T with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`.

Establish `hyA : ∀ j, ‖y (Fin.castLE hij j)‖ ≤ A`. Introduce `j`. Use `(hyn _).trans (div_le_div_of_nonneg_right ?_ hTpos.le)` and prove the remaining obligations. Conclude with `Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hWn) (by norm_num)`. Establish `hDi : Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) i ≤ A` using `tr_succMin_le _ (fun j => y (Fin.castLE hij j)) (fun j => hyD _) (hyli.comp _ (Fin.castLE_injective hij)) hA0 hyA`.

Establish `hAR : A * R ≤ (n : ℝ) ^ 2`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg _`. Establish `hA2 : A ^ 2 = (n : ℝ) ^ 3 / T ^ 2`. Rewrite using `[hA, div_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hn0]`. Evaluate the numerical expressions.

Establish `hR2 : R ^ 2 = ((k : ℝ) + 3) / 4 * T ^ 2` using `Real.sq_sqrt (by positivity)`. Establish `hk' : (k : ℝ) ≤ n` using `by exact_mod_cast hkn`. Rewrite using `[← pow_le_pow_iff_left₀ (mul_nonneg hA0 hR0) (by positivity) two_ne_zero]`. Rewrite using `[mul_pow, hA2, hR2]`. Establish `e : (n : ℝ) ^ 3 / T ^ 2 * (((k : ℝ) + 3) / 4 * T ^ 2) = (n : ℝ) ^ 3 * (((k : ℝ) + 3) / 4)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Establish `h4 : ((k : ℝ) + 3) / 4 ≤ n`. Establish `: (1 : ℝ) ≤ k` using `by exact_mod_cast hk1`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem transference_principle : Formalism.HadamardInequality.Transference := by
  intro E _ _ _ M hMd hspan i hi1 hin
  set n := finrank ℝ E with hn
  set k := n + 1 - i with hk
  have hkn : k ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨b, t, hbM, hli, ht0, hbn, hWs, -⟩ := tr_chain M hspan k hkn
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ t
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set T := t j0 with hT
  have hTpos : 0 < T := ht0 j0
  have htT : ∀ l, t l ^ 2 ≤ T ^ 2 := fun l =>
    pow_le_pow_left₀ (ht0 l).le (hj0 l (Finset.mem_univ _)) 2
  have hS : ∑ l, t l ^ 2 ≤ (k : ℝ) * T ^ 2 := by
    calc ∑ l, t l ^ 2 ≤ ∑ _l : Fin k, T ^ 2 := Finset.sum_le_sum fun l _ => htT l
      _ = (k : ℝ) * T ^ 2 := by simp
  set R := Real.sqrt (((k : ℝ) + 3) / 4 * T ^ 2) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hbR : ∀ j, ‖b j‖ ≤ R := by
    intro j
    have h1 := hbn j
    have h2 := htT j
    have h3 : ‖b j‖ ^ 2 ≤ ((k : ℝ) + 3) / 4 * T ^ 2 := by nlinarith
    have := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hMk : Formalism.HadamardInequality.succMin M k ≤ R := tr_succMin_le M b hbM hli hR0 hbR
  obtain ⟨W, hWr, hWm⟩ := hWs j0
  obtain ⟨y, hyD, hyli, hyn⟩ := tr_dual M hspan W hTpos hWm
  have hfr : finrank ℝ W + finrank ℝ Wᗮ = n := Submodule.finrank_add_finrank_orthogonal W
  have hj0k := j0.2
  have hij : i ≤ finrank ℝ Wᗮ := by omega
  have hWn : finrank ℝ Wᗮ ≤ n := by omega
  set A := (n : ℝ) ^ ((3 : ℝ) / 2) / T with hA
  have hA0 : 0 ≤ A := by positivity
  have hyA : ∀ j, ‖y (Fin.castLE hij j)‖ ≤ A := by
    intro j
    refine (hyn _).trans (div_le_div_of_nonneg_right ?_ hTpos.le)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hWn) (by norm_num)
  have hDi : Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) i ≤ A :=
    tr_succMin_le _ (fun j => y (Fin.castLE hij j)) (fun j => hyD _)
      (hyli.comp _ (Fin.castLE_injective hij)) hA0 hyA
  have hAR : A * R ≤ (n : ℝ) ^ 2 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hA2 : A ^ 2 = (n : ℝ) ^ 3 / T ^ 2 := by
      rw [hA, div_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hn0]
      norm_num
    have hR2 : R ^ 2 = ((k : ℝ) + 3) / 4 * T ^ 2 := Real.sq_sqrt (by positivity)
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    rw [← pow_le_pow_iff_left₀ (mul_nonneg hA0 hR0) (by positivity) two_ne_zero]
    rw [mul_pow, hA2, hR2]
    have e : (n : ℝ) ^ 3 / T ^ 2 * (((k : ℝ) + 3) / 4 * T ^ 2) =
        (n : ℝ) ^ 3 * (((k : ℝ) + 3) / 4) := by
      field_simp
    rw [e]
    have h4 : ((k : ℝ) + 3) / 4 ≤ n := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith
    calc (n : ℝ) ^ 3 * (((k : ℝ) + 3) / 4) ≤ (n : ℝ) ^ 3 * n :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = ((n : ℝ) ^ 2) ^ 2 := by ring
  calc Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) i * Formalism.HadamardInequality.succMin M k ≤ A * R :=
        mul_le_mul hDi hMk (tr_succMin_nonneg _ _) hA0
    _ ≤ (n : ℝ) ^ 2 := hAR

end Formalism.HadamardInequality.P
