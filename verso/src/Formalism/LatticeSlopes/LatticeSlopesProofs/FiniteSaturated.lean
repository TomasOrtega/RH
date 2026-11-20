import Formalism.LatticeSlopes.Statement
import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained

open Module Submodule

noncomputable section

namespace Formalism.F

universe u

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Establish `hD : DiscreteTopology (L.toAddSubgroup)` using `hL`. Establish `hcl : IsClosed (L : Set E)` using `AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)`. Establish `hs : IsDiscrete (L : Set E)` using `isDiscrete_iff_discreteTopology.mpr hL`. Use `(Metric.finite_isBounded_inter_isClosed hs (Metric.isBounded_closedBall (x := (0 : E)) (r := C)) hcl).subset ?_` and prove the remaining obligations. Introduce `v hv`.

Conclude with `⟨mem_closedBall_zero_iff.mpr hv.2, hv.1⟩`.
-/
theorem finite_mem_norm_le (L : Submodule ℤ E) [hL : DiscreteTopology L] (C : ℝ) :
    {v : E | v ∈ L ∧ ‖v‖ ≤ C}.Finite := by
  have hD : DiscreteTopology (L.toAddSubgroup) := hL
  have hcl : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hs : IsDiscrete (L : Set E) := isDiscrete_iff_discreteTopology.mpr hL
  refine (Metric.finite_isBounded_inter_isClosed hs (Metric.isBounded_closedBall (x := (0 : E)) (r := C))
    hcl).subset ?_
  intro v hv
  exact ⟨mem_closedBall_zero_iff.mpr hv.2, hv.1⟩

/- English proof (translation)
Establish `h0 : Wᗮ.starProjection (x - z) = 0` using `by rw [map_sub, h, sub_self]`. Rewrite `h0` using `[Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]`. Conclude with `h0`.
-/
theorem sub_mem_of_starProjection_eq (W : Submodule ℝ E) {x z : E}
    (h : Wᗮ.starProjection x = Wᗮ.starProjection z) : x - z ∈ W := by
  have h0 : Wᗮ.starProjection (x - z) = 0 := by rw [map_sub, h, sub_self]
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h0
  exact h0

/- English proof (translation)
Unfold `quot at hπ`. Rewrite `hπ` using `[Submodule.map_coe]`. Establish `hfun : ⇑(LinearMap.restrictScalars ℤ (((span ℝ (N₁ : Set E))ᗮ.starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E)) = ⇑(((span ℝ (N₁ : Set E))ᗮ.starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E)` using `rfl`. Rewrite `hπ` using `[hfun, Submodule.span_image, Submodule.mem_map]`. Take `⟨y, hy, hyx⟩` from `hπ`.

Establish `hxy : x - y ∈ span ℝ (N₁ : Set E)` using `sub_mem_of_starProjection_eq _ hyx.symm`. Establish `hle : span ℝ (N₁ : Set E) ≤ span ℝ (M : Set E)` using `span_mono h1`. Use `hM.2 x hx ?_` and prove the remaining obligations. Use `add_mem (hle hxy) hy` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem mem_of_starProjection_mem_span_orthQuotient {L M N₁ : Submodule ℤ E} (hM : IsSaturated L M) (h1 : N₁ ≤ M)
    {x : E} (hx : x ∈ L)
    (hπ : (span ℝ (N₁ : Set E))ᗮ.starProjection x ∈ span ℝ (quot M N₁ : Set E)) : x ∈ M := by
  unfold quot at hπ
  rw [Submodule.map_coe] at hπ
  have hfun : ⇑(LinearMap.restrictScalars ℤ
      (((span ℝ (N₁ : Set E))ᗮ.starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E)) =
      ⇑(((span ℝ (N₁ : Set E))ᗮ.starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
  rw [hfun, Submodule.span_image, Submodule.mem_map] at hπ
  obtain ⟨y, hy, hyx⟩ := hπ
  have hxy : x - y ∈ span ℝ (N₁ : Set E) := sub_mem_of_starProjection_eq _ hyx.symm
  have hle : span ℝ (N₁ : Set E) ≤ span ℝ (M : Set E) := span_mono h1
  refine hM.2 x hx ?_
  have := add_mem (hle hxy) hy
  rwa [sub_add_cancel] at this

end

/- English proof (translation)
Unfold `rk`. Conclude with `Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, by simpa using hv0⟩`.
-/
private theorem rk_pos_of_ne_zero_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (N : Submodule ℤ E) [DiscreteTopology N]
    {v : E} (hv : v ∈ N) (hv0 : v ≠ 0) : 0 < rk N := by
  unfold rk
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, by simpa using hv0⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `L hL X`. Use `(Set.finite_singleton (⊥ : Submodule ℤ E)).subset ?_` and prove the remaining obligations. Introduce and unpack `N ⟨hN, hrk, -⟩`.

Use `haveI : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hN.1`. Rewrite using `[Set.mem_singleton_iff]`. Assume the negation of the conclusion as `hne`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).mp hne`. Use `rk_pos_of_ne_zero_mem N hv hv0` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Introduce `L hL X`. Establish `hdisc : ∀ N : Submodule ℤ E, N ≤ L → DiscreteTopology N` using `fun N h => DiscreteTopology.of_subset (s := (L : Set E)) hL h`. Establish `hB : {v : E | v ∈ L ∧ ‖v‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) * max 1 X ∧ v ≠ 0}.Finite` using `(finite_mem_norm_le L _).subset fun v hv => ⟨hv.1, hv.2.1⟩`.

Use `((Set.finite_singleton ⊥).union (hB.biUnion (t := fun v => {N : Submodule ℤ E | IsSaturated L N ∧ rk N ≤ k + 1 ∧ covol N ≤ X ∧ satur L (span ℤ ({v} : Set E)) ≤ N}) fun v hv => ?_)).subset ?_` and prove the remaining obligations. Take `⟨hvL, -, hv0⟩` from `hv`. Establish `hspL : span ℤ ({v} : Set E) ≤ L` using `span_le.mpr (Set.singleton_subset_iff.mpr hvL)`. Take `⟨sat1, hsp1, hrk1⟩` from `saturation_properties E L _ hL hspL`. Use `haveI : DiscreteTopology (span ℤ ({v} : Set E)) := hdisc _ hspL`.

Establish `hrksp : 0 < rk (span ℤ ({v} : Set E))` using `rk_pos_of_ne_zero_mem _ (mem_span_singleton_self v) hv0`. Establish `dq` using `degree_quotient E L _ hL sat1`. Establish `hc1 : 0 < covol (satur L (span ℤ ({v} : Set E)))` using `covol_pos' E _ (hdisc _ sat1.1)`. Establish `hfin` using `ih (quot L (satur L (span ℤ ({v} : Set E)))) dq.1 (X / covol (satur L (span ℤ ({v} : Set E))))`. Use `Set.Finite.of_finite_image (f := fun N => quot N (satur L (span ℤ ({v} : Set E)))) (hfin.subset ?_) ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨N, ⟨hN, hrkN, hcov, h1⟩, rfl⟩ dsimp only [Set.mem_setOf_eq]`. Establish `hdN` using `hdisc N hN.1`. Establish `satN1 : IsSaturated N (satur L (span ℤ ({v} : Set E)))` using `⟨h1, fun x hx hxs => sat1.2 x (hN.1 hx) hxs⟩`. Establish `dqN` using `degree_quotient E N _ hdN satN1`. Establish `hcQ` using `covol_pos' E _ dqN.1`.

Establish `hcN` using `covol_pos' E N hdN`. Establish `hlog : Real.log (covol N) = Real.log (covol (satur L (span ℤ ({v} : Set E))) * covol (quot N (satur L (span ℤ ({v} : Set E)))))`. Rewrite using `[Real.log_mul hc1.ne' hcQ.ne']`. Use `dqN.2.2` as an intermediate fact. Unfold `deg at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmul` using `Real.log_injOn_pos (Set.mem_Ioi.mpr hcN) (Set.mem_Ioi.mpr (mul_pos hc1 hcQ)) hlog`. Use `⟨⟨Submodule.map_mono hN.1, fun y hy hys => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, hxL, rfl⟩` from `Submodule.mem_map.mp hy`. Conclude with `Submodule.mem_map_of_mem (mem_of_starProjection_mem_span_orthQuotient hN h1 hxL hys)`.

Use `dqN.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[le_div_iff₀ hc1, mul_comm, ← hmul]`. Conclude with `hcov`. Introduce `N hN N' hN' heq`.

Establish `key : ∀ {A B : Submodule ℤ E}, IsSaturated L B → satur L (span ℤ ({v} : Set E)) ≤ B → quot A (satur L (span ℤ ({v} : Set E))) = quot B (satur L (span ℤ ({v} : Set E))) → A ≤ L → A ≤ B`. Introduce `A B hB hB1 hAB hAL x hx`. Use `mem_of_starProjection_mem_span_orthQuotient hB hB1 (hAL hx) ?_` and prove the remaining obligations. Rewrite using `[← hAB]`. Conclude with `subset_span (Submodule.mem_map_of_mem hx)`.

Conclude with `le_antisymm (key hN'.1 hN'.2.2.2 heq hN.1.1) (key hN.1 hN.2.2.2 heq.symm hN'.1.1)`. Introduce and unpack `N ⟨hN, hrk, hcov⟩`. Distinguish the cases in `hbot : N = ⊥`. Conclude with `Or.inl hbot`. Use `right`.

Establish `hdN` using `hdisc N hN.1`. Take `⟨v, hvN, hv0, hvle⟩` from `hS E N hdN hbot`. Establish `hr` using `rk_pos_of_ne_zero_mem N hvN hv0`. Establish `hcN` using `covol_pos' E N hdN`. Establish `hsq : Real.sqrt (rk N : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ)` using `Real.sqrt_le_sqrt (by exact_mod_cast hrk)`.

Establish `hpow : covol N ^ ((1 : ℝ) / (rk N : ℝ)) ≤ max 1 X`. Establish `he : (1 : ℝ) / (rk N : ℝ) ≤ 1`. Rewrite using `[div_le_one (by exact_mod_cast hr)]`. Conclude with `hr` after adjusting the coercions. Establish `he0 : (0 : ℝ) ≤ 1 / (rk N : ℝ)` using `by positivity`.

Break down `le_or_gt (covol N) 1 with h | h` into its components or cases. Conclude with `(Real.rpow_le_one hcN.le h he0).trans (le_max_left _ _)`. Combine the equalities or inequalities in the displayed calculation. Establish `hnorm : ‖v‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) * max 1 X` using `hvle.trans (mul_le_mul hsq hpow (by positivity) (Real.sqrt_nonneg _))`. Use `Set.mem_biUnion (x := v) ⟨hN.1 hvN, hnorm, hv0⟩ ⟨hN, hrk, hcov, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Take `⟨hxL, hxs⟩` from `Submodule.mem_inf.mp hx`. Use `hN.2 x hxL (span_mono ?_ ((Submodule.restrictScalars_mem _ _ _).mp hxs))` and prove the remaining obligations. Conclude with `span_le.mpr (Set.singleton_subset_iff.mpr hvN)`.
-/
theorem finite_saturated_rank_le_covol_le (hS : ShortVector.{u}) {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (k : ℕ) :
    ∀ (L : Submodule ℤ E), DiscreteTopology L → ∀ X : ℝ,
      {N : Submodule ℤ E | IsSaturated L N ∧ rk N ≤ k ∧ covol N ≤ X}.Finite := by
  induction k with
  | zero =>
    intro L hL X
    refine (Set.finite_singleton (⊥ : Submodule ℤ E)).subset ?_
    rintro N ⟨hN, hrk, -⟩
    haveI : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hN.1
    rw [Set.mem_singleton_iff]
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
    have := rk_pos_of_ne_zero_mem N hv hv0
    omega
  | succ k ih =>
    intro L hL X
    have hdisc : ∀ N : Submodule ℤ E, N ≤ L → DiscreteTopology N :=
      fun N h => DiscreteTopology.of_subset (s := (L : Set E)) hL h
    have hB : {v : E | v ∈ L ∧ ‖v‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) * max 1 X ∧ v ≠ 0}.Finite :=
      (finite_mem_norm_le L _).subset fun v hv => ⟨hv.1, hv.2.1⟩
    refine ((Set.finite_singleton ⊥).union (hB.biUnion (t := fun v =>
      {N : Submodule ℤ E | IsSaturated L N ∧ rk N ≤ k + 1 ∧ covol N ≤ X ∧
        satur L (span ℤ ({v} : Set E)) ≤ N}) fun v hv => ?_)).subset ?_
    ·
      obtain ⟨hvL, -, hv0⟩ := hv
      have hspL : span ℤ ({v} : Set E) ≤ L := span_le.mpr (Set.singleton_subset_iff.mpr hvL)
      obtain ⟨sat1, hsp1, hrk1⟩ := saturation_properties E L _ hL hspL
      haveI : DiscreteTopology (span ℤ ({v} : Set E)) := hdisc _ hspL
      have hrksp : 0 < rk (span ℤ ({v} : Set E)) :=
        rk_pos_of_ne_zero_mem _ (mem_span_singleton_self v) hv0
      have dq := degree_quotient E L _ hL sat1
      have hc1 : 0 < covol (satur L (span ℤ ({v} : Set E))) := covol_pos' E _ (hdisc _ sat1.1)
      have hfin := ih (quot L (satur L (span ℤ ({v} : Set E)))) dq.1
        (X / covol (satur L (span ℤ ({v} : Set E))))
      refine Set.Finite.of_finite_image (f := fun N => quot N (satur L (span ℤ ({v} : Set E))))
        (hfin.subset ?_) ?_
      · rintro _ ⟨N, ⟨hN, hrkN, hcov, h1⟩, rfl⟩
        dsimp only [Set.mem_setOf_eq]
        have hdN := hdisc N hN.1
        have satN1 : IsSaturated N (satur L (span ℤ ({v} : Set E))) :=
          ⟨h1, fun x hx hxs => sat1.2 x (hN.1 hx) hxs⟩
        have dqN := degree_quotient E N _ hdN satN1
        have hcQ := covol_pos' E _ dqN.1
        have hcN := covol_pos' E N hdN
        have hlog : Real.log (covol N) = Real.log (covol (satur L (span ℤ ({v} : Set E))) *
            covol (quot N (satur L (span ℤ ({v} : Set E))))) := by
          rw [Real.log_mul hc1.ne' hcQ.ne']
          have := dqN.2.2
          unfold deg at this
          linarith
        have hmul := Real.log_injOn_pos (Set.mem_Ioi.mpr hcN) (Set.mem_Ioi.mpr (mul_pos hc1 hcQ)) hlog
        refine ⟨⟨Submodule.map_mono hN.1, fun y hy hys => ?_⟩, ?_, ?_⟩
        · obtain ⟨x, hxL, rfl⟩ := Submodule.mem_map.mp hy
          exact Submodule.mem_map_of_mem (mem_of_starProjection_mem_span_orthQuotient hN h1 hxL hys)
        · have := dqN.2.1
          omega
        · rw [le_div_iff₀ hc1, mul_comm, ← hmul]
          exact hcov
      · intro N hN N' hN' heq
        have key : ∀ {A B : Submodule ℤ E}, IsSaturated L B → satur L (span ℤ ({v} : Set E)) ≤ B →
            quot A (satur L (span ℤ ({v} : Set E))) = quot B (satur L (span ℤ ({v} : Set E))) →
            A ≤ L → A ≤ B := by
          intro A B hB hB1 hAB hAL x hx
          refine mem_of_starProjection_mem_span_orthQuotient hB hB1 (hAL hx) ?_
          rw [← hAB]
          exact subset_span (Submodule.mem_map_of_mem hx)
        exact le_antisymm (key hN'.1 hN'.2.2.2 heq hN.1.1) (key hN.1 hN.2.2.2 heq.symm hN'.1.1)
    ·
      rintro N ⟨hN, hrk, hcov⟩
      by_cases hbot : N = ⊥
      · exact Or.inl hbot
      right
      have hdN := hdisc N hN.1
      obtain ⟨v, hvN, hv0, hvle⟩ := hS E N hdN hbot
      have hr := rk_pos_of_ne_zero_mem N hvN hv0
      have hcN := covol_pos' E N hdN
      have hsq : Real.sqrt (rk N : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hrk)
      have hpow : covol N ^ ((1 : ℝ) / (rk N : ℝ)) ≤ max 1 X := by
        have he : (1 : ℝ) / (rk N : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hr)]
          exact_mod_cast hr
        have he0 : (0 : ℝ) ≤ 1 / (rk N : ℝ) := by positivity
        rcases le_or_gt (covol N) 1 with h | h
        · exact (Real.rpow_le_one hcN.le h he0).trans (le_max_left _ _)
        · calc covol N ^ ((1 : ℝ) / (rk N : ℝ)) ≤ covol N ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h.le he
            _ = covol N := Real.rpow_one _
            _ ≤ max 1 X := hcov.trans (le_max_right _ _)
      have hnorm : ‖v‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) * max 1 X :=
        hvle.trans (mul_le_mul hsq hpow (by positivity) (Real.sqrt_nonneg _))
      refine Set.mem_biUnion (x := v) ⟨hN.1 hvN, hnorm, hv0⟩ ⟨hN, hrk, hcov, ?_⟩
      intro x hx
      obtain ⟨hxL, hxs⟩ := Submodule.mem_inf.mp hx
      refine hN.2 x hxL (span_mono ?_ ((Submodule.restrictScalars_mem _ _ _).mp hxs))
      exact span_le.mpr (Set.singleton_subset_iff.mpr hvN)

/- English proof (translation)
Introduce `E _ _ _ L hL X`. Use `(finite_saturated_rank_le_covol_le hS (rk L) L hL X).subset ?_` and prove the remaining obligations. Introduce and unpack `N ⟨hN, hX⟩`. Use `(degree_quotient E L N hL hN).2.1` as an intermediate fact. Conclude with `⟨hN, by omega, hX⟩`.
-/
theorem finiteSaturated_of (hS : ShortVector.{u}) : FiniteSaturated.{u} := by
  intro E _ _ _ L hL X
  refine (finite_saturated_rank_le_covol_le hS (rk L) L hL X).subset ?_
  rintro N ⟨hN, hX⟩
  have := (degree_quotient E L N hL hN).2.1
  exact ⟨hN, by omega, hX⟩

end Formalism.F
