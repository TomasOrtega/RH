import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ExistsNeZeroNormLeRankDivOfDualMinimum
import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot

open Module Submodule

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Take `⟨hSat, hNS, -⟩` from `Formalism.F.saturation_properties E M N hMd hNM`. Take `⟨hQd, hrk, -⟩` from `Formalism.F.degree_quotient E M (Formalism.F.satur M N) hMd hSat`. Establish `hSW : span ℝ ((Formalism.F.satur M N : Submodule ℤ E) : Set E) = W`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce `x hx`. Rewrite using `[← hNW]`. Conclude with `(Submodule.mem_inf.mp hx).2`. Rewrite using `[← hNW]`. Conclude with `Submodule.span_mono (show (N : Set E) ⊆ Formalism.F.satur M N from hNS)`.

Establish `hQeq : ∀ q, q ∈ Formalism.F.quot M (Formalism.F.satur M N) ↔ ∃ m ∈ M, Wᗮ.starProjection m = q`. Introduce `q`. Simplify using `[Formalism.F.quot, hSW, Submodule.mem_map]`. Use `haveI := hQd`. Establish `hPzero : ∀ x ∈ W, Wᗮ.starProjection x = 0`.

Introduce `x hx`. Establish `h1` using `Submodule.starProjection_add_starProjection_orthogonal (K := W) x`. Rewrite `h1` using `[Submodule.starProjection_eq_self_iff.mpr hx]`. Simplify using `using h1`. Establish `hsubW : ∀ m : E, m - Wᗮ.starProjection m ∈ W`.

Introduce `m`. Establish `h1` using `Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m`. Rewrite `h1` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Establish `hQne : Formalism.F.quot M (Formalism.F.satur M N) ≠ ⊥`. Introduce `hQ0`.

Apply `hW` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`. Introduce `m hm`. Establish `hq : Wᗮ.starProjection m ∈ Formalism.F.quot M (Formalism.F.satur M N)` using `(hQeq _).mpr ⟨m, hm, rfl⟩`. Rewrite `hq` using `[hQ0, Submodule.mem_bot]`.

Establish `h1` using `hsubW m`. Rewrite `h1` using `[hq, sub_zero]`. Conclude with `h1`. Establish `hdual' : ∀ y ∈ span ℝ ((Formalism.F.quot M (Formalism.F.satur M N) : Submodule ℤ E) : Set E), y ≠ 0 → (∀ x ∈ Formalism.F.quot M (Formalism.F.satur M N), ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖`. Introduce `y hy hy0 hint`.

Apply `hdual y hy0` to reduce the goal to its premises. Introduce `x hx`. Take `⟨z, hz⟩` from `hint _ ((hQeq _).mpr ⟨x, hx, rfl⟩)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `hyW : y ∈ Wᗮ`.

Use `(Submodule.span_le.mpr ?_) hy` and prove the remaining obligations. Introduce `q hq`. Take `⟨m, -, rfl⟩` from `(hQeq q).mp hq`. Conclude with `Submodule.starProjection_apply_mem _ _`. Rewrite using `[← hz, Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hyW]`.

Take `⟨q, hqQ, hq0, hqle⟩` from `exists_ne_zero_norm_le_rank_div_of_dualMinimum (Formalism.F.quot M (Formalism.F.satur M N)) hQne hl hdual'`. Take `⟨m, hm, rfl⟩` from `(hQeq q).mp hqQ`. Use `⟨m, hm, hq0, le_trans hqle ?_⟩` and prove the remaining obligations. Establish `hMrk : Formalism.F.rk M = finrank ℝ E` using `by haveI : IsZLattice ℝ M := ⟨hspan⟩`. Conclude with `ZLattice.rank ℝ M`.

Establish `hle : Formalism.F.rk (Formalism.F.quot M (Formalism.F.satur M N)) ≤ finrank ℝ E`. Rewrite using `[← hMrk, hrk]`. Conclude with `Nat.le_add_left _ _`. Conclude with `div_le_div_of_nonneg_right (by exact_mod_cast hle) hl.le`.
-/
theorem exists_starProjection_ne_zero_norm_le_of_dualMinimum (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) {l : ℝ} (hl : 0 < l)
    (hdual : ∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖)
    (W : Submodule ℝ E) (N : Submodule ℤ E) (hNM : N ≤ M) (hNW : span ℝ (N : Set E) = W)
    (hW : W ≠ ⊤) :
    ∃ m ∈ M, Wᗮ.starProjection m ≠ 0 ∧
      ‖Wᗮ.starProjection m‖ ≤ (finrank ℝ E : ℝ) / l := by
  classical
  obtain ⟨hSat, hNS, -⟩ := Formalism.F.saturation_properties E M N hMd hNM
  obtain ⟨hQd, hrk, -⟩ := Formalism.F.degree_quotient E M (Formalism.F.satur M N) hMd hSat
  have hSW : span ℝ ((Formalism.F.satur M N : Submodule ℤ E) : Set E) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rw [← hNW]
      exact (Submodule.mem_inf.mp hx).2
    · rw [← hNW]
      exact Submodule.span_mono (show (N : Set E) ⊆ Formalism.F.satur M N from hNS)
  have hQeq : ∀ q, q ∈ Formalism.F.quot M (Formalism.F.satur M N) ↔ ∃ m ∈ M, Wᗮ.starProjection m = q := by
    intro q
    simp [Formalism.F.quot, hSW, Submodule.mem_map]
  haveI := hQd
  have hPzero : ∀ x ∈ W, Wᗮ.starProjection x = 0 := by
    intro x hx
    have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := W) x
    rw [Submodule.starProjection_eq_self_iff.mpr hx] at h1
    simpa using h1
  have hsubW : ∀ m : E, m - Wᗮ.starProjection m ∈ W := by
    intro m
    have h1 := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m
    rwa [Submodule.orthogonal_orthogonal] at h1
  have hQne : Formalism.F.quot M (Formalism.F.satur M N) ≠ ⊥ := by
    intro hQ0
    apply hW
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro m hm
    have hq : Wᗮ.starProjection m ∈ Formalism.F.quot M (Formalism.F.satur M N) := (hQeq _).mpr ⟨m, hm, rfl⟩
    rw [hQ0, Submodule.mem_bot] at hq
    have h1 := hsubW m
    rw [hq, sub_zero] at h1
    exact h1
  have hdual' : ∀ y ∈ span ℝ ((Formalism.F.quot M (Formalism.F.satur M N) : Submodule ℤ E) : Set E), y ≠ 0 →
      (∀ x ∈ Formalism.F.quot M (Formalism.F.satur M N), ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖ := by
    intro y hy hy0 hint
    apply hdual y hy0
    intro x hx
    obtain ⟨z, hz⟩ := hint _ ((hQeq _).mpr ⟨x, hx, rfl⟩)
    refine ⟨z, ?_⟩
    have hyW : y ∈ Wᗮ := by
      refine (Submodule.span_le.mpr ?_) hy
      intro q hq
      obtain ⟨m, -, rfl⟩ := (hQeq q).mp hq
      exact Submodule.starProjection_apply_mem _ _
    rw [← hz, Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hyW]
  obtain ⟨q, hqQ, hq0, hqle⟩ := exists_ne_zero_norm_le_rank_div_of_dualMinimum (Formalism.F.quot M (Formalism.F.satur M N)) hQne hl hdual'
  obtain ⟨m, hm, rfl⟩ := (hQeq q).mp hqQ
  refine ⟨m, hm, hq0, le_trans hqle ?_⟩
  have hMrk : Formalism.F.rk M = finrank ℝ E := by
    haveI : IsZLattice ℝ M := ⟨hspan⟩
    exact ZLattice.rank ℝ M
  have hle : Formalism.F.rk (Formalism.F.quot M (Formalism.F.satur M N)) ≤ finrank ℝ E := by
    rw [← hMrk, hrk]
    exact Nat.le_add_left _ _
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hl.le

/- English proof (translation)
Rewrite using `[norm_add_sq_real, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_add_sq_eq_of_inner_eq_zero {x y : E} (h : inner ℝ x y = 0) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring

/- English proof (translation)
Establish `hPzero : ∀ (W : Submodule ℝ E), ∀ x ∈ W, Wᗮ.starProjection x = 0`. Introduce `W x hx`. Establish `h1` using `Submodule.starProjection_add_starProjection_orthogonal (K := W) x`. Rewrite `h1` using `[Submodule.starProjection_eq_self_iff.mpr hx]`. Simplify using `using h1`.

Establish `hsubW : ∀ (W : Submodule ℝ E) (m : E), m - Wᗮ.starProjection m ∈ W`. Introduce `W m`. Establish `h1` using `Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m`. Rewrite `h1` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Establish `horth : ∀ (W : Submodule ℝ E) (u : E) (m : E), u ∈ W → inner ℝ u (Wᗮ.starProjection m) = 0`.

Introduce `W u m hu`. Conclude with `Submodule.inner_right_of_mem_orthogonal hu (Submodule.starProjection_apply_mem _ _)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `_`. Use `⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Establish `hw0 : w = 0` using `by simpa [Set.range_eq_empty] using hw`.

Substitute `hw0` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `hk`. Take `⟨b, hbM, hbli, hbn, hbd⟩` from `ih (by omega)`.

Establish `hNM : span ℤ (Set.range b) ≤ M` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbM i)`. Establish `hNW : span ℝ ((span ℤ (Set.range b) : Submodule ℤ E) : Set E) = span ℝ (Set.range b)` using `Submodule.span_span_of_tower ℤ ℝ (Set.range b)`. Establish `hWtop : span ℝ (Set.range b) ≠ ⊤`. Introduce `hW`. Establish `h1 : finrank ℝ (span ℝ (Set.range b)) = k`.

Rewrite using `[finrank_span_eq_card hbli, Fintype.card_fin]`. Rewrite `h1` using `[hW, finrank_top]`. Use linear arithmetic over natural numbers and integers. Take `⟨m, hm, hp0, hple⟩` from `exists_starProjection_ne_zero_norm_le_of_dualMinimum M hspan hl hdual (span ℝ (Set.range b)) (span ℤ (Set.range b)) hNM hNW hWtop`. Take `⟨z, hz, hzd⟩` from `hbd (m - (span ℝ (Set.range b))ᗮ.starProjection m) (hsubW _ m)`.

Establish `hzW : z ∈ span ℝ (Set.range b)`. Rewrite using `[← hNW]`. Conclude with `Submodule.subset_span hz`. Establish `hcnn : 0 ≤ (finrank ℝ E : ℝ) / l` using `div_nonneg (Nat.cast_nonneg _) hl.le`. Establish `hk1 : ((k : ℝ) + 1) ≤ (finrank ℝ E : ℝ)` using `by exact_mod_cast hk`.

Use `⟨Fin.snoc b (m - z), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.snoc_last]`. Conclude with `M.sub_mem hm (hNM hz)`.

Simplify using `only [Fin.snoc_castSucc]`. Conclude with `hbM j`. Rewrite using `[linearIndependent_fin_snoc]`. Use `⟨hbli, fun hmem => hp0 ?_⟩` and prove the remaining obligations. Establish `e : m = (m - z) + z` using `by abel`.

Rewrite using `[e, map_add, hPzero _ _ hmem, hPzero _ _ hzW, add_zero]`. Introduce `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.snoc_last]`. Establish `e : m - z = (span ℝ (Set.range b))ᗮ.starProjection m + ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z)` using `by abel`.

Establish `hin : ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) ∈ span ℝ (Set.range b)` using `Submodule.sub_mem _ (hsubW _ m) hzW`. Establish `hi : inner ℝ ((span ℝ (Set.range b))ᗮ.starProjection m) ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) = 0`. Rewrite using `[real_inner_comm]`. Conclude with `horth _ _ m hin`. Rewrite using `[e, norm_add_sq_eq_of_inner_eq_zero hi]`.

Establish `h2 : ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 ≤ ((finrank ℝ E : ℝ) / l) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hple 2`. Establish `hc2 : 0 ≤ ((finrank ℝ E : ℝ) / l) ^ 2` using `sq_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `hbn j`.

Introduce `w hw`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℝ).mp hw`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last]`. Establish `hu : ∑ j : Fin k, c j.castSucc • b j ∈ span ℝ (Set.range b)` using `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`.

Establish `hδ` using `abs_sub_round (c (Fin.last k))`. Establish `hv : ∑ j : Fin k, c j.castSucc • b j + (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) ∈ span ℝ (Set.range b)` using `Submodule.add_mem _ hu (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hsubW _ m) hzW))`. Take `⟨z'', hz'', hz''d⟩` from `hbd _ hv`. Establish `hmem_last : m - z ∈ span ℤ (Set.range (Fin.snoc b (m - z) : Fin (k + 1) → E))` using `Submodule.subset_span ⟨Fin.last k, by simp⟩`. Establish `hspan_le : span ℤ (Set.range b) ≤ span ℤ (Set.range (Fin.snoc b (m - z) : Fin (k + 1) → E))` using `Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨j.castSucc, by simp⟩)`.

Use `⟨(round (c (Fin.last k))) • (m - z) + z'', Submodule.add_mem _ (Submodule.smul_mem _ _ hmem_last) (hspan_le hz''), ?_⟩` and prove the remaining obligations. Establish `hdecomp : ∑ j : Fin k, c j.castSucc • b j + c (Fin.last k) • (m - z) - ((round (c (Fin.last k))) • (m - z) + z'') = (∑ j : Fin k, c j.castSucc • b j + (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) - z'') + (c (Fin.last k) - …`. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ]`. Simplify using `only [sub_smul, smul_sub]`. Normalize the expressions using the abelian group laws.

Establish `hz''W : z'' ∈ span ℝ (Set.range b)`. Rewrite using `[← hNW]`. Conclude with `Submodule.subset_span hz''`. Establish `hi : inner ℝ (∑ j : Fin k, c j.castSucc • b j + (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) - z'') ((c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • (span ℝ (Set.range b))ᗮ.starProjection m) = 0`. Rewrite using `[real_inner_smul_right, horth _ _ m (Submodule.sub_mem _ hv hz''W), mul_zero]`.

Rewrite using `[hdecomp, norm_add_sq_eq_of_inner_eq_zero hi, norm_smul, mul_pow, Real.norm_eq_abs]`. Establish `hδ2 : |c (Fin.last k) - (round (c (Fin.last k)) : ℝ)| ^ 2 ≤ 1 / 4`. Establish `h0` using `abs_nonneg (c (Fin.last k) - (round (c (Fin.last k)) : ℝ))`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 ≤ ((finrank ℝ E : ℝ) / l) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hple 2`.

Establish `hc2 : 0 ≤ ((finrank ℝ E : ℝ) / l) ^ 2` using `sq_nonneg _`. Establish `hp2 : 0 ≤ ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2` using `sq_nonneg _`. Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul hδ2 h2 hp2 (by norm_num : (0 : ℝ) ≤ 1 / 4)]`.
-/
theorem exists_short_linearIndependent_of_dualMinimum (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) {l : ℝ} (hl : 0 < l)
    (hdual : ∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) :
    ∀ k, k ≤ finrank ℝ E → ∃ b : Fin k → E, (∀ i, b i ∈ M) ∧ LinearIndependent ℝ b ∧
      (∀ i, ‖b i‖ ^ 2 ≤ (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2) ∧
      (∀ w ∈ span ℝ (Set.range b), ∃ z ∈ span ℤ (Set.range b),
        ‖w - z‖ ^ 2 ≤ (k : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2 / 4) := by
  classical
  have hPzero : ∀ (W : Submodule ℝ E), ∀ x ∈ W, Wᗮ.starProjection x = 0 := by
    intro W x hx
    have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := W) x
    rw [Submodule.starProjection_eq_self_iff.mpr hx] at h1
    simpa using h1
  have hsubW : ∀ (W : Submodule ℝ E) (m : E), m - Wᗮ.starProjection m ∈ W := by
    intro W m
    have h1 := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m
    rwa [Submodule.orthogonal_orthogonal] at h1
  have horth : ∀ (W : Submodule ℝ E) (u : E) (m : E), u ∈ W →
      inner ℝ u (Wᗮ.starProjection m) = 0 := by
    intro W u m hu
    exact Submodule.inner_right_of_mem_orthogonal hu (Submodule.starProjection_apply_mem _ _)
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩
    intro w hw
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    have hw0 : w = 0 := by simpa [Set.range_eq_empty] using hw
    subst hw0
    simp
  | succ k ih =>
    intro hk
    obtain ⟨b, hbM, hbli, hbn, hbd⟩ := ih (by omega)
    have hNM : span ℤ (Set.range b) ≤ M := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbM i)
    have hNW : span ℝ ((span ℤ (Set.range b) : Submodule ℤ E) : Set E) = span ℝ (Set.range b) :=
      Submodule.span_span_of_tower ℤ ℝ (Set.range b)
    have hWtop : span ℝ (Set.range b) ≠ ⊤ := by
      intro hW
      have h1 : finrank ℝ (span ℝ (Set.range b)) = k := by
        rw [finrank_span_eq_card hbli, Fintype.card_fin]
      rw [hW, finrank_top] at h1
      omega
    obtain ⟨m, hm, hp0, hple⟩ :=
      exists_starProjection_ne_zero_norm_le_of_dualMinimum M hspan hl hdual (span ℝ (Set.range b)) (span ℤ (Set.range b)) hNM hNW hWtop
    obtain ⟨z, hz, hzd⟩ := hbd (m - (span ℝ (Set.range b))ᗮ.starProjection m) (hsubW _ m)
    have hzW : z ∈ span ℝ (Set.range b) := by
      rw [← hNW]
      exact Submodule.subset_span hz
    have hcnn : 0 ≤ (finrank ℝ E : ℝ) / l := div_nonneg (Nat.cast_nonneg _) hl.le
    have hk1 : ((k : ℝ) + 1) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hk
    refine ⟨Fin.snoc b (m - z), ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        exact M.sub_mem hm (hNM hz)
      · simp only [Fin.snoc_castSucc]
        exact hbM j
    · rw [linearIndependent_fin_snoc]
      refine ⟨hbli, fun hmem => hp0 ?_⟩
      have e : m = (m - z) + z := by abel
      rw [e, map_add, hPzero _ _ hmem, hPzero _ _ hzW, add_zero]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        have e : m - z = (span ℝ (Set.range b))ᗮ.starProjection m +
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) := by abel
        have hin : ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) ∈ span ℝ (Set.range b) :=
          Submodule.sub_mem _ (hsubW _ m) hzW
        have hi : inner ℝ ((span ℝ (Set.range b))ᗮ.starProjection m)
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) = 0 := by
          rw [real_inner_comm]
          exact horth _ _ m hin
        rw [e, norm_add_sq_eq_of_inner_eq_zero hi]
        have h2 : ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hple 2
        have hc2 : 0 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 := sq_nonneg _
        nlinarith
      · simp only [Fin.snoc_castSucc]
        exact hbn j
    · intro w hw
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      have hu : ∑ j : Fin k, c j.castSucc • b j ∈ span ℝ (Set.range b) :=
        Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
      have hδ := abs_sub_round (c (Fin.last k))
      have hv : ∑ j : Fin k, c j.castSucc • b j +
          (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) ∈ span ℝ (Set.range b) :=
        Submodule.add_mem _ hu (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hsubW _ m) hzW))
      obtain ⟨z'', hz'', hz''d⟩ := hbd _ hv
      have hmem_last : m - z ∈ span ℤ (Set.range (Fin.snoc b (m - z) : Fin (k + 1) → E)) :=
        Submodule.subset_span ⟨Fin.last k, by simp⟩
      have hspan_le : span ℤ (Set.range b) ≤ span ℤ (Set.range (Fin.snoc b (m - z) : Fin (k + 1) → E)) :=
        Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨j.castSucc, by simp⟩)
      refine ⟨(round (c (Fin.last k))) • (m - z) + z'', Submodule.add_mem _
        (Submodule.smul_mem _ _ hmem_last) (hspan_le hz''), ?_⟩
      have hdecomp : ∑ j : Fin k, c j.castSucc • b j + c (Fin.last k) • (m - z) -
          ((round (c (Fin.last k))) • (m - z) + z'') =
          (∑ j : Fin k, c j.castSucc • b j +
            (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
              ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) - z'') +
          (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • (span ℝ (Set.range b))ᗮ.starProjection m := by
        rw [← Int.cast_smul_eq_zsmul ℝ]
        simp only [sub_smul, smul_sub]
        abel
      have hz''W : z'' ∈ span ℝ (Set.range b) := by
        rw [← hNW]
        exact Submodule.subset_span hz''
      have hi : inner ℝ (∑ j : Fin k, c j.castSucc • b j +
            (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
              ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) - z'')
          ((c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • (span ℝ (Set.range b))ᗮ.starProjection m) = 0 := by
        rw [real_inner_smul_right, horth _ _ m (Submodule.sub_mem _ hv hz''W), mul_zero]
      rw [hdecomp, norm_add_sq_eq_of_inner_eq_zero hi, norm_smul, mul_pow, Real.norm_eq_abs]
      have hδ2 : |c (Fin.last k) - (round (c (Fin.last k)) : ℝ)| ^ 2 ≤ 1 / 4 := by
        have h0 := abs_nonneg (c (Fin.last k) - (round (c (Fin.last k)) : ℝ))
        nlinarith
      have h2 : ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hple 2
      have hc2 : 0 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 := sq_nonneg _
      have hp2 : 0 ≤ ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 := sq_nonneg _
      push_cast
      nlinarith [mul_le_mul hδ2 h2 hp2 (by norm_num : (0 : ℝ) ≤ 1 / 4)]

/- English proof (translation)
Introduce `E _ _ _ M hMd hspan l hl hdual`. Use `haveI := hMd`. Take `⟨b, hbM, hbli, hbn, -⟩` from `exists_short_linearIndependent_of_dualMinimum M hspan hl hdual (finrank ℝ E) le_rfl`. Use `⟨b, hbM, hbli, fun i => ?_⟩` and prove the remaining obligations. Establish `hn0 : (0 : ℝ) < (finrank ℝ E : ℝ)` using `by exact_mod_cast Fin.pos i`.

Establish `h1 : ‖b i‖ ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l)`. Establish `h2` using `hbn i`. Establish `h3 : 0 ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l)` using `by positivity`. Establish `h4 : (Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l)) ^ 2 = (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2`. Rewrite using `[mul_pow, Real.sq_sqrt hn0.le]`.

Use polynomial arithmetic with `[norm_nonneg (b i)]`. Establish `h5 : (finrank ℝ E : ℝ) ^ ((3 : ℝ) / 2) = (finrank ℝ E : ℝ) * Real.sqrt (finrank ℝ E : ℝ)`. Rewrite using `[show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one, Real.sqrt_eq_rpow]`. Rewrite using `[h5]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem shortIndependentVectorsOfDualMinimum : ShortIndependentVectorsOfDualMinimum := by
  intro E _ _ _ M hMd hspan l hl hdual
  haveI := hMd
  obtain ⟨b, hbM, hbli, hbn, -⟩ := exists_short_linearIndependent_of_dualMinimum M hspan hl hdual (finrank ℝ E) le_rfl
  refine ⟨b, hbM, hbli, fun i => ?_⟩
  have hn0 : (0 : ℝ) < (finrank ℝ E : ℝ) := by exact_mod_cast Fin.pos i
  have h1 : ‖b i‖ ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := by
    have h2 := hbn i
    have h3 : 0 ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := by positivity
    have h4 : (Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l)) ^ 2 =
        (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn0.le]
    nlinarith [norm_nonneg (b i)]
  have h5 : (finrank ℝ E : ℝ) ^ ((3 : ℝ) / 2) = (finrank ℝ E : ℝ) * Real.sqrt (finrank ℝ E : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h5]
  calc ‖b i‖ ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := h1
    _ = (finrank ℝ E : ℝ) * Real.sqrt (finrank ℝ E : ℝ) / l := by ring

end Formalism.NormUnitaryCountingLemmas
