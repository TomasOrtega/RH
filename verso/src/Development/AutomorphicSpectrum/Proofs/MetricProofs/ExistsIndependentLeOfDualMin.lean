import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Formalism.NormUnitaryBounds.NormUnitary

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

/- English proof (translation)
Introduce `V _ _ _ L _ _ μ hμ hdual`. Use `set n := Module.finrank ℝ V with hn`. Use `set c : ℝ := (n : ℝ) / μ with hc`. Establish `hc0 : 0 ≤ c` using `div_nonneg (Nat.cast_nonneg _) hμ.le`. Establish `hspan : Submodule.span ℝ (L : Set V) = ⊤` using `IsZLattice.span_top`.

Establish `main : ∀ k, k ≤ n → ∃ b : Fin k → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧ (∀ i, ‖b i‖ ^ 2 ≤ n * c ^ 2) ∧ (∀ w ∈ Submodule.span ℝ (Set.range b), ∃ z ∈ Submodule.span ℤ (Set.range b), ‖w - z‖ ^ 2 ≤ k * c ^ 2 / 4)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`.

Use `⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Establish `hw0 : w = 0`. Rewrite `hw` using `[Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot]`.

Conclude with `hw`. Simplify using `[hw0]`. Consider the case `succ k ih`. Introduce `hk`. Take `⟨b, hbL, hbli, hbn, hcov⟩` from `ih (by omega)`.

Use `set W := Submodule.span ℝ (Set.range b) with hW`. Use `set N := Submodule.span ℤ (Set.range b) with hN`. Establish `hNL : N ≤ L` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)`. Establish `hNW : Submodule.span ℝ (N : Set V) = W` using `Submodule.span_span_of_tower ℤ ℝ (Set.range b)`. Establish `hWtop : W ≠ ⊤`.

Introduce `h`. Establish `h1 : Module.finrank ℝ W = k` using `by rw [hW, finrank_span_eq_card hbli, Fintype.card_fin]`. Rewrite `h1` using `[h, finrank_top]`. Use linear arithmetic over natural numbers and integers. Establish `hNsubW : ∀ y ∈ N, y ∈ W` using `fun y hy => by rw [← hNW]; exact Submodule.subset_span hy`.

Take `⟨m, hmL, hp0, hpn⟩` from `Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum L hspan hμ hdual W N hNL hNW hWtop`. Use `set p := Wᗮ.starProjection m with hp`. Establish `hpW : p ∈ Wᗮ` using `Wᗮ.starProjection_apply_mem m`. Establish `hwW : m - p ∈ W`. Use `Wᗮ.sub_starProjection_mem_orthogonal m` as an intermediate fact.

Rewrite `this` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Take `⟨z, hzN, hz⟩` from `hcov (m - p) hwW`. Establish `hzW : z ∈ W` using `hNsubW z hzN`. Use `set v := m - z with hv`. Establish `hvdec : v = (m - p - z) + p` using `by rw [hv]; abel`.

Establish `hvL : v ∈ L` using `L.sub_mem hmL (hNL hzN)`. Establish `hp2 : ‖p‖ ^ 2 ≤ c ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hpn 2`. Establish `pyth : ∀ a ∈ W, ∀ q ∈ Wᗮ, ‖a + q‖ ^ 2 = ‖a‖ ^ 2 + ‖q‖ ^ 2`. Introduce `a ha q hq`. Establish `h0 : ⟪a, q⟫_ℝ = 0` using `Submodule.inner_right_of_mem_orthogonal ha hq`.

Rewrite using `[sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_real h0]`. Establish `hvW : v ∉ W`. Introduce `h`. Apply `hp0` to reduce the goal to its premises. Establish `hmW : m ∈ W`.

Establish `e : m = v + z` using `by rw [hv]; abel`. Rewrite using `[e]`. Conclude with `W.add_mem h hzW`. Establish `hm' : m ∈ Wᗮᗮ` using `by rwa [Submodule.orthogonal_orthogonal]`. Conclude with `Wᗮ.starProjection_apply_eq_zero_iff.mpr hm'`.

Establish `hsub : m - p - z ∈ W` using `W.sub_mem hwW hzW`. Use `⟨Fin.cons v b, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hvL`.

Simplify using `using hbL j`. Conclude with `linearIndependent_finCons.mpr ⟨hbli, hvW⟩`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`.

Rewrite using `[hvdec, pyth _ hsub _ hpW]`. Establish `hkn : (k : ℝ) + 1 ≤ n` using `by exact_mod_cast hk`. Use polynomial arithmetic with `[sq_nonneg c, mul_le_mul_of_nonneg_right hkn (sq_nonneg c)]`. Simplify using `using hbn j`. Introduce `w' hw'`.

Rewrite `hw'` using `[Fin.range_cons, Submodule.mem_span_insert]`. Take `⟨t, u, hu, rfl⟩` from `hw'`. Use `set s := t - round t with hs`. Establish `hs2 : s ^ 2 ≤ 1 / 4`. Establish `h` using `abs_sub_round t`.

Rewrite `h` using `[← hs]`. Use polynomial arithmetic with `[abs_nonneg s, sq_abs s]`. Establish `hq : s • (m - p - z) + u ∈ W` using `W.add_mem (W.smul_mem _ hsub) hu`. Take `⟨z', hz'N, hz'⟩` from `hcov (s • (m - p - z) + u) hq`. Use `⟨(round t : ℤ) • v + z', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.range_cons, Submodule.mem_span_insert]`. Conclude with `⟨round t, z', hz'N, rfl⟩`. Establish `e : t • v + u - ((round t : ℤ) • v + z') = (s • (m - p - z) + u - z') + s • p`. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ, hs, hvdec]`. Use `module`.

Rewrite using `[e, pyth _ (W.sub_mem hq (hNsubW z' hz'N)) _ (Wᗮ.smul_mem _ hpW), norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]`. Establish `h4` using `mul_le_mul hs2 hp2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)`. Use `push_cast`. Use polynomial arithmetic with `[h4, hz']`. Take `⟨b, hbL, hbli, hbn, -⟩` from `main n le_rfl`.

Use `⟨b, hbL, hbli, fun i => ?_⟩` and prove the remaining obligations. Establish `hnR : (0 : ℝ) < n` using `by exact_mod_cast i.pos`. Establish `key : (n : ℝ) ^ (3 / 2 : ℝ) / μ = Real.sqrt (n * c ^ 2)`. Rewrite using `[Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc0, hc, Real.sqrt_eq_rpow, ← mul_div_assoc, ← Real.rpow_add_one hnR.ne']`. Evaluate the numerical expressions.

Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_independent_le_of_dual_min :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (μ : ℝ), 0 < μ →
      (∀ y : V, y ≠ 0 → (∀ x ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) → μ ≤ ‖y‖) →
      ∃ b : Fin (Module.finrank ℝ V) → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
        ∀ i, ‖b i‖ ≤ (Module.finrank ℝ V : ℝ) ^ (3 / 2 : ℝ) / μ := by
  intro V _ _ _ L _ _ μ hμ hdual
  set n := Module.finrank ℝ V with hn
  set c : ℝ := (n : ℝ) / μ with hc
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hμ.le
  have hspan : Submodule.span ℝ (L : Set V) = ⊤ := IsZLattice.span_top
  have main : ∀ k, k ≤ n → ∃ b : Fin k → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
      (∀ i, ‖b i‖ ^ 2 ≤ n * c ^ 2) ∧
      (∀ w ∈ Submodule.span ℝ (Set.range b), ∃ z ∈ Submodule.span ℤ (Set.range b),
        ‖w - z‖ ^ 2 ≤ k * c ^ 2 / 4) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩
      intro w hw
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hw0 : w = 0 := by
        rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hw
        exact hw
      simp [hw0]
    | succ k ih =>
      intro hk
      obtain ⟨b, hbL, hbli, hbn, hcov⟩ := ih (by omega)
      set W := Submodule.span ℝ (Set.range b) with hW
      set N := Submodule.span ℤ (Set.range b) with hN
      have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
      have hNW : Submodule.span ℝ (N : Set V) = W := Submodule.span_span_of_tower ℤ ℝ (Set.range b)
      have hWtop : W ≠ ⊤ := by
        intro h
        have h1 : Module.finrank ℝ W = k := by rw [hW, finrank_span_eq_card hbli, Fintype.card_fin]
        rw [h, finrank_top] at h1
        omega
      have hNsubW : ∀ y ∈ N, y ∈ W := fun y hy => by rw [← hNW]; exact Submodule.subset_span hy
      obtain ⟨m, hmL, hp0, hpn⟩ := Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum L hspan hμ hdual W N hNL hNW hWtop
      set p := Wᗮ.starProjection m with hp
      have hpW : p ∈ Wᗮ := Wᗮ.starProjection_apply_mem m
      have hwW : m - p ∈ W := by
        have := Wᗮ.sub_starProjection_mem_orthogonal m
        rwa [Submodule.orthogonal_orthogonal] at this
      obtain ⟨z, hzN, hz⟩ := hcov (m - p) hwW
      have hzW : z ∈ W := hNsubW z hzN
      set v := m - z with hv
      have hvdec : v = (m - p - z) + p := by rw [hv]; abel
      have hvL : v ∈ L := L.sub_mem hmL (hNL hzN)
      have hp2 : ‖p‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpn 2
      have pyth : ∀ a ∈ W, ∀ q ∈ Wᗮ, ‖a + q‖ ^ 2 = ‖a‖ ^ 2 + ‖q‖ ^ 2 := by
        intro a ha q hq
        have h0 : ⟪a, q⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal ha hq
        rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_real h0]
      have hvW : v ∉ W := by
        intro h
        apply hp0
        have hmW : m ∈ W := by
          have e : m = v + z := by rw [hv]; abel
          rw [e]
          exact W.add_mem h hzW
        have hm' : m ∈ Wᗮᗮ := by rwa [Submodule.orthogonal_orthogonal]
        exact Wᗮ.starProjection_apply_eq_zero_iff.mpr hm'
      have hsub : m - p - z ∈ W := W.sub_mem hwW hzW
      refine ⟨Fin.cons v b, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hvL
        · simpa using hbL j
      · exact linearIndependent_finCons.mpr ⟨hbli, hvW⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          rw [hvdec, pyth _ hsub _ hpW]
          have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
          nlinarith [sq_nonneg c, mul_le_mul_of_nonneg_right hkn (sq_nonneg c)]
        · simpa using hbn j
      · intro w' hw'
        rw [Fin.range_cons, Submodule.mem_span_insert] at hw'
        obtain ⟨t, u, hu, rfl⟩ := hw'
        set s := t - round t with hs
        have hs2 : s ^ 2 ≤ 1 / 4 := by
          have h := abs_sub_round t
          rw [← hs] at h
          nlinarith [abs_nonneg s, sq_abs s]
        have hq : s • (m - p - z) + u ∈ W := W.add_mem (W.smul_mem _ hsub) hu
        obtain ⟨z', hz'N, hz'⟩ := hcov (s • (m - p - z) + u) hq
        refine ⟨(round t : ℤ) • v + z', ?_, ?_⟩
        · rw [Fin.range_cons, Submodule.mem_span_insert]
          exact ⟨round t, z', hz'N, rfl⟩
        · have e : t • v + u - ((round t : ℤ) • v + z') = (s • (m - p - z) + u - z') + s • p := by
            rw [← Int.cast_smul_eq_zsmul ℝ, hs, hvdec]
            module
          rw [e, pyth _ (W.sub_mem hq (hNsubW z' hz'N)) _ (Wᗮ.smul_mem _ hpW), norm_smul,
            mul_pow, Real.norm_eq_abs, sq_abs]
          have h4 := mul_le_mul hs2 hp2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
          push_cast
          nlinarith [h4, hz']
  obtain ⟨b, hbL, hbli, hbn, -⟩ := main n le_rfl
  refine ⟨b, hbL, hbli, fun i => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast i.pos
  have key : (n : ℝ) ^ (3 / 2 : ℝ) / μ = Real.sqrt (n * c ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc0, hc, Real.sqrt_eq_rpow, ← mul_div_assoc,
      ← Real.rpow_add_one hnR.ne']
    norm_num
  rw [key]
  calc ‖b i‖ = Real.sqrt (‖b i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (hbn i)

end GlobalTheory.CompanionTheory.Ar.Cusp
