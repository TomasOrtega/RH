import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt

/- English proof (translation)
Introduce `K _ J _ T Bd hT hcl hBdT hscale hloc`. Take `⟨A, hA⟩ : ∃ A : Set ((Σ k, J k) → ℂ), A = (⋂ p, {w | ‖w p‖ ≤ 1}) ∩ ⋂ k, ⋃ i, {w | ‖w ⟨k, i⟩‖ = 1}` from `⟨_, rfl⟩`. Establish `hAcl : IsClosed A`. Rewrite using `[hA]`. Conclude with `(isClosed_iInter fun p => isClosed_le (continuous_norm.comp (continuous_apply p)) continuous_const).inter (isClosed_iInter fun k => isClosed_iUnion_of_finite fun i => isClosed_eq (continuous_norm.comp (continuous_apply _)) continuous_const)`.

Establish `hA_le : ∀ w ∈ A, ∀ p, ‖w p‖ ≤ 1`. Introduce `w hw p`. Rewrite `hw` using `[hA]`. Conclude with `Set.mem_iInter.mp hw.1 p`. Establish `hA_ne : ∀ w ∈ A, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0`.

Introduce `w hw k`. Rewrite `hw` using `[hA]`. Take `⟨i, hi⟩` from `Set.mem_iUnion.mp (Set.mem_iInter.mp hw.2 k)`. Use `⟨i, fun h0 => ?_⟩` and prove the remaining obligations. Establish `hi' : ‖w ⟨k, i⟩‖ = 1` using `hi`.

Rewrite `hi'` using `[h0, norm_zero]`. Conclude with `zero_ne_one hi'`. Establish `hScl : IsClosed (T ∩ A)`. Apply `isClosed_of_closure_subset` to reduce the goal to its premises. Introduce `w hw`.

Establish `hwT : w ∈ closure T` using `closure_mono Set.inter_subset_left hw`. Establish `hwA : w ∈ A` using `hAcl.closure_subset (closure_mono Set.inter_subset_right hw)`. Conclude with `⟨hcl w hwT (hA_ne w hwA), hwA⟩`. Establish `hSsub : T ∩ A ⊆ Metric.closedBall 0 1`. Introduce `w hw`.

Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]`. Conclude with `hA_le w hw.2`. Establish `hScpt : IsCompact (T ∩ A)` using `(isCompact_closedBall 0 1).of_isClosed_subset hScl hSsub`. Use `choose N hN C hC using fun w (hw : w ∈ T ∩ A) => hloc w hw.1`. Take `⟨t, ht⟩` from `hScpt.elim_nhds_subcover' N hN`.

Use `⟨∑ s ∈ t, |C s.1 s.2|, ?_⟩` and prove the remaining obligations. Introduce `w x hBd`. Establish `hwT` using `hBdT w x hBd`. Establish `hmax : ∀ k, ∃ i, ∀ j, ‖w ⟨k, j⟩‖ ≤ ‖w ⟨k, i⟩‖`. Introduce `k`.

Take `⟨i₀, -⟩` from `hT w hwT k`. Use `haveI : Nonempty (J k) := ⟨i₀⟩`. Conclude with `Finite.exists_max fun j => ‖w ⟨k, j⟩‖`. Use `choose m hm using hmax`. Establish `hmpos : ∀ k, 0 < ‖w ⟨k, m k⟩‖`.

Introduce `k`. Take `⟨i₀, hi₀⟩` from `hT w hwT k`. Conclude with `lt_of_lt_of_le (norm_pos_iff.mpr hi₀) (hm k i₀)`. Take `⟨c, hc⟩ : ∃ c : K → ℂ, c = fun k => ((‖w ⟨k, m k⟩‖⁻¹ : ℝ) : ℂ)` from `⟨_, rfl⟩`. Establish `hc0 : ∀ k, c k ≠ 0`.

Introduce `k`. Rewrite using `[hc]`. Conclude with `Complex.ofReal_ne_zero.mpr (inv_ne_zero (hmpos k).ne')`. Establish `hBd'` using `hscale w x c hc0 hBd`. Establish `hnorm : ∀ (k : K) (j : J k), ‖c k * w ⟨k, j⟩‖ = ‖w ⟨k, j⟩‖ / ‖w ⟨k, m k⟩‖`.

Introduce `k j`. Rewrite using `[hc, norm_mul, Complex.norm_real, norm_inv, norm_norm, div_eq_inv_mul]`. Establish `hw'S : (fun p => c p.1 * w p) ∈ T ∩ A`. Use `⟨hBdT _ _ hBd', ?_⟩` and prove the remaining obligations. Rewrite using `[hA]`.

Use `⟨Set.mem_iInter.mpr fun p => ?_, Set.mem_iInter.mpr fun k => Set.mem_iUnion.mpr ⟨m k, ?_⟩⟩` and prove the remaining obligations. Take `⟨k, j⟩` from `p show ‖c k * w ⟨k, j⟩‖ ≤ 1`. Rewrite using `[hnorm]`. Conclude with `(div_le_one (hmpos k)).mpr (hm k j)`. Use `show ‖c k * w ⟨k, m k⟩‖ = 1`.

Rewrite using `[hnorm]`. Conclude with `div_self (hmpos k).ne'`. Take `⟨s, hs, hsN⟩` from `Set.mem_iUnion₂.mp (ht hw'S)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bound_of_local_bounds_of_blockScale :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (T : Set ((Σ k, J k) → ℂ))
    (Bd : ((Σ k, J k) → ℂ) → ℝ → Prop),
    (∀ w ∈ T, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ w ∈ closure T, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → w ∈ T) →
    (∀ w x, Bd w x → w ∈ T) →
    (∀ w x (c : K → ℂ), (∀ k, c k ≠ 0) → Bd w x → Bd (fun p => c p.1 * w p) x) →
    (∀ w₀ ∈ T, ∃ N ∈ 𝓝 w₀, ∃ C : ℝ, ∀ w ∈ N, ∀ x, Bd w x → |x| ≤ C) →
    ∃ C : ℝ, ∀ w x, Bd w x → |x| ≤ C := by
  intro K _ J _ T Bd hT hcl hBdT hscale hloc
  classical
  obtain ⟨A, hA⟩ : ∃ A : Set ((Σ k, J k) → ℂ),
      A = (⋂ p, {w | ‖w p‖ ≤ 1}) ∩ ⋂ k, ⋃ i, {w | ‖w ⟨k, i⟩‖ = 1} := ⟨_, rfl⟩
  have hAcl : IsClosed A := by
    rw [hA]
    exact (isClosed_iInter fun p => isClosed_le (continuous_norm.comp (continuous_apply p))
      continuous_const).inter (isClosed_iInter fun k => isClosed_iUnion_of_finite fun i =>
        isClosed_eq (continuous_norm.comp (continuous_apply _)) continuous_const)
  have hA_le : ∀ w ∈ A, ∀ p, ‖w p‖ ≤ 1 := by
    intro w hw p
    rw [hA] at hw
    exact Set.mem_iInter.mp hw.1 p
  have hA_ne : ∀ w ∈ A, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
    intro w hw k
    rw [hA] at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hw.2 k)
    refine ⟨i, fun h0 => ?_⟩
    have hi' : ‖w ⟨k, i⟩‖ = 1 := hi
    rw [h0, norm_zero] at hi'
    exact zero_ne_one hi'
  have hScl : IsClosed (T ∩ A) := by
    apply isClosed_of_closure_subset
    intro w hw
    have hwT : w ∈ closure T := closure_mono Set.inter_subset_left hw
    have hwA : w ∈ A := hAcl.closure_subset (closure_mono Set.inter_subset_right hw)
    exact ⟨hcl w hwT (hA_ne w hwA), hwA⟩
  have hSsub : T ∩ A ⊆ Metric.closedBall 0 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact hA_le w hw.2
  have hScpt : IsCompact (T ∩ A) := (isCompact_closedBall 0 1).of_isClosed_subset hScl hSsub
  choose N hN C hC using fun w (hw : w ∈ T ∩ A) => hloc w hw.1
  obtain ⟨t, ht⟩ := hScpt.elim_nhds_subcover' N hN
  refine ⟨∑ s ∈ t, |C s.1 s.2|, ?_⟩
  intro w x hBd
  have hwT := hBdT w x hBd
  have hmax : ∀ k, ∃ i, ∀ j, ‖w ⟨k, j⟩‖ ≤ ‖w ⟨k, i⟩‖ := by
    intro k
    obtain ⟨i₀, -⟩ := hT w hwT k
    haveI : Nonempty (J k) := ⟨i₀⟩
    exact Finite.exists_max fun j => ‖w ⟨k, j⟩‖
  choose m hm using hmax
  have hmpos : ∀ k, 0 < ‖w ⟨k, m k⟩‖ := by
    intro k
    obtain ⟨i₀, hi₀⟩ := hT w hwT k
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi₀) (hm k i₀)
  obtain ⟨c, hc⟩ : ∃ c : K → ℂ, c = fun k => ((‖w ⟨k, m k⟩‖⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k
    rw [hc]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (hmpos k).ne')
  have hBd' := hscale w x c hc0 hBd
  have hnorm : ∀ (k : K) (j : J k), ‖c k * w ⟨k, j⟩‖ = ‖w ⟨k, j⟩‖ / ‖w ⟨k, m k⟩‖ := by
    intro k j
    rw [hc, norm_mul, Complex.norm_real, norm_inv, norm_norm, div_eq_inv_mul]
  have hw'S : (fun p => c p.1 * w p) ∈ T ∩ A := by
    refine ⟨hBdT _ _ hBd', ?_⟩
    rw [hA]
    refine ⟨Set.mem_iInter.mpr fun p => ?_, Set.mem_iInter.mpr fun k => Set.mem_iUnion.mpr ⟨m k, ?_⟩⟩
    · obtain ⟨k, j⟩ := p
      show ‖c k * w ⟨k, j⟩‖ ≤ 1
      rw [hnorm]
      exact (div_le_one (hmpos k)).mpr (hm k j)
    · show ‖c k * w ⟨k, m k⟩‖ = 1
      rw [hnorm]
      exact div_self (hmpos k).ne'
  obtain ⟨s, hs, hsN⟩ := Set.mem_iUnion₂.mp (ht hw'S)
  calc |x| ≤ C s.1 s.2 := hC s.1 s.2 _ hsN x hBd'
    _ ≤ |C s.1 s.2| := le_abs_self _
    _ ≤ ∑ s ∈ t, |C s.1 s.2| :=
      Finset.single_le_sum (f := fun s : ↥(T ∩ A) => |C s.1 s.2|) (fun _ _ => abs_nonneg _) hs

end GlobalTheory.CompanionTheory.Ar.RootHt
