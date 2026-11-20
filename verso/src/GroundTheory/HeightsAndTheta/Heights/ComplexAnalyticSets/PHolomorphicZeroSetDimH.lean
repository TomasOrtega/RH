import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicZeroSetDimH
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticImplicitChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperHolomorphicSurjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter
open scoped ENNReal NNReal

noncomputable section

namespace HolomorphicZeroSetDimH

def partialDeriv {k : ℕ} (h : (Fin k → ℂ) → ℂ) (n : ℕ) (m : Fin n → Fin k) (v : Fin k → ℂ) : ℂ :=
  iteratedFDeriv ℂ n h v (fun j => Pi.basisFun ℂ (Fin k) (m j))

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Take `⟨x, hx, hall⟩` from `exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (not_le.1 hlt)`. Take `⟨N, hN, hc⟩` from `hS x hx`. Conclude with `(not_le.2 (hall _ (inter_mem_nhdsWithin S hN))) hc`.
-/
theorem dimH_le_of_local {X : Type*} [EMetricSpace X] [SecondCountableTopology X] {S : Set X}
    {c : ℝ≥0∞} (hS : ∀ x ∈ S, ∃ N ∈ 𝓝 x, dimH (S ∩ N) ≤ c) : dimH S ≤ c := by
  by_contra hlt
  obtain ⟨x, hx, hall⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (not_le.1 hlt)
  obtain ⟨N, hN, hc⟩ := hS x hx
  exact (not_le.2 (hall _ (inter_mem_nhdsWithin S hN))) hc

/- English proof (translation)
Use `(dimH_image_le_of_locally_lipschitzOn fun y hy => ?_).trans ?_` and prove the remaining obligations. Take `⟨K, t, ht, hK⟩` from `((hg y hy).contDiffAt (n := 1)).exists_lipschitzOnWith`. Conclude with `⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩`. Establish `hfin : Module.finrank ℝ (Fin d → ℂ) = 2 * d`. Rewrite using `[Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem dimH_image_le_of_analyticOnNhd {d : ℕ} {σ : Type*} [Fintype σ] {O : Set (Fin d → ℂ)}
    {g : (Fin d → ℂ) → σ → ℂ} (hg : AnalyticOnNhd ℂ g O) : dimH (g '' O) ≤ 2 * (d : ℝ≥0∞) := by
  refine (dimH_image_le_of_locally_lipschitzOn fun y hy => ?_).trans ?_
  · obtain ⟨K, t, ht, hK⟩ := ((hg y hy).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  · have hfin : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
      rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    calc dimH O ≤ dimH (Set.univ : Set (Fin d → ℂ)) := dimH_mono (Set.subset_univ _)
      _ = Module.finrank ℝ (Fin d → ℂ) := Real.dimH_univ_eq_finrank _
      _ = 2 * (d : ℝ≥0∞) := by rw [hfin]; push_cast; ring

/- English proof (translation)
Use `dimH_le_of_local fun p hp => ?_` and prove the remaining obligations. Take `⟨d, A, O, V, φ, hd, hO, hV, hpV, -, hφ, -, hZ⟩` from `AnalyticImplicitChart.proof (Fin k) (Fin 1) (fun _ => g) p Set.univ (fun _ => hg p hp.1) (fun _ => hp.2.1) (linearIndependent_unique_iff.2 hp.2.2) univ_mem`. Use `⟨V, hV.mem_nhds hpV, ?_⟩` and prove the remaining obligations. Establish `hk : k - 1 = d` using `by simp only [Fintype.card_fin] at hd; omega`. Rewrite using `[hk]`.

Use `(dimH_mono ?_).trans (dimH_image_le_of_analyticOnNhd hφ)` and prove the remaining obligations. Rewrite using `[← hZ]`. Introduce and unpack `z ⟨hz, hzV⟩`. Conclude with `⟨hzV, fun _ => hz.2.1⟩`.
-/
theorem dimH_regular_zeros_le {k : ℕ} {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g U) :
    dimH {v | v ∈ U ∧ g v = 0 ∧ fderiv ℂ g v ≠ 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
  refine dimH_le_of_local fun p hp => ?_
  obtain ⟨d, A, O, V, φ, hd, hO, hV, hpV, -, hφ, -, hZ⟩ :=
    AnalyticImplicitChart.proof (Fin k) (Fin 1) (fun _ => g) p Set.univ (fun _ => hg p hp.1)
      (fun _ => hp.2.1) (linearIndependent_unique_iff.2 hp.2.2) univ_mem
  refine ⟨V, hV.mem_nhds hpV, ?_⟩
  have hk : k - 1 = d := by simp only [Fintype.card_fin] at hd; omega
  rw [hk]
  refine (dimH_mono ?_).trans (dimH_image_le_of_analyticOnNhd hφ)
  rw [← hZ]
  rintro z ⟨hz, hzV⟩
  exact ⟨hzV, fun _ => hz.2.1⟩

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hdiff : ∀ n, DifferentiableAt ℂ (iteratedFDeriv ℂ n h) v` using `fun n => ((hh.iteratedFDeriv n) v hv).differentiableAt`. Establish `hall : ∀ n m, partialDeriv h n m v = 0`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro m`. Simplify using `[partialDeriv, iteratedFDeriv_zero_apply, h0]`. Consider the case `succ n ih`. Introduce `m`.

Establish `h1` using `hcon n (Fin.tail m) (ih _)`. Establish `h2` using `congrArg (fun L => L (Pi.basisFun ℂ (Fin k) (m 0))) h1`. Simplify using `only [zero_apply] at h2`. Unfold `partialDeriv at h2 ⊢`. Rewrite `h2` using `[fderiv_continuousMultilinear_apply_const_apply (hdiff n)]`.

Rewrite using `[iteratedFDeriv_succ_apply_left]`. Conclude with `h2`. Establish `hzero : ∀ n, iteratedFDeriv ℂ n h v = 0` using `fun n => ContinuousMultilinearMap.toMultilinearMap_injective (Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin k)) fun m => by`. Simplify `hall n m)` using `[partialDeriv]`. Take `⟨p, r, hp⟩` from `hh v hv`.

Establish `hev : ∀ᶠ x in 𝓝 v, h x = 0`. Establish `h1 : Tendsto (fun x => x - v) (𝓝 v) (𝓝 0)`. Simplify using `using (continuous_sub_right v).tendsto v`. Use `filter_upwards [h1.eventually (Metric.eball_mem_nhds 0 hp.r_pos)] with x hx`. Establish `hs` using `hp.hasSum_iteratedFDeriv hx`.

Simplify using `only [hzero, zero_apply, smul_zero, add_sub_cancel] at hs`. Conclude with `hs.unique hasSum_zero`. Take `⟨W, hWsub, hWo, hvW⟩` from `_root_.mem_nhds_iff.1 (hev.and (hU.mem_nhds hv))`. Take `⟨w, hw, hw0⟩` from `hW W (fun x hx => (hWsub hx).2) hWo ⟨v, hvW⟩`. Conclude with `hw0 (hWsub hw).1`.
-/
theorem exists_partialDeriv {k : ℕ} {U : Set (Fin k → ℂ)} {h : (Fin k → ℂ) → ℂ} (hU : IsOpen U)
    (hh : AnalyticOnNhd ℂ h U) (hW : ∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0)
    {v : Fin k → ℂ} (hv : v ∈ U) (h0 : h v = 0) :
    ∃ n m, partialDeriv h n m v = 0 ∧ fderiv ℂ (partialDeriv h n m) v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdiff : ∀ n, DifferentiableAt ℂ (iteratedFDeriv ℂ n h) v := fun n =>
    ((hh.iteratedFDeriv n) v hv).differentiableAt
  have hall : ∀ n m, partialDeriv h n m v = 0 := by
    intro n
    induction n with
    | zero => intro m; simp [partialDeriv, iteratedFDeriv_zero_apply, h0]
    | succ n ih =>
      intro m
      have h1 := hcon n (Fin.tail m) (ih _)
      have h2 := congrArg (fun L => L (Pi.basisFun ℂ (Fin k) (m 0))) h1
      simp only [zero_apply] at h2
      unfold partialDeriv at h2 ⊢
      rw [fderiv_continuousMultilinear_apply_const_apply (hdiff n)] at h2
      rw [iteratedFDeriv_succ_apply_left]
      exact h2
  have hzero : ∀ n, iteratedFDeriv ℂ n h v = 0 := fun n =>
    ContinuousMultilinearMap.toMultilinearMap_injective
      (Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin k)) fun m => by
        simpa [partialDeriv] using hall n m)
  obtain ⟨p, r, hp⟩ := hh v hv
  have hev : ∀ᶠ x in 𝓝 v, h x = 0 := by
    have h1 : Tendsto (fun x => x - v) (𝓝 v) (𝓝 0) := by
      simpa using (continuous_sub_right v).tendsto v
    filter_upwards [h1.eventually (Metric.eball_mem_nhds 0 hp.r_pos)] with x hx
    have hs := hp.hasSum_iteratedFDeriv hx
    simp only [hzero, zero_apply, smul_zero, add_sub_cancel] at hs
    exact hs.unique hasSum_zero
  obtain ⟨W, hWsub, hWo, hvW⟩ := _root_.mem_nhds_iff.1 (hev.and (hU.mem_nhds hv))
  obtain ⟨w, hw, hw0⟩ := hW W (fun x hx => (hWsub hx).2) hWo ⟨v, hvW⟩
  exact hw0 (hWsub hw).1

/- English proof (translation)
Introduce `k U h hU hh hW`. Establish `ha : AnalyticOnNhd ℂ h U` using `analyticOnNhd_pi_iff.1 (ProperHolomorphicSurjective.analyticOnNhd_of_differentiableOn (m := 1) (f := fun v _ => h v) hU (differentiableOn_pi.2 fun _ => hh)) 0`. Establish `hpd : ∀ n m, AnalyticOnNhd ℂ (partialDeriv h n m) U` using `fun n m x hx => ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Fin k → ℂ) ℂ (fun j => Pi.basisFun ℂ (Fin k) (m j))).analyticAt _).comp (ha.iteratedFDeriv n x hx)`. Combine the equalities or inequalities in the displayed calculation. Use `dimH_mono fun v hv => ?_` and prove the remaining obligations.

Take `⟨n, m, h1, h2⟩` from `exists_partialDeriv hU ha hW hv.1 hv.2`. Conclude with `Set.mem_iUnion.2 ⟨⟨n, m⟩, hv.1, h1, h2⟩`. Use `_ ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by`. Rewrite using `[dimH_iUnion]`. Conclude with `iSup_le fun nm => dimH_regular_zeros_le (hpd nm.1 nm.2)`.
-/
theorem proof : HolomorphicZeroSetDimH.Statement := by
  intro k U h hU hh hW
  have ha : AnalyticOnNhd ℂ h U :=
    analyticOnNhd_pi_iff.1 (ProperHolomorphicSurjective.analyticOnNhd_of_differentiableOn (m := 1)
      (f := fun v _ => h v) hU (differentiableOn_pi.2 fun _ => hh)) 0
  have hpd : ∀ n m, AnalyticOnNhd ℂ (partialDeriv h n m) U := fun n m x hx =>
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Fin k → ℂ) ℂ
      (fun j => Pi.basisFun ℂ (Fin k) (m j))).analyticAt _).comp (ha.iteratedFDeriv n x hx)
  calc dimH {v | v ∈ U ∧ h v = 0}
      ≤ dimH (⋃ nm : (Σ n, Fin n → Fin k),
          {v | v ∈ U ∧ partialDeriv h nm.1 nm.2 v = 0 ∧ fderiv ℂ (partialDeriv h nm.1 nm.2) v ≠ 0}) := by
        refine dimH_mono fun v hv => ?_
        obtain ⟨n, m, h1, h2⟩ := exists_partialDeriv hU ha hW hv.1 hv.2
        exact Set.mem_iUnion.2 ⟨⟨n, m⟩, hv.1, h1, h2⟩
    _ ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
        rw [dimH_iUnion]
        exact iSup_le fun nm => dimH_regular_zeros_le (hpd nm.1 nm.2)

end HolomorphicZeroSetDimH

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
