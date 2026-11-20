import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstIsRingHomOnBoundedStatement

open GlobalTheory.ConvSer Filter Topology

namespace GlobalTheory.ConvSer

/- English proof (translation)
Rewrite using `[NormedAddGroup.tendsto_nhds_zero]`. Introduce `ε hε`. Establish `h1 : Tendsto (fun b => C * ‖d b‖) cofinite (𝓝 0)`. Simplify using `using (tendsto_zero_iff_norm_tendsto_zero.1 hd).const_mul C`. Establish `h2 : {b | ¬ C * ‖d b‖ < ε}.Finite` using `eventually_cofinite.1 (h1.eventually (gt_mem_nhds hε))`.

Establish `h3 : ∀ b, {a | ¬ ‖c a b * d b‖ < ε}.Finite`. Introduce `b`. Establish `: Tendsto (fun a => c a b * d b) cofinite (𝓝 0)`. Simplify using `using (hc b).mul_const (d b)`. Conclude with `eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 this ε hε)`.

Rewrite using `[eventually_cofinite]`. Use `(h2.biUnion (t := fun b => (fun a => (a, b)) '' {a | ¬ ‖c a b * d b‖ < ε}) (fun b _ => (h3 b).image _)).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩ hp`. Simplify using `only [Set.mem_ofPred_eq] at hp`. Simplify using `only [Set.mem_iUnion]`.

Use `⟨b, ?_, a, hp, rfl⟩` and prove the remaining obligations. Introduce `hlt`. Apply `hp` to reduce the goal to its premises. Rewrite using `[norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hC a b) (norm_nonneg _)) hlt`.
-/
theorem tendsto_cofinite_double {K α β : Type*} [NormedField K] (c : α → β → K) (d : β → K)
    (C : ℝ) (hC : ∀ a b, ‖c a b‖ ≤ C) (hc : ∀ b, Tendsto (fun a => c a b) cofinite (𝓝 0))
    (hd : Tendsto d cofinite (𝓝 0)) :
    Tendsto (fun p : α × β => c p.1 p.2 * d p.2) cofinite (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have h1 : Tendsto (fun b => C * ‖d b‖) cofinite (𝓝 0) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hd).const_mul C
  have h2 : {b | ¬ C * ‖d b‖ < ε}.Finite :=
    eventually_cofinite.1 (h1.eventually (gt_mem_nhds hε))
  have h3 : ∀ b, {a | ¬ ‖c a b * d b‖ < ε}.Finite := by
    intro b
    have : Tendsto (fun a => c a b * d b) cofinite (𝓝 0) := by
      simpa using (hc b).mul_const (d b)
    exact eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 this ε hε)
  rw [eventually_cofinite]
  refine (h2.biUnion (t := fun b => (fun a => (a, b)) '' {a | ¬ ‖c a b * d b‖ < ε})
    (fun b _ => (h3 b).image _)).subset ?_
  rintro ⟨a, b⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  simp only [Set.mem_iUnion]
  refine ⟨b, ?_, a, hp, rfl⟩
  intro hlt
  apply hp
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hC a b) (norm_nonneg _)) hlt

/- English proof (translation)
Take `⟨hI, hB, hP, hC, -⟩` from `GlobalTheory.BddAlg.bdd_alg K σ`. Use `set c := MvPowerSeries.constantCoeff u with hc`. Establish `hCi : Intg (MvPowerSeries.C c : MvPowerSeries σ K)` using `(hC c).2.1 hu.2.le`. Establish `h1 : Intg (u - MvPowerSeries.C c)` using `(hI _ _ hu.1 hCi).2.1`. Establish `hb1 : Bdd (u - MvPowerSeries.C c)` using `(hP _ 0).2.2 h1`.

Establish `hbu : Bdd u` using `(hP _ 0).2.2 hu.1`. Establish `h2 : Small (csub t (u - MvPowerSeries.C c))` using `(GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hb1).2.2.2 h1 (by simp [hc])`. Take `⟨hR, hRC, -⟩` from `GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht`. Establish `h3 : csub t u = csub t (u - MvPowerSeries.C c) + MvPowerSeries.C c`. Rewrite using `[(hR _ _ hbu (hC c).1).2.1, hRC]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨(GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hbu).2.2.1 hu.1, ?_⟩` and prove the remaining obligations. Rewrite using `[h3, map_add, MvPowerSeries.constantCoeff_C]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2.2 hu.2)`.
-/
theorem small_csub_of_small (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ τ : Type) [Fintype σ] (t : σ → MvPowerSeries τ K) (ht : ∀ i, Small (t i))
    (u : MvPowerSeries σ K) (hu : Small u) : Small (csub t u) := by
  obtain ⟨hI, hB, hP, hC, -⟩ := GlobalTheory.BddAlg.bdd_alg K σ
  set c := MvPowerSeries.constantCoeff u with hc
  have hCi : Intg (MvPowerSeries.C c : MvPowerSeries σ K) := (hC c).2.1 hu.2.le
  have h1 : Intg (u - MvPowerSeries.C c) := (hI _ _ hu.1 hCi).2.1
  have hb1 : Bdd (u - MvPowerSeries.C c) := (hP _ 0).2.2 h1
  have hbu : Bdd u := (hP _ 0).2.2 hu.1
  have h2 : Small (csub t (u - MvPowerSeries.C c)) :=
    (GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hb1).2.2.2 h1 (by simp [hc])
  obtain ⟨hR, hRC, -⟩ := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht
  have h3 : csub t u = csub t (u - MvPowerSeries.C c) + MvPowerSeries.C c := by
    rw [(hR _ _ hbu (hC c).1).2.1, hRC]; ring
  refine ⟨(GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hbu).2.2.1 hu.1, ?_⟩
  rw [h3, map_add, MvPowerSeries.constantCoeff_C]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2.2 hu.2)

/- English proof (translation)
Introduce `K _ _ _ ρ σ τ _ _ s t S hs ht hS`. Establish `hst : ∀ j, Small (csub t (s j))` using `fun j => small_csub_of_small K σ τ t ht _ (hs j)`. Use `⟨hst, ?_⟩` and prove the remaining obligations. Take `⟨hI, hB, hP, hC, -, hF, -⟩` from `GlobalTheory.BddAlg.bdd_alg K σ`. Take `⟨-, -, -, hRP, hRF, -⟩` from `GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht`.

Establish `hint : ∀ ν : ρ →₀ ℕ, Intg (∏ j, s j ^ ν j)` using `fun ν => ((hF ρ Finset.univ _).1 fun j _ => (hP _ _).1 (hs j).1).1`. Establish `hbd : ∀ ν : ρ →₀ ℕ, Bdd (∏ j, s j ^ ν j)` using `fun ν => (hP _ 0).2.2 (hint ν)`. Establish `hprod : ∀ ν : ρ →₀ ℕ, csub t (∏ j, s j ^ ν j) = ∏ j, csub t (s j) ^ ν j`. Introduce `ν`. Rewrite using `[hRF ρ Finset.univ _ fun j _ => (hP _ 0).2.2 ((hP _ _).1 (hs j).1)]`.

Conclude with `Finset.prod_congr rfl fun j _ => hRP _ _ ((hP _ 0).2.2 (hs j).1)`. Use extensionality with `μ`. Take `⟨C, hCS⟩` from `id hS`. Set `c : (ρ →₀ ℕ) → (σ →₀ ℕ) → K` to `fun ν l => MvPowerSeries.coeff ν S * MvPowerSeries.coeff l (∏ j, s j ^ ν j)`. Set `d : (σ →₀ ℕ) → K` to `fun l => MvPowerSeries.coeff μ (∏ i, t i ^ l i)`.

Establish `hcs : ∀ l, HasSum (fun ν => c ν l) (MvPowerSeries.coeff l (csub s S))` using `(GlobalTheory.ConvSer.csub_hasSum_and_bounds K ρ σ s S hs hS).1`. Establish `hd : Tendsto d cofinite (𝓝 0)`. Set `U : MvPowerSeries σ K` to `fun _ => 1`. Establish `hU : ∀ l, MvPowerSeries.coeff l U = 1` using `fun _ => rfl`. Use `((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t U ht ⟨1, fun l => by simp [hU]⟩).1 μ).summable.tendsto_cofinite_zero` as an intermediate fact.

Simplify `this` using `only [hU, one_mul]`. Establish `hsum : Summable (fun p : (ρ →₀ ℕ) × (σ →₀ ℕ) => c p.1 p.2 * d p.2)`. Apply `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` to reduce the goal to its premises. Use `tendsto_cofinite_double c d C ?_ (fun l => (hcs l).summable.tendsto_cofinite_zero) hd` and prove the remaining obligations. Introduce `ν l`.

Simplify using `only [c, norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (hint ν l)).trans (hCS ν)`. Establish `hA : HasSum (fun ν : ρ →₀ ℕ => MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ j, csub t (s j) ^ ν j)) (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2)`. Use `hsum.hasSum.prod_fiberwise fun ν => ?_` and prove the remaining obligations. Rewrite using `[← hprod]`.

Use `((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht (hbd ν)).1 μ).mul_left (MvPowerSeries.coeff ν S)` as an intermediate fact. Simplify `this` using `only [c, d, mul_assoc]`. Establish `hB' : HasSum (fun l : σ →₀ ℕ => MvPowerSeries.coeff l (csub s S) * d l) (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2)`. Use `((Equiv.prodComm _ _).hasSum_iff.2 hsum.hasSum).prod_fiberwise fun l => ?_` and prove the remaining obligations. Conclude with `(hcs l).mul_right (d l)`.

Conclude with `hB'.tsum_eq.trans hA.tsum_eq.symm`.
-/
theorem csub_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K)
    (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) →
    (∀ i, Small (t i)) → Bdd S →
    (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  intro K _ _ _ ρ σ τ _ _ s t S hs ht hS
  have hst : ∀ j, Small (csub t (s j)) := fun j => small_csub_of_small K σ τ t ht _ (hs j)
  refine ⟨hst, ?_⟩
  obtain ⟨hI, hB, hP, hC, -, hF, -⟩ := GlobalTheory.BddAlg.bdd_alg K σ
  obtain ⟨-, -, -, hRP, hRF, -⟩ := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht
  have hint : ∀ ν : ρ →₀ ℕ, Intg (∏ j, s j ^ ν j) := fun ν =>
    ((hF ρ Finset.univ _).1 fun j _ => (hP _ _).1 (hs j).1).1
  have hbd : ∀ ν : ρ →₀ ℕ, Bdd (∏ j, s j ^ ν j) := fun ν => (hP _ 0).2.2 (hint ν)
  have hprod : ∀ ν : ρ →₀ ℕ, csub t (∏ j, s j ^ ν j) = ∏ j, csub t (s j) ^ ν j := by
    intro ν
    rw [hRF ρ Finset.univ _ fun j _ => (hP _ 0).2.2 ((hP _ _).1 (hs j).1)]
    exact Finset.prod_congr rfl fun j _ => hRP _ _ ((hP _ 0).2.2 (hs j).1)
  ext μ
  obtain ⟨C, hCS⟩ := id hS
  let c : (ρ →₀ ℕ) → (σ →₀ ℕ) → K := fun ν l =>
    MvPowerSeries.coeff ν S * MvPowerSeries.coeff l (∏ j, s j ^ ν j)
  let d : (σ →₀ ℕ) → K := fun l => MvPowerSeries.coeff μ (∏ i, t i ^ l i)
  have hcs : ∀ l, HasSum (fun ν => c ν l) (MvPowerSeries.coeff l (csub s S)) :=
    (GlobalTheory.ConvSer.csub_hasSum_and_bounds K ρ σ s S hs hS).1
  have hd : Tendsto d cofinite (𝓝 0) := by
    let U : MvPowerSeries σ K := fun _ => 1
    have hU : ∀ l, MvPowerSeries.coeff l U = 1 := fun _ => rfl
    have := ((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t U ht ⟨1, fun l => by simp [hU]⟩).1 μ).summable.tendsto_cofinite_zero
    simpa only [hU, one_mul] using this
  have hsum : Summable (fun p : (ρ →₀ ℕ) × (σ →₀ ℕ) => c p.1 p.2 * d p.2) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    refine tendsto_cofinite_double c d C ?_ (fun l => (hcs l).summable.tendsto_cofinite_zero) hd
    intro ν l
    simp only [c, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hint ν l)).trans (hCS ν)
  have hA : HasSum (fun ν : ρ →₀ ℕ => MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ j, csub t (s j) ^ ν j))
      (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2) := by
    refine hsum.hasSum.prod_fiberwise fun ν => ?_
    rw [← hprod]
    have := ((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht (hbd ν)).1 μ).mul_left (MvPowerSeries.coeff ν S)
    simpa only [c, d, mul_assoc] using this
  have hB' : HasSum (fun l : σ →₀ ℕ => MvPowerSeries.coeff l (csub s S) * d l)
      (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2) := by
    refine ((Equiv.prodComm _ _).hasSum_iff.2 hsum.hasSum).prod_fiberwise fun l => ?_
    exact (hcs l).mul_right (d l)
  exact hB'.tsum_eq.trans hA.tsum_eq.symm

end GlobalTheory.ConvSer
