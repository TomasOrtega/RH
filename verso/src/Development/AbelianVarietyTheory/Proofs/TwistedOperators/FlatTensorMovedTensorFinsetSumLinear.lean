import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand

open MeasureTheory GlobalTheory.FunObj

namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

/- English proof (translation)
Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Establish `hint : ∀ i ∈ S, Integrable (flatIntegrand hs ψ (moved G keep g (T i)) X Y) (varsVol G ν)`. Introduce `i hi`. Unfold `varsVol`. Conclude with `(continuous_flatIntegrand hs hψ (hT i hi) keep g X Y).integrable_of_hasCompactSupport (hasCompactSupport_flatIntegrand hs ψ (hT i hi) keep g X Y)`.

Establish `h : ∀ v, flatIntegrand hs ψ (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y v = ∑ i ∈ S, x i * flatIntegrand hs ψ (moved G keep g (T i)) X Y v`. Introduce `v`. Simplify using `only [flatIntegrand, moved, GlobalTheory.SplitFlip.Grid.pathAct, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Simplify using `only [flatTensor, h]`.

Rewrite using `[integral_finset_sum _ fun i hi => (hint i hi).const_mul _]`. Simplify using `only [integral_const_mul]`.
-/
theorem flatTensor_moved_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s)
    (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : Continuous ψ) (ϖ : kˣ) (e : ℕ) (keep : Bool)
    (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ)
    (hT : ∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) (X : ColArgs G) (Y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y =
      ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hint : ∀ i ∈ S, Integrable (flatIntegrand hs ψ (moved G keep g (T i)) X Y) (varsVol G ν) := by
    intro i hi
    unfold varsVol
    exact (continuous_flatIntegrand hs hψ (hT i hi) keep g X Y).integrable_of_hasCompactSupport
      (hasCompactSupport_flatIntegrand hs ψ (hT i hi) keep g X Y)
  have h : ∀ v, flatIntegrand hs ψ (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y v =
      ∑ i ∈ S, x i * flatIntegrand hs ψ (moved G keep g (T i)) X Y v := by
    intro v
    simp only [flatIntegrand, moved, GlobalTheory.SplitFlip.Grid.pathAct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [flatTensor, h]
  rw [integral_finset_sum _ fun i hi => (hint i hi).const_mul _]
  simp only [integral_const_mul]

end GlobalTheory.FunObj
