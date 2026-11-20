import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.LocConstTensor

/- English proof (translation)
Establish `hfin : (T '' K).Finite`. Use `letI : TopologicalSpace V := ⊥`. Use `haveI : DiscreteTopology V := ⟨rfl⟩`. Conclude with `(hK.image hT.continuous).finite_of_discrete`. Set `S : Finset V` to `hfin.toFinset.erase 0`.

Set `e : Fin S.card ≃ S` to `S.equivFin.symm`. Establish `hmem : ∀ w : V, w ≠ 0 → (fun y => if T y = w then (1 : ℂ) else 0) ∈ SB Z`. Introduce `w hw`. Use `⟨hT.comp (fun u => if u = w then (1 : ℂ) else 0), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro hK ?_` and prove the remaining obligations.

Introduce `y hy`. Rewrite using `[h0 y hy, if_neg (Ne.symm hw)]`. Use `⟨S.card, fun i => (e i : V), fun i => ⟨_, hmem (e i) (Finset.ne_of_mem_erase (e i).2)⟩, fun y => ?_⟩` and prove the remaining obligations. Establish `h1 : ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V) = ∑ w ∈ S, (if T y = w then (1 : ℂ) else 0) • w`. Rewrite using `[← Finset.sum_coe_sort S]`.

Conclude with `Equiv.sum_comp e (fun w : S => (if T y = (w : V) then (1 : ℂ) else 0) • (w : V))`. Express the relevant statement in the definitionally equal form `T y = ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)`. Rewrite using `[h1]`. Simplify using `only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Apply `h` to reduce the goal to its premises. Use `Finset.mem_erase.2 ⟨hne, hfin.mem_toFinset.2 ⟨y, ?_, rfl⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hy`.

Conclude with `hne (h0 y hy)`.
-/
theorem exists_sum (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V]
    [Module ℂ V] (T : Z → V) (hT : IsLocallyConstant T) (K : Set Z) (hK : IsCompact K)
    (h0 : ∀ y, y ∉ K → T y = 0) :
    ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  classical
  have hfin : (T '' K).Finite := by
    letI : TopologicalSpace V := ⊥
    haveI : DiscreteTopology V := ⟨rfl⟩
    exact (hK.image hT.continuous).finite_of_discrete
  let S : Finset V := hfin.toFinset.erase 0
  let e : Fin S.card ≃ S := S.equivFin.symm
  have hmem : ∀ w : V, w ≠ 0 → (fun y => if T y = w then (1 : ℂ) else 0) ∈ SB Z := by
    intro w hw
    refine ⟨hT.comp (fun u => if u = w then (1 : ℂ) else 0), ?_⟩
    refine HasCompactSupport.intro hK ?_
    intro y hy
    rw [h0 y hy, if_neg (Ne.symm hw)]
  refine ⟨S.card, fun i => (e i : V),
    fun i => ⟨_, hmem (e i) (Finset.ne_of_mem_erase (e i).2)⟩, fun y => ?_⟩
  have h1 : ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
      = ∑ w ∈ S, (if T y = w then (1 : ℂ) else 0) • w := by
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp e (fun w : S => (if T y = (w : V) then (1 : ℂ) else 0) • (w : V))
  change T y = ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
  rw [h1]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    refine Finset.mem_erase.2 ⟨hne, hfin.mem_toFinset.2 ⟨y, ?_, rfl⟩⟩
    by_contra hy
    exact hne (h0 y hy)

end GlobalTheory.LocConstTensor
