import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeakClosed

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use extensionality with `m`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, letπ, map_add, map_sum, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk, Finset.sum_ite_eq, Finset.mem_range]`. Distinguish the cases in `hk : m < k`. Simplify using `[hk, Nat.not_le.2 hk]`.

Simplify using `[hk, Nat.le_of_not_lt hk, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]`.
-/
theorem tailDecomp {O : Type} [CommRing O] {n : ℕ} (k : ℕ) (a : LetA O n) :
    a = (∑ j ∈ Finset.range k, fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j) +
      (letπ : LetA O n) ^ k * (fun i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (a i)) := by
  funext i
  ext m
  simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, letπ, map_add, map_sum,
    PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    Finset.sum_ite_eq, Finset.mem_range]
  by_cases hk : m < k
  · simp [hk, Nat.not_le.2 hk]
  · simp [hk, Nat.le_of_not_lt hk, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `a₀`. Rewrite using `[ContinuousAt, ← tendsto_sub_nhds_zero_iff]`. Introduce `U hU`. Take `⟨V, hV, hVV⟩` from `exists_nhds_zero_half hU`.

Take `⟨k, hk⟩` from `hsmall V hV`. Set `mono : ℕ → LetA O n → M` to `fun j a => Φ (fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j)`. Establish `hcont : ∀ j, Continuous (mono j)` using `fun j => (hmono j).comp (continuous_pi fun i => (PowerSeries.WithPiTopology.continuous_coeff O j).comp (continuous_apply i))`. Set `S : LetA O n → M` to `fun a => ∑ j ∈ Finset.range k, (mono j a - mono j a₀)`. Establish `hS : Continuous S` using `continuous_finset_sum _ fun j _ => (hcont j).sub continuous_const`.

Establish `hS0 : S a₀ = 0` using `by simp [S]`. Establish `hSV : ∀ᶠ a in 𝓝 a₀, S a ∈ V`. Use `hS.continuousAt (x := a₀)` as an intermediate fact. Rewrite `this` using `[ContinuousAt, hS0]`. Conclude with `this hV`.

Rewrite using `[Filter.mem_map]`. Use `filter_upwards [hSV] with a ha`. Set `tl : LetA O n → LetA O n` to `fun b i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (b i)`. Establish `hΦ : ∀ b, Φ b = (∑ j ∈ Finset.range k, mono j b) + Φ (letπ ^ k * tl b)`. Introduce `b`.

Use `conv_lhs => rw [tailDecomp k b]`. Rewrite using `[map_add, map_sum]`. Establish `: Φ a - Φ a₀ = S a + Φ (letπ ^ k * (tl a - tl a₀))`. Rewrite using `[hΦ a, hΦ a₀, mul_sub, map_sub]`. Simplify using `only [S, Finset.sum_sub_distrib]`.

Normalize the expressions using the abelian group laws. Use `show Φ a - Φ a₀ ∈ U`. Rewrite using `[this]`. Conclude with `hVV _ ha _ (hk _)`.
-/
theorem continuous_of_tail {O : Type} [CommRing O] [TopologicalSpace O] {n : ℕ} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] (Φ : LetA O n →+ M)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ r : LetA O n, Φ (letπ ^ k * r) ∈ U)
    (hmono : ∀ j : ℕ, Continuous fun c : ZMod n → O => Φ (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) :
    Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro a₀
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half hU
  obtain ⟨k, hk⟩ := hsmall V hV
  let mono : ℕ → LetA O n → M := fun j a =>
    Φ (fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j)
  have hcont : ∀ j, Continuous (mono j) := fun j =>
    (hmono j).comp (continuous_pi fun i =>
      (PowerSeries.WithPiTopology.continuous_coeff O j).comp (continuous_apply i))
  let S : LetA O n → M := fun a => ∑ j ∈ Finset.range k, (mono j a - mono j a₀)
  have hS : Continuous S := continuous_finset_sum _ fun j _ => (hcont j).sub continuous_const
  have hS0 : S a₀ = 0 := by simp [S]
  have hSV : ∀ᶠ a in 𝓝 a₀, S a ∈ V := by
    have := hS.continuousAt (x := a₀)
    rw [ContinuousAt, hS0] at this
    exact this hV
  rw [Filter.mem_map]
  filter_upwards [hSV] with a ha
  let tl : LetA O n → LetA O n := fun b i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (b i)
  have hΦ : ∀ b, Φ b = (∑ j ∈ Finset.range k, mono j b) + Φ (letπ ^ k * tl b) := by
    intro b
    conv_lhs => rw [tailDecomp k b]
    rw [map_add, map_sum]
  have : Φ a - Φ a₀ = S a + Φ (letπ ^ k * (tl a - tl a₀)) := by
    rw [hΦ a, hΦ a₀, mul_sub, map_sub]
    simp only [S, Finset.sum_sub_distrib]
    abel
  show Φ a - Φ a₀ ∈ U
  rw [this]
  exact hVV _ ha _ (hk _)

end GlobalTheory.WeakClosed
