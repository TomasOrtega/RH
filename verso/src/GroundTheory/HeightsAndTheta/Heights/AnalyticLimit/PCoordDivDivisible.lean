import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

/- English proof (translation)
Distinguish the cases in `hzi : z i = 0`. Use `swap`. Establish `h` using `hFG z hz`. Rewrite `h` using `[hF z hz hzk]`. Conclude with `(mul_eq_zero.mp h.symm).resolve_left hzi`.

Use `set w : ℂ → (Fin D → ℂ) := fun ε => Function.update z i ε with hw`. Establish `hwc : Continuous w` using `continuous_const.update i continuous_id`. Establish `hw0 : w 0 = z` using `by rw [← hzi]; simp [hw]`. Establish `hcont : ContinuousAt (fun ε => G (w ε)) 0`. Establish `h` using `(hG z hz).continuousAt`.

Rewrite `h` using `[← hw0]`. Conclude with `h.comp hwc.continuousAt`. Establish `hmem : ∀ᶠ ε in 𝓝 (0 : ℂ), w ε ∈ Ω`. Conclude with `hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact hΩ.mem_nhds hz)`. Establish `hzero : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), G (w ε) = 0` using `by filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with ε hε hne`.

Establish `hwk : w ε k = 0` using `by simp [hw, hik, hzk]`. Establish `hwi : w ε i = ε` using `by simp [hw]`. Establish `h` using `hFG _ hε`. Rewrite `h` using `[hF _ hε hwk, hwi]`. Conclude with `(mul_eq_zero.mp h.symm).resolve_left hne`.

Establish `ht1 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (G (w 0)))` using `hcont.tendsto.mono_left nhdsWithin_le_nhds`. Establish `ht2 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 0)` using `tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)`. Establish `h` using `tendsto_nhds_unique ht1 ht2`. Rewrite `h` using `[hw0]`. Then use the resulting hypothesis.
-/
theorem cofactor_vanish {D : ℕ} {Ω : Set (Fin D → ℂ)} (hΩ : IsOpen Ω) {F G : (Fin D → ℂ) → ℂ}
    {i k : Fin D} (hik : k ≠ i) (hG : AnalyticOnNhd ℂ G Ω) (hFG : ∀ z ∈ Ω, F z = z i * G z)
    (hF : ∀ z ∈ Ω, z k = 0 → F z = 0) {z : Fin D → ℂ} (hz : z ∈ Ω) (hzk : z k = 0) : G z = 0 := by
  classical
  by_cases hzi : z i = 0
  swap
  · have h := hFG z hz
    rw [hF z hz hzk] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hzi

  set w : ℂ → (Fin D → ℂ) := fun ε => Function.update z i ε with hw
  have hwc : Continuous w := continuous_const.update i continuous_id
  have hw0 : w 0 = z := by rw [← hzi]; simp [hw]
  have hcont : ContinuousAt (fun ε => G (w ε)) 0 := by
    have h := (hG z hz).continuousAt
    rw [← hw0] at h
    exact h.comp hwc.continuousAt
  have hmem : ∀ᶠ ε in 𝓝 (0 : ℂ), w ε ∈ Ω := by
    exact hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact hΩ.mem_nhds hz)

  have hzero : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), G (w ε) = 0 := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with ε hε hne
    have hwk : w ε k = 0 := by simp [hw, hik, hzk]
    have hwi : w ε i = ε := by simp [hw]
    have h := hFG _ hε
    rw [hF _ hε hwk, hwi] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  have ht1 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (G (w 0))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)
  have h := tendsto_nhds_unique ht1 ht2
  rwa [hw0] at h

/- English proof (translation)
Introduce `D Ω F S hΩ hFa hF`. Proceed by induction on `S using Finset.induction_on generalizing F with`. Consider the case `empty => exact ⟨F, hFa, fun z _ => by simp⟩`. Consider the case `insert i S hi ih`. Take `⟨G₁, hG₁a, hG₁⟩` from `hH D Ω F i hΩ hFa fun z hz hzi => hF z hz ⟨i, Finset.mem_insert_self i S, hzi⟩`.

Establish `hG₁0 : ∀ z ∈ Ω, z ∈ coordDiv S → G₁ z = 0`. Introduce and unpack `z hz ⟨k, hk, hzk⟩`. Establish `hki : k ≠ i` using `fun h => hi (h ▸ hk)`. Conclude with `cofactor_vanish hΩ hki hG₁a hG₁ (fun y hy hyk => hF y hy ⟨k, Finset.mem_insert_of_mem hk, hyk⟩) hz hzk`. Take `⟨G, hGa, hG⟩` from `ih G₁ hG₁a hG₁0`.

Use `⟨G, hGa, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hG₁ z hz, hG z hz, Finset.prod_insert hi, mul_assoc]`.
-/
theorem CoordDivDivisible.proof (hH : HyperplaneDivisible.Statement) : CoordDivDivisible.Statement := by
  classical
  intro D Ω F S hΩ hFa hF
  induction S using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hFa, fun z _ => by simp⟩
  | insert i S hi ih =>
    obtain ⟨G₁, hG₁a, hG₁⟩ := hH D Ω F i hΩ hFa fun z hz hzi =>
      hF z hz ⟨i, Finset.mem_insert_self i S, hzi⟩
    have hG₁0 : ∀ z ∈ Ω, z ∈ coordDiv S → G₁ z = 0 := by
      rintro z hz ⟨k, hk, hzk⟩
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      exact cofactor_vanish hΩ hki hG₁a hG₁
        (fun y hy hyk => hF y hy ⟨k, Finset.mem_insert_of_mem hk, hyk⟩) hz hzk
    obtain ⟨G, hGa, hG⟩ := ih G₁ hG₁a hG₁0
    refine ⟨G, hGa, fun z hz => ?_⟩
    rw [hG₁ z hz, hG z hz, Finset.prod_insert hi, mul_assoc]

end GroundTheory.Heights₂.Heights.AnalyticLimit
