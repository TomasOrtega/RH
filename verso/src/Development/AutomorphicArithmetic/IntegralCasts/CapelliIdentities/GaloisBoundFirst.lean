import Mathlib

open Filter Topology in
/- English proof (translation)
Introduce and unpack `B hB ⟨z0, hz0⟩ a`. Establish `han : AnalyticOnNhd ℂ B Set.univ` using `hB.differentiableOn.analyticOnNhd isOpen_univ`. Establish `hnot : ¬ ∀ᶠ z in 𝓝 a, B z = 0` using `fun h => hz0 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h (Set.mem_univ z0))`. Take `⟨k, g, hg, hga, hev⟩` from `(AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (han a (Set.mem_univ a))).2 hnot`. Establish `hev' : ∀ᶠ z in 𝓝 a, z ≠ a → B z / (z - a) ^ k = g z` using `by filter_upwards [hev] with z hz hne`.

Establish `h0 : (z - a) ^ k ≠ 0` using `pow_ne_zero _ (sub_ne_zero.2 hne)`. Rewrite using `[hz, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Set `v : ℂ → ℂ` to `fun z => if z = a then g a else B z / (z - a) ^ k`. Establish `hva : v a = g a` using `by simp [v]`.

Establish `hvne : ∀ z, z ≠ a → v z = B z / (z - a) ^ k` using `fun z hz => by simp [v, hz]`. Use `⟨k, v, ?_, by rwa [hva], ?_⟩` and prove the remaining obligations. Introduce `z`. Distinguish the cases in `hz : z = a`. Substitute `hz` using the available equality.

Establish `: v =ᶠ[𝓝 z] g` using `by filter_upwards [hev'] with w hw`. Distinguish the cases in `hwz : w = z`. Rewrite using `[hwz, hva]`. Rewrite using `[hvne w hwz, hw hwz]`. Conclude with `(hg.differentiableAt.congr_of_eventuallyEq this)`.

Establish `hd : DifferentiableAt ℂ (fun w => B w / (w - a) ^ k) z` using `(hB z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow k) (pow_ne_zero _ (sub_ne_zero.2 hz))`. Establish `: v =ᶠ[𝓝 z] fun w => B w / (w - a) ^ k` using `by filter_upwards [isOpen_ne.mem_nhds hz] with w hw`. Conclude with `hvne w hw`. Conclude with `hd.congr_of_eventuallyEq this`. Introduce `z`.

Distinguish the cases in `hz : z = a`. Substitute `hz` using the available equality. Establish `hB0 : B z = (z - z) ^ k * g z`. Simplify `hev.self_of_nhds` using `[smul_eq_mul]`. Rewrite using `[hva]`.

Conclude with `hB0`. Rewrite using `[hvne z hz]`. Establish `h0 : (z - a) ^ k ≠ 0` using `pow_ne_zero _ (sub_ne_zero.2 hz)`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.Reformulated.B.GaloisBoundFirst.main :
    ∀ (B : ℂ → ℂ),
      Differentiable ℂ B →
        (∃ (z : ℂ), B z ≠ (0 : ℂ)) →
          ∀ (a : ℂ), ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ (0 : ℂ) ∧ ∀ (z : ℂ), B z = (z - a) ^ k * v z := by
  rintro B hB ⟨z0, hz0⟩ a
  have han : AnalyticOnNhd ℂ B Set.univ := hB.differentiableOn.analyticOnNhd isOpen_univ
  have hnot : ¬ ∀ᶠ z in 𝓝 a, B z = 0 := fun h => hz0
    (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
      (Set.mem_univ z0))
  obtain ⟨k, g, hg, hga, hev⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (han a (Set.mem_univ a))).2 hnot
  have hev' : ∀ᶠ z in 𝓝 a, z ≠ a → B z / (z - a) ^ k = g z := by
    filter_upwards [hev] with z hz hne
    have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    rw [hz, smul_eq_mul]
    field_simp
  let v : ℂ → ℂ := fun z => if z = a then g a else B z / (z - a) ^ k
  have hva : v a = g a := by simp [v]
  have hvne : ∀ z, z ≠ a → v z = B z / (z - a) ^ k := fun z hz => by simp [v, hz]
  refine ⟨k, v, ?_, by rwa [hva], ?_⟩
  · intro z
    by_cases hz : z = a
    · subst hz
      have : v =ᶠ[𝓝 z] g := by
        filter_upwards [hev'] with w hw
        by_cases hwz : w = z
        · rw [hwz, hva]
        · rw [hvne w hwz, hw hwz]
      exact (hg.differentiableAt.congr_of_eventuallyEq this)
    · have hd : DifferentiableAt ℂ (fun w => B w / (w - a) ^ k) z :=
        (hB z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow k)
          (pow_ne_zero _ (sub_ne_zero.2 hz))
      have : v =ᶠ[𝓝 z] fun w => B w / (w - a) ^ k := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        exact hvne w hw
      exact hd.congr_of_eventuallyEq this
  · intro z
    by_cases hz : z = a
    · subst hz
      have hB0 : B z = (z - z) ^ k * g z := by
        simpa [smul_eq_mul] using hev.self_of_nhds
      rw [hva]; exact hB0
    · rw [hvne z hz]
      have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
      field_simp
