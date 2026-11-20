import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `ε hε`. Establish `hδpos : 0 < ε / 4` using `by positivity`. Take `⟨U, hU, hUeq⟩` from `heq (ε / 4) hδpos`. Take `⟨C, hCc, hCB, hCt⟩` from `htail (ε / 4) hδpos`. Take `⟨t, htC, hCcov⟩` from `hCc.elim_nhds_subcover (fun x => (fun h => x⁻¹ * h) ⁻¹' U) (by`.

Introduce `x _`. Establish `hc : Continuous (fun h : G => x⁻¹ * h)` using `continuous_const.mul continuous_id`. Apply `hc.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using hU)`. Set `T : (G → ℂ) → (t → ℂ)` to `fun φ i => φ i`.

Establish `hTb : T '' Φ ⊆ Metric.closedBall 0 1`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Rewrite using `[mem_closedBall_zero_iff]`. Use `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_` and prove the remaining obligations. Conclude with `hbd φ hφ i (hCB (htC i i.2))`.

Establish `htb : TotallyBounded (T '' Φ)` using `((isCompact_closedBall (0 : t → ℂ) 1).totallyBounded).subset hTb`. Take `⟨s, hsT, hsf, hscov⟩` from `Metric.finite_approx_of_totallyBounded htb (ε / 4) hδpos`. Set `c : (t → ℂ) → (G → ℂ)` to `fun y => if h : ∃ φ ∈ Φ, T φ = y then h.choose else 0`. Establish `hc : ∀ y ∈ s, c y ∈ Φ ∧ T (c y) = y`. Introduce `y hy`.

Establish `h : ∃ φ ∈ Φ, T φ = y` using `hsT hy`. Simplify using `only [c, dif_pos h]`. Conclude with `h.choose_spec`. Use `⟨hsf.toFinset.image c, fun φ hφ => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨y, hy, hdist⟩ : ∃ y ∈ s, dist (T φ) y < ε / 4 := by`.

Use `hscov ⟨φ, hφ, rfl⟩` as an intermediate fact. Simplify using `using this`. Take `⟨hψ, hTψ⟩` from `hc y hy`. Use `⟨c y, Finset.mem_image.2 ⟨y, hsf.mem_toFinset.2 hy, rfl⟩, fun g hg => ?_⟩` and prove the remaining obligations. Break down `hCt g hg with ⟨s', hs', hsg⟩ | hsmall` into its components or cases.

Choose the witnesses or unpack the hypotheses as in `⟨x, hxt, hxU⟩ : ∃ x ∈ t, x⁻¹ * (s' * g) ∈ U := by`. Use `hCcov hsg` as an intermediate fact. Simplify using `using this`. Establish `hxB : x ∈ B` using `hCB (htC x hxt)`. Establish `hmul : x * (x⁻¹ * (s' * g)) = s' * g` using `mul_inv_cancel_left x _`.

Establish `hsgB : s' * g ∈ B` using `hCB hsg`. Establish `h1` using `hUeq φ hφ x hxB _ hxU (by rw [hmul]; exact hsgB)`. Establish `h2` using `hUeq (c y) hψ x hxB _ hxU (by rw [hmul]; exact hsgB)`. Rewrite `h1`, `h2` using `[hmul]`. Establish `h3 : ‖φ x - c y x‖ ≤ ε / 4`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hinv φ hφ s' hs' g, ← hinv (c y) hψ s' hs' g]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(norm_sub_le _ _).trans (by linarith [hsmall φ hφ, hsmall (c y) hψ])`.
-/
theorem totallyBounded_sup_of_equicontinuous_tails
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G)
    (Φ : Set (G → ℂ))
    (hinv : ∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g)
    (hbd : ∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B →
      ‖φ (g * u) - φ g‖ ≤ ε)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧
      ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  classical
  intro ε hε
  have hδpos : 0 < ε / 4 := by positivity
  obtain ⟨U, hU, hUeq⟩ := heq (ε / 4) hδpos
  obtain ⟨C, hCc, hCB, hCt⟩ := htail (ε / 4) hδpos
  obtain ⟨t, htC, hCcov⟩ := hCc.elim_nhds_subcover (fun x => (fun h => x⁻¹ * h) ⁻¹' U) (by
    intro x _
    have hc : Continuous (fun h : G => x⁻¹ * h) := continuous_const.mul continuous_id
    apply hc.continuousAt.preimage_mem_nhds
    simpa using hU)
  let T : (G → ℂ) → (t → ℂ) := fun φ i => φ i
  have hTb : T '' Φ ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    exact hbd φ hφ i (hCB (htC i i.2))
  have htb : TotallyBounded (T '' Φ) :=
    ((isCompact_closedBall (0 : t → ℂ) 1).totallyBounded).subset hTb
  obtain ⟨s, hsT, hsf, hscov⟩ := Metric.finite_approx_of_totallyBounded htb (ε / 4) hδpos
  let c : (t → ℂ) → (G → ℂ) := fun y => if h : ∃ φ ∈ Φ, T φ = y then h.choose else 0
  have hc : ∀ y ∈ s, c y ∈ Φ ∧ T (c y) = y := by
    intro y hy
    have h : ∃ φ ∈ Φ, T φ = y := hsT hy
    simp only [c, dif_pos h]
    exact h.choose_spec
  refine ⟨hsf.toFinset.image c, fun φ hφ => ?_⟩
  obtain ⟨y, hy, hdist⟩ : ∃ y ∈ s, dist (T φ) y < ε / 4 := by
    have := hscov ⟨φ, hφ, rfl⟩
    simpa using this
  obtain ⟨hψ, hTψ⟩ := hc y hy
  refine ⟨c y, Finset.mem_image.2 ⟨y, hsf.mem_toFinset.2 hy, rfl⟩, fun g hg => ?_⟩
  rcases hCt g hg with ⟨s', hs', hsg⟩ | hsmall
  · obtain ⟨x, hxt, hxU⟩ : ∃ x ∈ t, x⁻¹ * (s' * g) ∈ U := by
      have := hCcov hsg
      simpa using this
    have hxB : x ∈ B := hCB (htC x hxt)
    have hmul : x * (x⁻¹ * (s' * g)) = s' * g := mul_inv_cancel_left x _
    have hsgB : s' * g ∈ B := hCB hsg
    have h1 := hUeq φ hφ x hxB _ hxU (by rw [hmul]; exact hsgB)
    have h2 := hUeq (c y) hψ x hxB _ hxU (by rw [hmul]; exact hsgB)
    rw [hmul] at h1 h2
    have h3 : ‖φ x - c y x‖ ≤ ε / 4 := by
      calc ‖φ x - c y x‖ = dist (T φ ⟨x, hxt⟩) (T (c y) ⟨x, hxt⟩) := (dist_eq_norm _ _).symm
        _ ≤ dist (T φ) (T (c y)) := dist_le_pi_dist _ _ _
        _ = dist (T φ) y := by rw [hTψ]
        _ ≤ ε / 4 := hdist.le
    rw [← hinv φ hφ s' hs' g, ← hinv (c y) hψ s' hs' g]
    calc ‖φ (s' * g) - c y (s' * g)‖
        = ‖(φ (s' * g) - φ x) + (φ x - c y x) - (c y (s' * g) - c y x)‖ := by congr 1; ring
      _ ≤ ‖φ (s' * g) - φ x‖ + ‖φ x - c y x‖ + ‖c y (s' * g) - c y x‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
      _ ≤ ε := by linarith
  · exact (norm_sub_le _ _).trans (by linarith [hsmall φ hφ, hsmall (c y) hψ])

end GlobalTheory
