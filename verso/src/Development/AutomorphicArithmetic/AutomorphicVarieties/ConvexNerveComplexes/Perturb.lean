import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `E Y _ _ q hq h hh k hk`. Establish `hh' : ∀ y, 1 ≤ q y h` using `hh`. Take `⟨S, hS, hU⟩` from `hq h hh`. Establish `hc : Continuous fun s : ℝ => h + s • k` using `continuous_const.add (continuous_id.smul continuous_const)`. Establish `hT : Filter.Tendsto (fun s : ℝ => h + s • k) (nhds 0) (nhds h)`.

Use `hc.tendsto 0` as an intermediate fact. Simplify using `using this`. Establish `A : ∀ᶠ s in nhds (0:ℝ), ∀ y ∉ S, 1 < q y (h + s • k)` using `hT.eventually hU`. Establish `B : ∀ᶠ s in nhds (0:ℝ), ∀ y ∈ S, 1 ≤ q y (h + s • k)`. Use `(Filter.eventually_all_finite hS).2 fun y _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hy : q y h = 1`. Use `Filter.Eventually.of_forall fun s => ?_` and prove the remaining obligations. Simplify using `[hy, hk y hy]`. Establish `hlt : 1 < q y h` using `lt_of_le_of_ne (hh' y) (Ne.symm hy)`. Establish `hcy : Continuous fun s : ℝ => q y (h + s • k)` using `(q y).continuous.comp hc`.

Establish `ht` using `hcy.tendsto 0`. Simplify using `only [zero_smul, add_zero] at ht`. Conclude with `(ht.eventually (lt_mem_nhds hlt)).mono fun s hs => hs.le`. Take `⟨δ, hδ, hP⟩` from `Metric.eventually_nhds_iff.1 (A.and B)`. Use `⟨δ / 2, half_pos hδ, fun s hs => ?_⟩` and prove the remaining obligations.

Establish `hd : dist s 0 < δ`. Rewrite using `[Real.dist_eq, sub_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨h1, h2⟩` from `hP hd`. Use `show ∀ y, 1 ≤ q y (h + s • k)`.

Introduce `y`. Distinguish the cases in `hyS : y ∈ S`. Conclude with `h2 y hyS`. Conclude with `(h1 y hyS).le`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.perturb :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ}, LocFin q → ∀ h ∈ poly q, ∀ k : E, (∀ y, q y h = 1 → q y k = 0) → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| ≤ ε → h + s • k ∈ poly q := by
  intro E Y _ _ q hq h hh k hk
  have hh' : ∀ y, 1 ≤ q y h := hh
  obtain ⟨S, hS, hU⟩ := hq h hh
  have hc : Continuous fun s : ℝ => h + s • k :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hT : Filter.Tendsto (fun s : ℝ => h + s • k) (nhds 0) (nhds h) := by
    have := hc.tendsto 0
    simpa using this
  have A : ∀ᶠ s in nhds (0:ℝ), ∀ y ∉ S, 1 < q y (h + s • k) := hT.eventually hU
  have B : ∀ᶠ s in nhds (0:ℝ), ∀ y ∈ S, 1 ≤ q y (h + s • k) := by
    refine (Filter.eventually_all_finite hS).2 fun y _ => ?_
    by_cases hy : q y h = 1
    · refine Filter.Eventually.of_forall fun s => ?_
      simp [hy, hk y hy]
    · have hlt : 1 < q y h := lt_of_le_of_ne (hh' y) (Ne.symm hy)
      have hcy : Continuous fun s : ℝ => q y (h + s • k) := (q y).continuous.comp hc
      have ht := hcy.tendsto 0
      simp only [zero_smul, add_zero] at ht
      exact (ht.eventually (lt_mem_nhds hlt)).mono fun s hs => hs.le
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 (A.and B)
  refine ⟨δ / 2, half_pos hδ, fun s hs => ?_⟩
  have hd : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    linarith
  obtain ⟨h1, h2⟩ := hP hd
  show ∀ y, 1 ≤ q y (h + s • k)
  intro y
  by_cases hyS : y ∈ S
  · exact h2 y hyS
  · exact (h1 y hyS).le
