import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `E Y _ _ q T g π hq hT`. Establish `hpoly : ∀ h, h ∈ poly q → g.symm h ∈ poly q`. Introduce `h hh`. Use `show ∀ y, 1 ≤ q y (g.symm h)`. Introduce `y`.

Establish `h1` using `(hh : ∀ y, 1 ≤ q y h) (π y)`. Rewrite using `[← hq y (g.symm h), g.apply_symm_apply]`. Conclude with `h1`. Use `⟨fun h hv => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ∀ y, 1 ≤ q y (g h)`.

Introduce `y`. Establish `h1` using `(hv.1 : ∀ y, 1 ≤ q y h) (π.symm y)`. Rewrite `h1` using `[← hq (π.symm y) h, π.apply_symm_apply]`. Conclude with `h1`. Introduce `k hk`.

Establish `h0 : g.symm k = 0`. Use `hv.2 _ fun y hy => ?_` and prove the remaining obligations. Establish `h1 : q (π y) (g h) = 1`. Rewrite using `[hq]`. Conclude with `hy`.

Establish `h2` using `hk (π y) h1`. Rewrite using `[← hq y (g.symm k), g.apply_symm_apply]`. Conclude with `h2`. Simplify using `using congrArg g h0`. Introduce `n t t' ht ht0`.

Take `⟨x, hx, hxj⟩ : ∃ x ∈ posDual T, ∀ j, x ∈ normalCone q (t j).1` from `ht0`. Use `show ∃ x ∈ posDual T, ∀ j, x ∈ normalCone q (t' j).1`. Use `⟨x.comp (g.symm : E →L[ℝ] E), ?_, fun j => ?_⟩` and prove the remaining obligations. Use `show ∀ k ∈ T, k ≠ 0 → 0 < (x.comp (g.symm : E →L[ℝ] E)) k`. Introduce `k hk hk0`.

Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]`. Use `(hx : ∀ k ∈ T, k ≠ 0 → 0 < x k) (g.symm k) ?_ ?_` and prove the remaining obligations. Rewrite using `[← hT, g.apply_symm_apply]`. Conclude with `hk`. Introduce `h0`.

Conclude with `hk0 (by simpa using congrArg g h0)`. Use `show ∀ h' ∈ poly q, (x.comp (g.symm : E →L[ℝ] E)) (t' j).1 ≤ (x.comp (g.symm : E →L[ℝ] E)) h'`. Introduce `h' hh'`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ht j, g.symm_apply_apply]`. Conclude with `(hxj j : ∀ h' ∈ poly q, x (t j).1 ≤ x h') (g.symm h') (hpoly h' hh')`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.simp_smul :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E} (g : E ≃L[ℝ] E) (π : Y ≃ Y), (∀ y h, q (π y) (g h) = q y h) → (∀ k, g k ∈ T ↔ k ∈ T) → (∀ h, IsVert q h → IsVert q (g h)) ∧ ∀ (n : ℕ) (t t' : Fin n → Vert q), (∀ j, (t' j).1 = g (t j).1) → t ∈ simp q T n → t' ∈ simp q T n := by
  intro E Y _ _ q T g π hq hT
  have hpoly : ∀ h, h ∈ poly q → g.symm h ∈ poly q := by
    intro h hh
    show ∀ y, 1 ≤ q y (g.symm h)
    intro y
    have h1 := (hh : ∀ y, 1 ≤ q y h) (π y)
    rw [← hq y (g.symm h), g.apply_symm_apply]
    exact h1
  refine ⟨fun h hv => ⟨?_, ?_⟩, ?_⟩
  · show ∀ y, 1 ≤ q y (g h)
    intro y
    have h1 := (hv.1 : ∀ y, 1 ≤ q y h) (π.symm y)
    rw [← hq (π.symm y) h, π.apply_symm_apply] at h1
    exact h1
  · intro k hk
    have h0 : g.symm k = 0 := by
      refine hv.2 _ fun y hy => ?_
      have h1 : q (π y) (g h) = 1 := by
        rw [hq]
        exact hy
      have h2 := hk (π y) h1
      rw [← hq y (g.symm k), g.apply_symm_apply]
      exact h2
    simpa using congrArg g h0
  · intro n t t' ht ht0
    obtain ⟨x, hx, hxj⟩ : ∃ x ∈ posDual T, ∀ j, x ∈ normalCone q (t j).1 := ht0
    show ∃ x ∈ posDual T, ∀ j, x ∈ normalCone q (t' j).1
    refine ⟨x.comp (g.symm : E →L[ℝ] E), ?_, fun j => ?_⟩
    · show ∀ k ∈ T, k ≠ 0 → 0 < (x.comp (g.symm : E →L[ℝ] E)) k
      intro k hk hk0
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      refine (hx : ∀ k ∈ T, k ≠ 0 → 0 < x k) (g.symm k) ?_ ?_
      · rw [← hT, g.apply_symm_apply]
        exact hk
      · intro h0
        exact hk0 (by simpa using congrArg g h0)
    · show ∀ h' ∈ poly q, (x.comp (g.symm : E →L[ℝ] E)) (t' j).1 ≤ (x.comp (g.symm : E →L[ℝ] E)) h'
      intro h' hh'
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ht j,
        g.symm_apply_apply]
      exact (hxj j : ∀ h' ∈ poly q, x (t j).1 ≤ x h') (g.symm h') (hpoly h' hh')
