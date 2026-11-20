import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

/- English proof (translation)
Use `haveI := h.frac`. Establish `hN : e.re * e.re + τ * e.re * e.im - (-1) * e.im * e.im = 1`. Establish `h'` using `hn`. Rewrite `h'` using `[QuadraticAlgebra.norm_def]`. Conclude with `h'`.

Distinguish the cases in `hq : e.im = 0`. Establish `hp : (e.re - 1) * (e.re + 1) = 0`. Rewrite `hN` using `[hq]`. Take the linear combination `hN`. Break down `mul_eq_zero.mp hp with h1 | h1` into its components or cases.

Establish `he : e = 1`. Use `ext`. Simplify using the standard rewrite rules. Take the linear combination `h1`. Simplify using `[hq]`.

Rewrite using `[he]`. Conclude with `isIntegral_one`. Establish `he : e = -1`. Use `ext`. Simplify using the standard rewrite rules.

Take the linear combination `h1`. Simplify using `[hq]`. Rewrite using `[he]`. Conclude with `isIntegral_one.neg`. Establish `h2K : (2 : K) ≠ 0`.

Establish `h2` using `h.two.map (algebraMap O K)`. Rewrite `h2` using `[map_ofNat]`. Conclude with `h2.ne_zero`. Establish `nz : ∀ x y : K, y ≠ 0 → x * x + τ * x * y + y * y ≠ 0`. Introduce `x y hy hxy`.

Apply `hτ` to reduce the goal to its premises. Use `⟨2 * x / y + τ, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-4) * hxy`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : O, algebraMap O K t = QuadraticAlgebra.trace e := by`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hTd : QuadraticAlgebra.trace e = 2 * e.re + τ * e.im` using `QuadraticAlgebra.trace_def e`. Use `set T := QuadraticAlgebra.trace e with hTdef`. Establish `hT0 : T ≠ 0` using `fun h0 => hne 0 (by rw [map_zero, h0])`.

Break down `ValuationRing.isInteger_or_isInteger O T with ⟨t, ht⟩ | ⟨s, hs⟩` into its components or cases. Conclude with `hne t ht`. Establish `hsm : s ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Take `⟨u, rfl⟩` from `hu`. Apply `hne (↑u⁻¹)` to reduce the goal to its premises. Rewrite using `[map_units_inv, hs, inv_inv]`. Take `⟨r, hr, -⟩` from `sqrtO O K Δ h (1 - 4 * s ^ 2) 1 isUnit_one (by`. Establish `e' : (1 - 4 * s ^ 2) - 1 ^ 2 = s * (-(4 * s))` using `by ring`.

Rewrite using `[e']`. Conclude with `Ideal.mul_mem_right _ _ hsm)`. Establish `hTS : T * algebraMap O K s = 1`. Rewrite using `[hs]`. Conclude with `mul_inv_cancel₀ hT0`.

Establish `hR : (algebraMap O K r) ^ 2 = 1 - 4 * (algebraMap O K s) ^ 2`. Rewrite using `[← map_pow, hr, map_sub, map_one, map_mul, map_pow, map_ofNat]`. Apply `nz (-τ * e.im - T * algebraMap O K r) (2 * e.im) (mul_ne_zero h2K hq)` to reduce the goal to its premises. Take the linear combination `T ^ 2 * hR - 4 * (T * algebraMap O K s + 1) * hTS + 4 * hN + (T + 2 * e.re + τ * e.im) * hTd`. Conclude with `isIntegral_of_trace_norm t 1 ht.symm (by rw [hn, map_one])`.
-/
private theorem int_of_norm_one {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] {Δ τ : K} (h : IsLoc O Δ) (hτ : ¬ IsSquare (τ ^ 2 - 4)) (e : Etau K τ)
    (hn : QuadraticAlgebra.norm e = 1) : IsIntegral O e := by
  classical
  haveI := h.frac
  have hN : e.re * e.re + τ * e.re * e.im - (-1) * e.im * e.im = 1 := by
    have h' := hn
    rw [QuadraticAlgebra.norm_def] at h'
    exact h'
  by_cases hq : e.im = 0
  · have hp : (e.re - 1) * (e.re + 1) = 0 := by
      rw [hq] at hN
      linear_combination hN
    rcases mul_eq_zero.mp hp with h1 | h1
    · have he : e = 1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one
    · have he : e = -1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one.neg
  · have h2K : (2 : K) ≠ 0 := by
      have h2 := h.two.map (algebraMap O K)
      rw [map_ofNat] at h2
      exact h2.ne_zero
    have nz : ∀ x y : K, y ≠ 0 → x * x + τ * x * y + y * y ≠ 0 := by
      intro x y hy hxy
      apply hτ
      refine ⟨2 * x / y + τ, ?_⟩
      field_simp
      linear_combination (-4) * hxy
    obtain ⟨t, ht⟩ : ∃ t : O, algebraMap O K t = QuadraticAlgebra.trace e := by
      by_contra hne
      push_neg at hne
      have hTd : QuadraticAlgebra.trace e = 2 * e.re + τ * e.im := QuadraticAlgebra.trace_def e
      set T := QuadraticAlgebra.trace e with hTdef
      have hT0 : T ≠ 0 := fun h0 => hne 0 (by rw [map_zero, h0])
      rcases ValuationRing.isInteger_or_isInteger O T with ⟨t, ht⟩ | ⟨s, hs⟩
      · exact hne t ht
      · have hsm : s ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          obtain ⟨u, rfl⟩ := hu
          apply hne (↑u⁻¹)
          rw [map_units_inv, hs, inv_inv]
        obtain ⟨r, hr, -⟩ := sqrtO O K Δ h (1 - 4 * s ^ 2) 1 isUnit_one (by
          have e' : (1 - 4 * s ^ 2) - 1 ^ 2 = s * (-(4 * s)) := by ring
          rw [e']
          exact Ideal.mul_mem_right _ _ hsm)
        have hTS : T * algebraMap O K s = 1 := by
          rw [hs]
          exact mul_inv_cancel₀ hT0
        have hR : (algebraMap O K r) ^ 2 = 1 - 4 * (algebraMap O K s) ^ 2 := by
          rw [← map_pow, hr, map_sub, map_one, map_mul, map_pow, map_ofNat]
        apply nz (-τ * e.im - T * algebraMap O K r) (2 * e.im) (mul_ne_zero h2K hq)
        linear_combination T ^ 2 * hR - 4 * (T * algebraMap O K s + 1) * hTS + 4 * hN +
          (T + 2 * e.re + τ * e.im) * hTd
    exact isIntegral_of_trace_norm t 1 ht.symm (by rw [hn, map_one])

/- English proof (translation)
Simplify using `only [quo, map_mul, QuadraticAlgebra.norm_star]`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.
-/
private theorem norm_quo {K : Type} [Field K] {τ : K} (z : (Etau K τ)ˣ) : QuadraticAlgebra.norm (quo z) = 1 := by
  simp only [quo, map_mul, QuadraticAlgebra.norm_star]
  rw [← map_mul, Units.mul_inv, map_one]

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ h _ hτ`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Conclude with `⟨int_of_norm_one h hτ _ (norm_quo z), int_of_norm_one h hτ _ (norm_quo z⁻¹)⟩`.
-/
theorem UpperTheory.compactTorusUnits_eq_top_of_nonsplit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ¬ IsSquare (τ ^ 2 - 4) → Cint O τ = ⊤ := by
  intro O K _ _ _ _ _ Δ τ h _ hτ
  rw [eq_top_iff]
  intro z _
  exact ⟨int_of_norm_one h hτ _ (norm_quo z), int_of_norm_one h hτ _ (norm_quo z⁻¹)⟩
