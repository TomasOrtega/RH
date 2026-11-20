import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Introduce `Γ k _ _ κ U hU hu y hy hb`. Take `⟨u, huU, hu1⟩` from `hu`. Take `⟨b, hb⟩` from `hb`. Use `⟨b, fun s => ?_⟩` and prove the remaining obligations. Establish `hc : s * u * s⁻¹ * u⁻¹ ∈ U`.

Apply `hU` to reduce the goal to its premises. Use `Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top u)` as an intermediate fact. Rewrite `this` using `[commutatorElement_def]`. Conclude with `this`. Establish `hv : s * u * s⁻¹ ∈ U`.

Use `U.mul_mem hc huU` as an intermediate fact. Simplify using `using this`. Establish `hκ : κ (s * u * s⁻¹) = κ u`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm (κ s) (κ u), mul_inv_cancel_right]`. Establish `h1` using `hy s u`.

Establish `h2` using `hy (s * u * s⁻¹) s`. Rewrite `h2` using `[inv_mul_cancel_right, hb _ hv, hκ]`. Rewrite `h1` using `[hb u huU]`. Establish `hne : ((κ u : k) - 1) ≠ 0`. Introduce `h`.

Apply `hu1` to reduce the goal to its premises. Use `ext`. Simplify using `using sub_eq_zero.mp h`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `h1 - h2`.
-/
theorem UpperTheory.V.Fr.st_res :
    ∀ (Γ k : Type) [Group Γ] [Field k] (κ : Γ →* kˣ) (U : Subgroup Γ), commutator Γ ≤ U → (∃ u ∈ U, κ u ≠ 1) → ∀ y : Γ → k, (∀ s t, y (s * t) = y s + κ s * y t) → (∃ b, ∀ s ∈ U, y s = κ s * b - b) → ∃ b, ∀ s, y s = κ s * b - b := by
  intro Γ k _ _ κ U hU hu y hy hb
  obtain ⟨u, huU, hu1⟩ := hu
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun s => ?_⟩
  have hc : s * u * s⁻¹ * u⁻¹ ∈ U := by
    apply hU
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top u)
    rw [commutatorElement_def] at this
    exact this
  have hv : s * u * s⁻¹ ∈ U := by
    have := U.mul_mem hc huU
    simpa using this
  have hκ : κ (s * u * s⁻¹) = κ u := by
    rw [map_mul, map_mul, map_inv, mul_comm (κ s) (κ u), mul_inv_cancel_right]
  have h1 := hy s u
  have h2 := hy (s * u * s⁻¹) s
  rw [inv_mul_cancel_right, hb _ hv, hκ] at h2
  rw [hb u huU] at h1
  have hne : ((κ u : k) - 1) ≠ 0 := by
    intro h
    apply hu1
    ext
    simpa using sub_eq_zero.mp h
  apply mul_left_cancel₀ hne
  linear_combination h1 - h2
