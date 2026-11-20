import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ hL _ t`. Establish `h2 : (2 : K) ≠ 0`. Establish `h` using `hL.two.map (algebraMap O K)`. Rewrite `h` using `[map_ofNat]`. Conclude with `h.ne_zero`.

Establish `hiff : hs (τ ^ 2 - 4) (t : K) = 1 ↔ ∃ a b : K, a ^ 2 - (τ ^ 2 - 4) * b ^ 2 = t`. Unfold `hs`. Use `split_ifs with h`. Simplify using `[h]`. Simplify using `only [h, iff_false]`.

Evaluate the numerical expressions. Rewrite using `[hiff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Establish `hz' : QuadraticAlgebra.norm (z : QuadraticAlgebra K (-1) τ) = (t : K)`.

Establish `h` using `congrArg Units.val hz`. Rewrite `h` using `[Units.coe_map]`. Then use the resulting hypothesis. Use `⟨((z : QuadraticAlgebra K (-1) τ).re * 2 + τ * (z : QuadraticAlgebra K (-1) τ).im) / 2, (z : QuadraticAlgebra K (-1) τ).im / 2, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz', norm_def]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨a, b, hab⟩`. Establish `hw : QuadraticAlgebra.norm (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) = (t : K)`. Rewrite using `[← hab, norm_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hu : IsUnit (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ)`. Rewrite using `[isUnit_iff_norm_isUnit, hw]`. Conclude with `t.isUnit`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Use `ext`.

Rewrite using `[Units.coe_map, IsUnit.unit_spec]`. Conclude with `hw`.
-/
theorem UpperTheory.V.Z.Sym.Loc.hsNE : UpperTheory.V.Z.Sym.Loc.HsNE := by
  intro O K _ _ _ _ _ Δ τ hL _ t
  have h2 : (2 : K) ≠ 0 := by
    have h := hL.two.map (algebraMap O K)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hiff : hs (τ ^ 2 - 4) (t : K) = 1 ↔ ∃ a b : K, a ^ 2 - (τ ^ 2 - 4) * b ^ 2 = t := by
    unfold hs
    split_ifs with h
    · simp [h]
    · simp only [h, iff_false]
      norm_num
  rw [hiff]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : QuadraticAlgebra.norm (z : QuadraticAlgebra K (-1) τ) = (t : K) := by
      have h := congrArg Units.val hz
      rwa [Units.coe_map] at h
    refine ⟨((z : QuadraticAlgebra K (-1) τ).re * 2 + τ * (z : QuadraticAlgebra K (-1) τ).im) / 2,
      (z : QuadraticAlgebra K (-1) τ).im / 2, ?_⟩
    rw [← hz', norm_def]
    field_simp
    ring
  · rintro ⟨a, b, hab⟩
    have hw : QuadraticAlgebra.norm (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) = (t : K) := by
      rw [← hab, norm_def]
      ring
    have hu : IsUnit (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) := by
      rw [isUnit_iff_norm_isUnit, hw]
      exact t.isUnit
    refine ⟨hu.unit, ?_⟩
    ext
    rw [Units.coe_map, IsUnit.unit_spec]
    exact hw
