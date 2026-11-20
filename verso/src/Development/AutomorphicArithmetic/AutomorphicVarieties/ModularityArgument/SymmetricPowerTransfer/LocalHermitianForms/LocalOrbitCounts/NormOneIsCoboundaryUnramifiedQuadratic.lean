import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ L β hβ`. Use `haveI := L.frac`. Establish `h2` using `L.two_ne`. Establish `h0 : Δ ≠ 0`. Take `⟨u, s, hs, e⟩` from `L.even`.

Rewrite using `[e]`. Conclude with `mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)`. Rewrite `hβ` using `[QuadraticAlgebra.norm_def]`. Distinguish the cases in `h : 1 + β.re = 0`. Establish `h1 : β.re = -1` using `by linear_combination h`.

Establish `h3 : β.im = 0`. Establish `: Δ * β.im ^ 2 = 0` using `by rw [h1] at hβ; linear_combination -hβ`. Simplify `this` using `[h0]`. Establish `hu : IsUnit (ω : Lsq K Δ)` using `QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by simp [QuadraticAlgebra.norm_def, h0])`. Apply the tactic sequence `exact ⟨hu.unit, by ext <;> simp [h1, h3]⟩`.

Establish `hu : IsUnit (⟨1 + β.re, -β.im⟩ : Lsq K Δ)` using `QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by`. Establish `: QuadraticAlgebra.norm (⟨1 + β.re, -β.im⟩ : Lsq K Δ) = 2 * (1 + β.re)`. Rewrite using `[QuadraticAlgebra.norm_def]`. Simplify using `only`. Take the linear combination `hβ`.

Rewrite using `[this]`. Conclude with `(mul_ne_zero h2 h).isUnit)`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using the standard rewrite rules.

Take the linear combination `-hβ`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Sym.Loc.h90L : UpperTheory.V.Z.Sym.Loc.NormOneIsCoboundaryUnramifiedQuadratic := by
  intro O K _ _ _ _ _ Δ L β hβ
  haveI := L.frac
  have h2 := L.two_ne
  have h0 : Δ ≠ 0 := by
    obtain ⟨u, s, hs, e⟩ := L.even
    rw [e]
    exact mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)
  rw [QuadraticAlgebra.norm_def] at hβ
  by_cases h : 1 + β.re = 0
  · have h1 : β.re = -1 := by linear_combination h
    have h3 : β.im = 0 := by
      have : Δ * β.im ^ 2 = 0 := by rw [h1] at hβ; linear_combination -hβ
      simpa [h0] using this
    have hu : IsUnit (ω : Lsq K Δ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by simp [QuadraticAlgebra.norm_def, h0])
    exact ⟨hu.unit, by ext <;> simp [h1, h3]⟩
  · have hu : IsUnit (⟨1 + β.re, -β.im⟩ : Lsq K Δ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by
      have : QuadraticAlgebra.norm (⟨1 + β.re, -β.im⟩ : Lsq K Δ) = 2 * (1 + β.re) := by
        rw [QuadraticAlgebra.norm_def]; simp only; linear_combination hβ
      rw [this]; exact (mul_ne_zero h2 h).isUnit)
    refine ⟨hu.unit, ?_⟩
    ext
    · simp; linear_combination -hβ
    · simp; ring
