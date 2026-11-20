import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

open scoped Matrix

/- English proof (translation)
Introduce `Γ X Y _ _ _ p hp y horb d ξ f f' h`. Use function extensionality and compare the values at `x`. Take `⟨g, hg⟩` from `horb x`. Establish `hx : g • x ∈ UpperTheory.V.Af.CohB.fib p hp y`. Express the relevant statement in the definitionally equal form `p (g • x) = y`.

Rewrite using `[hp, hg]`. Establish `h1 : (UpperTheory.V.Af.CohB.toCo p hp y ξ f).1 g ⟨g • x, hx⟩ = (UpperTheory.V.Af.CohB.toCo p hp y ξ f').1 g ⟨g • x, hx⟩` using `by rw [h]`. Rewrite `h1` using `[UpperTheory.V.Af.CohB.toCo_apply, UpperTheory.V.Af.CohB.toCo_apply]`. Simplify using `only [inv_smul_smul] at h1`. Establish `h2` using `congrArg (fun v => ξ g⁻¹ *ᵥ v) h1`.

Simplify using `only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2`. Conclude with `h2`.
-/
theorem UpperTheory.cohomology_to_coinvariants_injective :
    UpperTheory.V.Af.CohB.ToCoInj := by
  intro Γ X Y _ _ _ p hp y horb d ξ f f' h
  funext x
  obtain ⟨g, hg⟩ := horb x
  have hx : g • x ∈ UpperTheory.V.Af.CohB.fib p hp y := by
    change p (g • x) = y
    rw [hp, hg]
  have h1 : (UpperTheory.V.Af.CohB.toCo p hp y ξ f).1 g ⟨g • x, hx⟩
      = (UpperTheory.V.Af.CohB.toCo p hp y ξ f').1 g ⟨g • x, hx⟩ := by rw [h]
  rw [UpperTheory.V.Af.CohB.toCo_apply, UpperTheory.V.Af.CohB.toCo_apply] at h1
  simp only [inv_smul_smul] at h1
  have h2 := congrArg (fun v => ξ g⁻¹ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
  exact h2
