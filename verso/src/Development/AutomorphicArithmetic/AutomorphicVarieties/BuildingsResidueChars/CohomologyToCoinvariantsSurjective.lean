import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

open scoped Matrix in
/- English proof (translation)
Introduce `Γ X Y _ _ _ p hp y h d ξ F`. Use `choose c hc using h`. Establish `hm : ∀ x, c x • x ∈ UpperTheory.V.Af.CohB.fib p hp y` using `fun x => by`. Express the relevant statement in the definitionally equal form `p (c x • x) = y`. Rewrite using `[hp, hc]`.

Establish `key : ∀ (g g' : Γ) (z z' : ↥(UpperTheory.V.Af.CohB.fib p hp y)), g⁻¹ • z.1 = g'⁻¹ • z'.1 → ξ g *ᵥ (ξ g'⁻¹ *ᵥ F.1 g' z') = F.1 g z`. Introduce `g g' z z' hz`. Establish `hz' : z.1 = (g * g'⁻¹) • z'.1` using `by rw [mul_smul, ← hz, smul_inv_smul]`. Establish `hs : g * g'⁻¹ ∈ MulAction.stabilizer Γ y`. Establish `h1 : p z.1 = y` using `z.2`.

Establish `h2 : p z'.1 = y` using `z'.2`. Rewrite `h1` using `[hz', hp, h2]`. Conclude with `h1`. Establish `h3` using `congrFun (F.2 ⟨_, hs⟩ g') z`. Establish `h4 : (⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z = z'`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(g * g'⁻¹)⁻¹ • z.1 = z'.1`. Rewrite using `[hz', inv_smul_smul]`. Express the relevant statement in the definitionally equal form `F.1 (g * g'⁻¹ * g') z = ξ (g * g'⁻¹) *ᵥ F.1 g' ((⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z) at h3`. Rewrite `h3` using `[h4, inv_mul_cancel_right]`.

Rewrite using `[h3, map_mul, Matrix.mulVec_mulVec]`. Use `⟨fun x => ξ (c x)⁻¹ *ᵥ F.1 (c x) ⟨c x • x, hm x⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g z`. Rewrite using `[UpperTheory.V.Af.CohB.toCo_apply]`.

Conclude with `key g _ z _ (by simp)`.
-/
theorem UpperTheory.cohomology_to_coinvariants_surjective :
    UpperTheory.V.Af.CohB.ToCoSurj := by
  intro Γ X Y _ _ _ p hp y h d ξ F
  choose c hc using h
  have hm : ∀ x, c x • x ∈ UpperTheory.V.Af.CohB.fib p hp y := fun x => by
    change p (c x • x) = y
    rw [hp, hc]
  have key : ∀ (g g' : Γ) (z z' : ↥(UpperTheory.V.Af.CohB.fib p hp y)), g⁻¹ • z.1 = g'⁻¹ • z'.1 →
      ξ g *ᵥ (ξ g'⁻¹ *ᵥ F.1 g' z') = F.1 g z := by
    intro g g' z z' hz
    have hz' : z.1 = (g * g'⁻¹) • z'.1 := by rw [mul_smul, ← hz, smul_inv_smul]
    have hs : g * g'⁻¹ ∈ MulAction.stabilizer Γ y := by
      have h1 : p z.1 = y := z.2
      have h2 : p z'.1 = y := z'.2
      rw [hz', hp, h2] at h1
      exact h1
    have h3 := congrFun (F.2 ⟨_, hs⟩ g') z
    have h4 : (⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z = z' := by
      apply Subtype.ext
      change (g * g'⁻¹)⁻¹ • z.1 = z'.1
      rw [hz', inv_smul_smul]
    change F.1 (g * g'⁻¹ * g') z = ξ (g * g'⁻¹) *ᵥ F.1 g' ((⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z) at h3
    rw [h4, inv_mul_cancel_right] at h3
    rw [h3, map_mul, Matrix.mulVec_mulVec]
  refine ⟨fun x => ξ (c x)⁻¹ *ᵥ F.1 (c x) ⟨c x • x, hm x⟩, ?_⟩
  apply Subtype.ext
  funext g z
  rw [UpperTheory.V.Af.CohB.toCo_apply]
  exact key g _ z _ (by simp)
