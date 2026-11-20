import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr Matrix

/- English proof (translation)
Introduce `Γ V S _ _ _ d G _hcone l hl q P hP γ w`. Establish `hinv : ∀ x : V, G.ρ γ (G.ρ γ⁻¹ x) = x`. Introduce `x`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Establish `hinv' : ∀ x : V, G.ρ γ⁻¹ (G.ρ γ x) = x`.

Introduce `x`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]`. Establish `hinvS : ∀ s : S, G.σ γ (G.σ γ⁻¹ s) = s`. Introduce `s`. Rewrite using `[← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Distinguish the cases in `hp : p ∈ G.Y`. Establish `hp' : G.ρ γ⁻¹ p ∈ G.Y` using `G.maps _ _ hp`. Establish `hleq : l (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = l s p`.

Use `hl.2 γ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) hp'` as an intermediate fact. Rewrite `this` using `[hinvS, hinv]`. Conclude with `this.symm`. Establish `hdiff : DifferentiableAt ℝ (l s) p` using `((hl.1 s).1.contDiffAt (G.isOpen.mem_nhds hp)).differentiableAt (by simp)`. Establish `hf : HasFDerivAt (fun x => l s x • x) (fderiv ℝ (fun x => l s x • x) p) (G.ρ γ (G.ρ γ⁻¹ p))`.

Rewrite using `[hinv]`. Conclude with `(hdiff.smul differentiableAt_id).hasFDerivAt`. Establish `hcomp` using `(G.ρ γ⁻¹).hasFDerivAt.comp (G.ρ γ⁻¹ p) (hf.comp (G.ρ γ⁻¹ p) (G.ρ γ).hasFDerivAt)`. Establish `heq : (fun x => l (G.σ γ⁻¹ s) x • x) =ᶠ[nhds (G.ρ γ⁻¹ p)] (⇑(G.ρ γ⁻¹) ∘ ((fun x => l s x • x) ∘ ⇑(G.ρ γ)))` using `by filter_upwards [G.isOpen.mem_nhds hp'] with x hx`. Use `hl.2 γ (G.σ γ⁻¹ s) x hx` as an intermediate fact.

Rewrite `this` using `[hinvS]`. Simplify using `only [Function.comp_apply, map_smul, hinv', this]`. Establish `hder : ∀ u : V, fderiv ℝ (fun x => l (G.σ γ⁻¹ s) x • x) (G.ρ γ⁻¹ p) (G.ρ γ⁻¹ u) = G.ρ γ⁻¹ (fderiv ℝ (fun x => l s x • x) p u)`. Introduce `u`. Rewrite using `[(hcomp.congr_of_eventuallyEq heq).fderiv]`.

Simplify using `only [ContinuousLinearMap.coe_comp', Function.comp_apply, hinv]`. Use extensionality with `v`. Rewrite using `[G.act_apply, hP w _ _ hp', hP _ s p hp]`. Simplify using `only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply, G.act_apply]`. Rewrite using `[hleq, map_smul]`.

Simplify using `only [Function.comp_def, hder]`. Establish `hnot : G.ρ γ⁻¹ p ∉ G.Y`. Introduce `h`. Conclude with `hp (hinv p ▸ G.maps γ _ h)`. Establish `h1` using `((P w).2 (G.σ γ⁻¹ s)).2 _ hnot`.

Establish `h2` using `((P (G.act q γ w)).2 s).2 p hp`. Rewrite using `[h2]`. Use extensionality with `v`. Rewrite using `[G.act_apply, h1]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Cj.A.pullAct :
    PullAct := by
  intro Γ V S _ _ _ d G _hcone l hl q P hP γ w
  have hinv : ∀ x : V, G.ρ γ (G.ρ γ⁻¹ x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  have hinv' : ∀ x : V, G.ρ γ⁻¹ (G.ρ γ x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  have hinvS : ∀ s : S, G.σ γ (G.σ γ⁻¹ s) = s := by
    intro s
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  apply Subtype.ext
  funext s p
  by_cases hp : p ∈ G.Y
  · have hp' : G.ρ γ⁻¹ p ∈ G.Y := G.maps _ _ hp
    have hleq : l (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = l s p := by
      have := hl.2 γ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) hp'
      rw [hinvS, hinv] at this
      exact this.symm
    have hdiff : DifferentiableAt ℝ (l s) p :=
      ((hl.1 s).1.contDiffAt (G.isOpen.mem_nhds hp)).differentiableAt (by simp)
    have hf : HasFDerivAt (fun x => l s x • x) (fderiv ℝ (fun x => l s x • x) p) (G.ρ γ (G.ρ γ⁻¹ p)) := by
      rw [hinv]
      exact (hdiff.smul differentiableAt_id).hasFDerivAt
    have hcomp := (G.ρ γ⁻¹).hasFDerivAt.comp (G.ρ γ⁻¹ p) (hf.comp (G.ρ γ⁻¹ p) (G.ρ γ).hasFDerivAt)
    have heq : (fun x => l (G.σ γ⁻¹ s) x • x) =ᶠ[nhds (G.ρ γ⁻¹ p)]
        (⇑(G.ρ γ⁻¹) ∘ ((fun x => l s x • x) ∘ ⇑(G.ρ γ))) := by
      filter_upwards [G.isOpen.mem_nhds hp'] with x hx
      have := hl.2 γ (G.σ γ⁻¹ s) x hx
      rw [hinvS] at this
      simp only [Function.comp_apply, map_smul, hinv', this]
    have hder : ∀ u : V, fderiv ℝ (fun x => l (G.σ γ⁻¹ s) x • x) (G.ρ γ⁻¹ p) (G.ρ γ⁻¹ u)
        = G.ρ γ⁻¹ (fderiv ℝ (fun x => l s x • x) p u) := by
      intro u
      rw [(hcomp.congr_of_eventuallyEq heq).fderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hinv]
    ext v
    rw [G.act_apply, hP w _ _ hp', hP _ s p hp]
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply, G.act_apply]
    rw [hleq, map_smul]
    simp only [Function.comp_def, hder]
  · have hnot : G.ρ γ⁻¹ p ∉ G.Y := by
      intro h
      exact hp (hinv p ▸ G.maps γ _ h)
    have h1 := ((P w).2 (G.σ γ⁻¹ s)).2 _ hnot
    have h2 := ((P (G.act q γ w)).2 s).2 p hp
    rw [h2]
    ext v
    rw [G.act_apply, h1]
    simp
