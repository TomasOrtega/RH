import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.P1.trNe :
    ∀ {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H : Subgroup Γ) (χ : Fin (n + 1) → Γ →* kˣ), (Function.Injective fun i => (χ i).comp H.subtype) →
          H = ⊤ ∨ ∃ g, g ∉ H ∧ ∑ i, (χ i g : k) ≠ 0 := by
  intro Γ k _ _ n H χ hinj
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hH, hz⟩ := hcon
  have hz' : ∀ g, g ∉ H → ∑ i, (χ i g : k) = 0 := by
    intro g hg
    by_contra h
    exact hz ⟨g, hg, h⟩
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 ∉ H := by
    by_contra h
    apply hH
    rw [eq_top_iff]
    intro x _
    by_contra hx
    exact h ⟨x, hx⟩
  let ψ : Fin (n + 1) → (H →* k) := fun i => (Units.coeHom k).comp ((χ i).comp H.subtype)
  have hψ : Function.Injective ψ := by
    intro i j hij
    apply hinj
    ext x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom H k).comp ψ hψ
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (fun i => (χ i g0 : k)) (by
    funext h
    have hm : g0 * (h : Γ) ∉ H := fun hm => hg0 ((H.mul_mem_cancel_right h.2).1 hm)
    have := hz' _ hm
    simp only [map_mul, Units.val_mul] at this
    simpa [ψ, Finset.sum_apply] using this) 0
  exact (χ 0 g0).ne_zero h0
