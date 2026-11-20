import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `Γ k _ _ n H χ hinj`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_or]`. Take `⟨hH, hz⟩` from `hcon`. Establish `hz' : ∀ g, g ∉ H → ∑ i, (χ i g : k) = 0`.

Introduce `g hg`. Assume the negation of the conclusion as `h`. Conclude with `hz ⟨g, hg, h⟩`. Choose the witnesses or unpack the hypotheses as in `⟨g0, hg0⟩ : ∃ g0, g0 ∉ H := by`. Assume the negation of the conclusion as `h`.

Apply `hH` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`. Introduce `x _`. Assume the negation of the conclusion as `hx`. Conclude with `h ⟨x, hx⟩`.

Set `ψ : Fin (n + 1) → (H →* k)` to `fun i => (Units.coeHom k).comp ((χ i).comp H.subtype)`. Establish `hψ : Function.Injective ψ`. Introduce `i j hij`. Apply `hinj` to reduce the goal to its premises. Use extensionality with `x`.

Conclude with `DFunLike.congr_fun hij x`. Establish `hli` using `(linearIndependent_monoidHom H k).comp ψ hψ`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Establish `h0` using `hli (fun i => (χ i g0 : k)) (by`. Use function extensionality and compare the values at `h`.

Establish `hm : g0 * (h : Γ) ∉ H` using `fun hm => hg0 ((H.mul_mem_cancel_right h.2).1 hm)`. Use `hz' _ hm` as an intermediate fact. Simplify using `only [map_mul, Units.val_mul] at this`. Simplify `this) 0` using `[ψ, Finset.sum_apply]`. Conclude with `(χ 0 g0).ne_zero h0`.
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
