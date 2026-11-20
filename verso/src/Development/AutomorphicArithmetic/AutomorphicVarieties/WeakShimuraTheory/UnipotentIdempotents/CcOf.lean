import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T s`. Take `⟨j, hj⟩` from `s.hc`. Use `⟨(s.c : Ω ≃ₐ[W.Lp T.L] Ω).restrictScalars ℚ, ?_, ?_⟩` and prove the remaining obligations. Introduce `hfix`. Rewrite `hfix` using `[IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]`.

Establish `hreal : NumberField.ComplexEmbedding.IsReal (j.comp (T.K.val : T.K →+* Ω))`. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Establish `hx` using `hfix (x : Ω) x.2`.

Express the relevant statement in the definitionally equal form `s.c (x : Ω) = (x : Ω) at hx`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← hj]`. Express the relevant statement in the definitionally equal form `j (s.c (x : Ω)) = j (x : Ω)`. Rewrite using `[hx]`.

Conclude with `NumberField.IsTotallyComplex.complexEmbedding_not_isReal _ hreal`. Introduce `g g' h`. Use extensionality with `x`. Establish `hx` using `congrArg (fun f : G (W.Lp T.L) Ω => f x) h`. Conclude with `hx`.
-/
theorem UpperTheory.V.Ws.Lk.ccOf :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ → resQ T.L g' = σ * resQ T.L g * σ⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  obtain ⟨j, hj⟩ := s.hc
  refine ⟨(s.c : Ω ≃ₐ[W.Lp T.L] Ω).restrictScalars ℚ, ?_, ?_⟩
  · intro hfix
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hfix
    have hreal : NumberField.ComplexEmbedding.IsReal (j.comp (T.K.val : T.K →+* Ω)) := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      have hx := hfix (x : Ω) x.2
      change s.c (x : Ω) = (x : Ω) at hx
      simp only [RingHom.comp_apply]
      rw [← hj]
      change j (s.c (x : Ω)) = j (x : Ω)
      rw [hx]
    exact NumberField.IsTotallyComplex.complexEmbedding_not_isReal _ hreal
  · intro g g' h
    ext x
    have hx := congrArg (fun f : G (W.Lp T.L) Ω => f x) h
    exact hx
