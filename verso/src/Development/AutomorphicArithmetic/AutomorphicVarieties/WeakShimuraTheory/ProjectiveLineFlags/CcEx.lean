import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T s`. Use `haveI := T.nL`. Use `haveI := T.cmL`. Use `haveI := T.nF`. Use `haveI := T.realF`.

Use `haveI : Normal (W.Lp T.L) T.L := by`. Unfold `UpperTheory.V.W.Lp`. Use `infer_instance`. Take `⟨j, hj⟩` from `s.hc`. Establish `hstab : ∀ τ : G (W.Lp T.L) Ω, ∀ x : T.L, ∃ y : T.L, τ (x : Ω) = (y : Ω)`.

Introduce `τ x`. Conclude with `⟨τ.restrictNormal T.L x, (AlgEquiv.restrictNormal_commutes τ T.L x).symm⟩`. Establish `hfixF : ∀ x : T.F, s.c (x : Ω) = x`. Introduce `x`. Establish `hmem : (⟨(x : Ω), T.F_le x.2⟩ : T.L) ∈ NumberField.maximalRealSubfield T.L`.

Introduce `φ`. Establish `h` using `NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp (IntermediateField.inclusion T.F_le).toRingHom)`. Establish `h2` using `RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp h) x`. Simplify using `only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h2`. Conclude with `h2`.

Conclude with `s.c.commutes (show W.Lp T.L from (⟨_, hmem⟩ : NumberField.maximalRealSubfield T.L))`. Set `cF : G T.F Ω` to `{ s.c.toRingEquiv with commutes' := fun x => hfixF x }`. Use `⟨cF, ⟨j, fun x => hj x⟩, ?_⟩` and prove the remaining obligations. Introduce `g`. Set `ρ : Ω ≃+* Ω` to `s.c.symm.toRingEquiv.trans (g.toRingEquiv.trans s.c.toRingEquiv)`.

Establish `hρ : ∀ x : T.L, ρ (algebraMap T.L Ω x) = algebraMap T.L Ω x`. Introduce `x`. Take `⟨y, hy⟩` from `hstab s.c⁻¹ x`. Establish `hy' : s.c.symm (x : Ω) = (y : Ω)` using `hy`. Express the relevant statement in the definitionally equal form `s.c (g (s.c.symm (x : Ω))) = (x : Ω)`.

Rewrite using `[hy']`. Establish `hg : g (y : Ω) = (y : Ω)` using `g.commutes y`. Rewrite using `[hg, ← hy']`. Conclude with `s.c.apply_symm_apply _`. Use `⟨AlgEquiv.ofRingEquiv hρ, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `z`. Both sides reduce to the same expression. Use extensionality with `z`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Ws.P1.ccEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ cF : G T.F Ω, IsCC cF ∧
          ∀ g : G T.L Ω, ∃ g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ ∧ resLe T.F_le g' = cF * resLe T.F_le g * cF⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  haveI := T.nL
  haveI := T.cmL
  haveI := T.nF
  haveI := T.realF
  haveI : Normal (W.Lp T.L) T.L := by
    unfold UpperTheory.V.W.Lp
    infer_instance
  obtain ⟨j, hj⟩ := s.hc
  have hstab : ∀ τ : G (W.Lp T.L) Ω, ∀ x : T.L, ∃ y : T.L, τ (x : Ω) = (y : Ω) := by
    intro τ x
    exact ⟨τ.restrictNormal T.L x, (AlgEquiv.restrictNormal_commutes τ T.L x).symm⟩
  have hfixF : ∀ x : T.F, s.c (x : Ω) = x := by
    intro x
    have hmem : (⟨(x : Ω), T.F_le x.2⟩ : T.L) ∈ NumberField.maximalRealSubfield T.L := by
      intro φ
      have h := NumberField.IsTotallyReal.complexEmbedding_isReal
        (φ.comp (IntermediateField.inclusion T.F_le).toRingHom)
      have h2 := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp h) x
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h2
      exact h2
    exact s.c.commutes (show W.Lp T.L from (⟨_, hmem⟩ : NumberField.maximalRealSubfield T.L))
  let cF : G T.F Ω := { s.c.toRingEquiv with commutes' := fun x => hfixF x }
  refine ⟨cF, ⟨j, fun x => hj x⟩, ?_⟩
  intro g
  let ρ : Ω ≃+* Ω := s.c.symm.toRingEquiv.trans (g.toRingEquiv.trans s.c.toRingEquiv)
  have hρ : ∀ x : T.L, ρ (algebraMap T.L Ω x) = algebraMap T.L Ω x := by
    intro x
    obtain ⟨y, hy⟩ := hstab s.c⁻¹ x
    have hy' : s.c.symm (x : Ω) = (y : Ω) := hy
    change s.c (g (s.c.symm (x : Ω))) = (x : Ω)
    rw [hy']
    have hg : g (y : Ω) = (y : Ω) := g.commutes y
    rw [hg, ← hy']
    exact s.c.apply_symm_apply _
  refine ⟨AlgEquiv.ofRingEquiv hρ, ?_, ?_⟩
  · ext z
    rfl
  · ext z
    rfl
