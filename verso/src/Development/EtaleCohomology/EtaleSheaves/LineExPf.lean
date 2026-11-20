import Development.EtaleCohomology.EtaleSheaves.ChowLCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineExPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℤ

/- English proof (translation)
Introduce and unpack `⟨x, hx⟩`. Use `⟨MvPolynomial.coeff 0 x, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h : MvPolynomial.IsHomogeneous x 0` using `(MvPolynomial.mem_homogeneousSubmodule _ _).mp hx`. Distinguish the cases in `h0 : x = 0`.

Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Use `h.totalDegree h0` as an intermediate fact. Rewrite `this` using `[MvPolynomial.totalDegree_eq_zero_iff_eq_C]`. Express the relevant statement in the definitionally equal form `((algebraMap ℤ (𝒜 0) _ : 𝒜 0) : MvPolynomial (Fin 2) ℤ) = x`.

Use `Eq.trans ?_ this.symm` and prove the remaining obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
lemma zero_surj : Function.Surjective (algebraMap ℤ (𝒜 0)) := by
  rintro ⟨x, hx⟩
  refine ⟨MvPolynomial.coeff 0 x, ?_⟩
  apply Subtype.ext
  have h : MvPolynomial.IsHomogeneous x 0 := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hx
  by_cases h0 : x = 0
  · subst h0; simp
  · have := h.totalDegree h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at this
    change ((algebraMap ℤ (𝒜 0) _ : 𝒜 0) : MvPolynomial (Fin 2) ℤ) = x
    refine Eq.trans ?_ this.symm
    simp
    rfl

instance ft : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin 2) ℤ) :=
  Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝒜 0) (MvPolynomial (Fin 2) ℤ)

/- English proof (translation)
The claim follows from `inferInstance`.
-/
lemma proj_proper : IsProper (Proj.toSpecZero 𝒜) := inferInstance

/- English proof (translation)
Establish `h1 : IsProper (Proj.toSpecZero 𝒜)` using `proj_proper`. Establish `h2 : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0))))` using `IsClosedImmersion.spec_of_surjective _ zero_surj`. Establish `e : terminal.from P1 = Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0))) ≫ terminal.from (Spec (CommRingCat.of ℤ))` using `terminal.hom_ext _ _`. Establish `: IsIso (terminal.from (Spec (CommRingCat.of ℤ)))` using `⟨⟨specZIsTerminal.from _, specZIsTerminal.hom_ext _ _, terminal.hom_ext _ _⟩⟩`. Establish `h3 : IsProper (terminal.from (Spec (CommRingCat.of ℤ)))`.

Establish `: IsClosedImmersion (terminal.from (Spec (CommRingCat.of ℤ)))` using `inferInstance`. Use `infer_instance`. Establish `h2' : IsProper (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0))))` using `inferInstance`. Rewrite using `[e]`. Conclude with `MorphismProperty.comp_mem @IsProper _ _ h1 (MorphismProperty.comp_mem @IsProper _ _ h2' h3)`.
-/
lemma projective_line_over_integers_isProper : IsProper (terminal.from P1) := by
  have h1 : IsProper (Proj.toSpecZero 𝒜) := proj_proper
  have h2 : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0)))) :=
    IsClosedImmersion.spec_of_surjective _ zero_surj
  have e : terminal.from P1 = Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0))) ≫
      terminal.from (Spec (CommRingCat.of ℤ)) := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (CommRingCat.of ℤ))) :=
    ⟨⟨specZIsTerminal.from _, specZIsTerminal.hom_ext _ _, terminal.hom_ext _ _⟩⟩
  have h3 : IsProper (terminal.from (Spec (CommRingCat.of ℤ))) := by
    have : IsClosedImmersion (terminal.from (Spec (CommRingCat.of ℤ))) := inferInstance
    infer_instance
  have h2' : IsProper (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0)))) := inferInstance
  rw [e]
  exact MorphismProperty.comp_mem @IsProper _ _ h1 (MorphismProperty.comp_mem @IsProper _ _ h2' h3)

/- English proof (translation)
Introduce `S`. Use `⟨pullback (terminal.from P1) (terminal.from S), pullback.snd _ _, ?_, pullback.fst _ _, IsPullback.of_hasPullback _ _⟩` and prove the remaining obligations. Conclude with `MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) projective_line_over_integers_isProper`.
-/
theorem LineEx_of : LateralTheory.E.ChowLCut.LineEx := by
  intro S
  refine ⟨pullback (terminal.from P1) (terminal.from S), pullback.snd _ _, ?_, pullback.fst _ _,
    IsPullback.of_hasPullback _ _⟩
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) projective_line_over_integers_isProper

end LateralTheory.E.LineExPf

end
