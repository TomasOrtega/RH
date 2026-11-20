import Development.EtaleCohomology.EtaleSheaves.ChowLCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineExPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℤ

/- English proof (translation)
Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
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
A detailed English derivation is pending.
-/
lemma proj_proper : IsProper (Proj.toSpecZero 𝒜) := inferInstance

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem LineEx_of : LateralTheory.E.ChowLCut.LineEx := by
  intro S
  refine ⟨pullback (terminal.from P1) (terminal.from S), pullback.snd _ _, ?_, pullback.fst _ _,
    IsPullback.of_hasPullback _ _⟩
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) projective_line_over_integers_isProper

end LateralTheory.E.LineExPf

end
