import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Wt.evLem_of :
    UpperTheory.Gal.Wt.EvLem := by
  intro M X Z _ _ _ ev hsep T Φ hT L
  let W : Submodule ℂ (Module.Dual ℂ M) := Submodule.span ℂ (Set.range ev)
  have hbot : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Submodule.mem_dualCoannihilator] at hm
    exact (Submodule.mem_bot ℂ).2 (hsep m fun x => hm _ (Submodule.subset_span ⟨x, rfl⟩))
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hbot, Submodule.dualAnnihilator_bot]
  let φ : Module.Dual ℂ M →ₗ[ℂ] (Z → ℂ) :=
    { toFun := fun l z => l (Φ z)
      map_add' := fun a b => by
        ext z
        simp
      map_smul' := fun c a => by
        ext z
        simp }
  have hle : W ≤ T.comap φ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hT x
  have hL : L ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  exact hle hL
