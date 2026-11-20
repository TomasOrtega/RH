import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep UpperTheory.V.Lit.Dr

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
private theorem sand_split (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ) (p : HV E a) :
    sand (GeneralLinearGroup.map (pInf E) (GlobalTheory.UnitaryBC.splitCentre E a t)) p = (Real.exp t * Real.exp t) • p := by
  rw [GlobalTheory.UnitaryBC.splitCentre, pInf_infGL]
  refine Subtype.ext ?_
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp t • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  change Matrix.of (sand _ p).1 = (Real.exp t * Real.exp t) • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.V.Cj.A.splitFacts :
    SplitFacts := by
  intro E _ _ _ a
  refine ⟨fun t => ⟨pFin_infGL _, _, mul_pos (Real.exp_pos t) (Real.exp_pos t), sand_split E a t⟩,
    fun r hr => ⟨Real.log r / 2, fun p => ?_⟩⟩
  rw [sand_split, ← Real.exp_add, add_halves, Real.exp_log hr]
