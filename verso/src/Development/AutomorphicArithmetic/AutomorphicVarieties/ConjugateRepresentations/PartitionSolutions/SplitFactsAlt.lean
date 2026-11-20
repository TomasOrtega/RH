import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep UpperTheory.V.Lit.Dr

/- English proof (translation)
Rewrite using `[GlobalTheory.UnitaryBC.splitCentre, pInf_infGL]`. Use `Subtype.ext ?_` and prove the remaining obligations. Establish `h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)) : GL (Fin a) (Cinf E)).val = Real.exp t • (1 : Matrix (Fin a) (Fin a) (Cinf E))`. Use extensionality with `i j w`. Apply the tactic sequence `by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]`.

Express the relevant statement in the definitionally equal form `Matrix.of (sand _ p).1 = (Real.exp t * Real.exp t) • Matrix.of p.1`. Rewrite using `[sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]`.
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
Introduce `E _ _ _ a`. Use `⟨fun t => ⟨pFin_infGL _, _, mul_pos (Real.exp_pos t) (Real.exp_pos t), sand_split E a t⟩, fun r hr => ⟨Real.log r / 2, fun p => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[sand_split, ← Real.exp_add, add_halves, Real.exp_log hr]`.
-/
theorem UpperTheory.V.Cj.A.splitFacts :
    SplitFacts := by
  intro E _ _ _ a
  refine ⟨fun t => ⟨pFin_infGL _, _, mul_pos (Real.exp_pos t) (Real.exp_pos t), sand_split E a t⟩,
    fun r hr => ⟨Real.log r / 2, fun p => ?_⟩⟩
  rw [sand_split, ← Real.exp_add, add_halves, Real.exp_log hr]
