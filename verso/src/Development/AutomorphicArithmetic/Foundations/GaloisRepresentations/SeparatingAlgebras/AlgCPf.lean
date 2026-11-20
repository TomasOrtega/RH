import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Gen.algC_pf :
    UpperTheory.Gal.Gen.Alg → UpperTheory.Gal.Gen.AlgC := by
  intro hA l _ ι H _ _ hp P hP hcard
  let P' : Submodule (Qbar l) (H → Qbar l) :=
    { carrier := {f | (fun h => ι (f h)) ∈ P}
      zero_mem' := by
        show (fun h => ι ((0 : H → Qbar l) h)) ∈ P
        convert P.zero_mem using 1
        funext h
        simp
      add_mem' := by
        intro a b ha hb
        show (fun h => ι ((a + b) h)) ∈ P
        convert P.add_mem ha hb using 1
        funext h
        simp
      smul_mem' := by
        intro r a ha
        show (fun h => ι ((r • a) h)) ∈ P
        convert P.smul_mem (ι r) ha using 1
        funext h
        simp }
  let j : P ≃+ P' :=
    { toFun := fun c => ⟨fun h => ι.symm (c.1 h), by
        show (fun h => ι (ι.symm (c.1 h))) ∈ P
        simpa using c.2⟩
      invFun := fun f => ⟨fun h => ι (f.1 h), f.2⟩
      left_inv := by
        intro c
        ext h
        simp
      right_inv := by
        intro f
        ext h
        simp
      map_add' := by
        intro a b
        ext h
        simp }
  have hrank : Module.rank ℂ P = Module.rank (Qbar l) P' := by
    refine rank_eq_of_equiv_equiv (fun z => ι.symm z) j ι.symm.bijective ?_
    intro r m
    ext h
    simp [j, smul_eq_mul, map_mul]
  have hfin : Module.finrank ℂ P = Module.finrank (Qbar l) P' := by
    unfold Module.finrank
    rw [hrank]
  have hinv : ∀ c ∈ P', ∀ g : H, (fun h => c (h * g)) ∈ P' := by
    intro c hc g
    exact hP _ hc g
  obtain ⟨c, hc, hbound⟩ := hA (Qbar l) l H hp P' hinv (hfin ▸ hcard)
  refine ⟨fun h => ι (c h), hc, ?_⟩
  intro h
  simpa using hbound h
