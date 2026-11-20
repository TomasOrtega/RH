import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Mult.geomTr :
    UpperTheory.V.Z.Mult.GeomTr := by
  intro E _ _ _ hU n hn S hS lam K' hK'
  refine ⟨dimW_ne_zero lam, fun f hf hsep => ?_⟩
  have hOrb : geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) =
      geomURat lam (fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) := by
    unfold geomURat
    refine finsum_congr fun c => ?_
    split_ifs with hc
    · exact congrArg (_ * ·) (GlobalTheory.T.twistedOrbitalIntegral_product_eq_finprod E hU n hn S hS K' hK' f hf c.rep hc)
    · rfl
  rw [GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses E hU n hn S hS lam K' hK' f hf hsep, hOrb,
    GlobalTheory.PreStabU.geomURat_eq_geomU E hU n hn S hS lam K' hK' f hf hsep]
