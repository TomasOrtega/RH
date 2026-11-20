import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenMul
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Establish an intermediate fact.

Substitute using the available equality. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. It suffices to derive a contradiction. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Int.Div.dGenMul_of :
    DGenMul := by
  classical
  intro a q B ha hc hG
  obtain ⟨α, rfl⟩ : ∃ α : Fin a → ℂˣ, Finset.univ.val.map α = B := by
    induction B using Quotient.inductionOn with
    | h l =>
      have hl : l.length = a := hc
      subst hl
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  refine UpperTheory.Gal.crystallineComparison.genMul_of ℂˣ a α ?_
  intro m hs hp
  have hne := hG α rfl
  unfold DGen at hne
  rw [map_mul] at hne
  have h3 := right_ne_zero_of_mul hne
  rw [map_prod] at h3
  have hle : ∀ i, m i < a + 1 := fun i => Nat.lt_succ_of_le
    (hs ▸ Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hone : ((1 : Fin (a + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  by_cases hm : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) = fun _ => 1
  · intro i
    have h := congrArg Fin.val (congrFun hm i)
    rw [hone] at h
    exact h
  · exfalso
    have hmem : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) ∈
        (Finset.univ : Finset (Fin a → Fin (a + 1))).filter
          (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩
    refine Finset.prod_ne_zero_iff.mp h3 _ hmem ?_
    have hp' : ∏ i, (α i : ℂ) ^ m i = ∏ i, (α i : ℂ) := by
      have h := congrArg Units.val hp
      simpa [Units.coe_prod] using h
    simpa [map_sub, map_prod, map_pow, MvPolynomial.aeval_X] using sub_eq_zero.mpr hp'
