import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.PrTypeProof

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem typeSum_indep (D : D7) (i : D.nd.Loc) : iSupIndep (typeSum D i) := by
  intro o
  have hd : Disjoint {P | D.naut.ptV i P = o} {P | D.naut.ptV i P ≠ o} :=
    Set.disjoint_left.2 fun P h h' => h' h
  refine ((D.naut.typeV_indep i).disjoint_biSup_biSup hd).mono_right ?_
  refine iSup₂_le fun o' ho' => iSup₂_le fun P hP => ?_
  exact le_biSup (D.naut.typeV i) (show P ∈ {P | D.naut.ptV i P ≠ o} from fun e => ho' (hP.symm.trans e))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem typeV_le_typeSum (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) :
    D.naut.typeV i P ≤ typeSum D i (D.naut.ptV i P) :=
  le_biSup (D.naut.typeV i) (show P ∈ {Q | D.naut.ptV i Q = D.naut.ptV i P} from rfl)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → PrType D := by
  intro D hS i PI x hx
  classical
  let s := (hS i).some
  set v := D.nd.prMt i x with hvdef
  have hvtop : v ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ v).1 hvtop
  have hΦv : s.Φ v = ∑ y ∈ f.support, s.Φ (f y) := by
    rw [← hsum, Finsupp.sum, map_sum]
  have hn := s.split x
  have hind := typeSum_indep D i
  have hjx : D.what₂.jMt _ _ x ∈ typeSum D i (D.naut.ptV i PI) := typeV_le_typeSum D i PI hx
  have key : ∀ y, some y ≠ D.naut.ptV i PI → f y = 0 := by
    intro y hy
    by_cases hs : y ∈ f.support
    · have e : s.Φ (f y) = (D.what₂.jMt _ _ x - (D.what₂.jMt _ _ x - s.Φ v)) -
          ∑ y' ∈ f.support.erase y, s.Φ (f y') := by
        rw [sub_sub_cancel, hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : s.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o := by
        rw [e]
        refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.sum_mem _ fun y' hy' => ?_)
        · exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (Ne.symm hy) hjx)
        · exact Submodule.mem_iSup_of_mem none (Submodule.mem_iSup_of_mem (by simp) hn)
        · refine Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (s.eig y' _ (hf y')))
          exact fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')
      have h0 : s.Φ (f y) = 0 := (Submodule.disjoint_def.1 (hind (some y))) _ (s.eig y _ (hf y)) m2
      exact s.inj (h0.trans (map_zero s.Φ).symm)
    · exact Finsupp.notMem_support_iff.1 hs
  refine ⟨fun p hp => ?_, fun hp => ?_⟩
  · rw [← hsum, Finsupp.sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hyp : y = p
    · subst hyp; exact hf y
    · rw [key y (by rw [hp]; exact fun e => hyp (Option.some_injective _ e))]
      exact Submodule.zero_mem _
  · rw [← hsum, Finsupp.sum]
    exact Finset.sum_eq_zero fun y _ => key y (by rw [hp]; simp)

end GlobalTheory.PendOf.PrTypeProof

end
