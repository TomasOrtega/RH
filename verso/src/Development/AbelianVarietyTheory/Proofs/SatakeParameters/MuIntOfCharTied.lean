import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.MuIntegral

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem muInt_of_charTied : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Formalism.L2.Host.NCharTied D C nch Tp → MuInt D.nd D.naut := by
  intro D C nch Tp hT i τ z hz
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hmu := hT.muC i j hjj
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin (D.nd.mu i)
  have hinf : (Tp.tup (D.nd.mu i) j).HasInfQ (Formalism.L2.Host.embPsi D.host) (fun g => -Formalism.L2.Host.eExp D j g) :=
    (C.isMu0 j).inf.mul_triv (GlobalTheory.TypeValues.inf_eq_one _ hn ho)
  rw [← hmu] at hinf
  have key := hT.infG _ _ hinf
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
  obtain ⟨m, hm⟩ := (D.hc (D.eTau.symm (D.eTau ρ))).e_int j
  have hm' : Formalism.L2.Host.eExp D j (D.eTau ρ) = m := hm
  rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
  · have ht : τ = Formalism.L2.Host.embPsi D.host (D.eTau ρ) := h.symm
    rw [ht, (key (D.eTau ρ)).1] at hz
    refine ⟨-m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring
  · have ht : τ = (starRingEnd ℂ).comp (Formalism.L2.Host.embPsi D.host (D.eTau ρ)) := by
      rw [← h]; ext x; rfl
    rw [ht, (key (D.eTau ρ)).2] at hz
    refine ⟨m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring

end GlobalTheory.MuIntegral
