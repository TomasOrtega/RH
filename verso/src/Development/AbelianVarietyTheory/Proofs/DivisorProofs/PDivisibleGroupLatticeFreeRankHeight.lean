import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatumStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem GlobalTheory.PDivLat.latt_free_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → Module.Free (Ainf p O) (latt G) ∧ Module.Finite (Ainf p O) (latt G) ∧ Module.finrank (Ainf p O) (latt G) = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  obtain ⟨D, e, fil, _lie, hal, _⟩ := hG
  obtain ⟨L, -⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
  haveI : Nontrivial (PreTilt O p) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  refine ⟨Module.Free.of_equiv L, Module.Finite.equiv L, ?_⟩
  rw [← L.finrank_eq, Module.finrank_fin_fun]
