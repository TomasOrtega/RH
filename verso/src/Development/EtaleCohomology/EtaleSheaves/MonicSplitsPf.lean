import Development.EtaleCohomology.EtaleSheaves.HensCut

open Polynomial

namespace LateralTheory.E.MonicSplitsPf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem selfDualLattice_projection_mem_of_unit_length (R : Type) [CommRing R] [IsDomain R] (hA : GlobalTheory.EtC.AIC R) :
    ∀ n : ℕ, ∀ p : Polynomial R, p.Monic → p.natDegree = n →
      ∃ s : Multiset R, p = (s.map fun a => X - C a).prod := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    refine ⟨0, ?_⟩
    simpa using hp.natDegree_eq_zero.mp hn
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := hA p hp (by omega)
    have hroot : IsRoot p a := ha
    have hmul := (mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hmul]; exact hp)
    have hqd : q.natDegree = n := by
      rw [hq, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C, hn]; omega
    obtain ⟨s, hs⟩ := ih q hqm hqd
    refine ⟨a ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem MonicSplits_of : LateralTheory.E.HensCut.MonicSplits := by
  intro R _ _ hA p hp
  exact selfDualLattice_projection_mem_of_unit_length R hA p.natDegree p hp rfl

end LateralTheory.E.MonicSplitsPf
