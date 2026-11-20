import Development.EtaleCohomology.EtaleSheaves.HensCut

open Polynomial

namespace LateralTheory.E.MonicSplitsPf

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hp hn`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Simplify using `using hp.natDegree_eq_zero.mp hn`. Consider the case `succ n ih`. Introduce `p hp hn`. Take `⟨a, ha⟩` from `hA p hp (by omega)`. Establish `hroot : IsRoot p a` using `ha`.

Establish `hmul` using `(mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr hroot`. Use `set q := p /ₘ (X - C a) with hq`. Establish `hqm : q.Monic` using `Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hmul]; exact hp)`. Establish `hqd : q.natDegree = n`. Rewrite using `[hq, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C, hn]`.

Use linear arithmetic over natural numbers and integers. Take `⟨s, hs⟩` from `ih q hqm hqd`. Use `⟨a ::ₘ s, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]`.
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
Introduce `R _ _ hA p hp`. Conclude with `selfDualLattice_projection_mem_of_unit_length R hA p.natDegree p hp rfl`.
-/
theorem MonicSplits_of : LateralTheory.E.HensCut.MonicSplits := by
  intro R _ _ hA p hp
  exact selfDualLattice_projection_mem_of_unit_length R hA p.natDegree p hp rfl

end LateralTheory.E.MonicSplitsPf
