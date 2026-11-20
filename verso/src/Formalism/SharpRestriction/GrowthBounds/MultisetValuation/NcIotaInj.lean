import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

abbrev nc_iota (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : Formalism.MainNotions.G.HH D :=
  t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)

include hL ht0 in
/- English proof (translation)
Establish an intermediate fact. Simplify by unfolding definitions. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem nc_n_eq : (D.gat u w hg).P.n' (Y.vOf u w hg t0) = addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  exact (h t0 ht0).1

include hL ht0 in
/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem nc_iota_inj : Function.Injective (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  intro s s' hss
  have hs := lt_of_lt_of_eq s.isLt hn
  have hs' := lt_of_lt_of_eq s'.isLt hn
  exact Fin.ext (nsmul_injOn_Iio_addOrderOf hs hs' (add_left_cancel hss))

include hL ht0 in
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify by unfolding definitions. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem nc_topsOn : Formalism.MainNotions.G.topsOn X (D.what₂.places.resChar w) t0 =
    ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).image (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  have hst := nc_step (D := D) hg
  have hr : t0 ∈ Finset.univ.image (X.bs (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))) := by
    rw [← hst]; exact ht0
  have hb := nc_bs_rep X _ t0 hr
  have hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := addOrderOf_pos _
  ext t
  simp only [Formalism.MainNotions.G.topsOn, Finset.mem_filter, Finset.mem_image, hst]
  constructor
  · rintro ⟨htT, hbt⟩
    obtain ⟨i, hi⟩ := X.bs_orb (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) t
    rw [hbt] at hi
    have hlt : i % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) <
        (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by
      rw [hn]; exact Nat.mod_lt _ hpos
    refine ⟨⟨_, hlt⟩, ?_, ?_⟩
    · rw [((h t0 ht0).2 _).2.1]
      simp only [mod_addOrderOf_nsmul, hi]
      exact htT
    · simp only [nc_iota, mod_addOrderOf_nsmul, hi]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨((h t0 ht0).2 s).2.1.1 hs, ?_⟩
    simp only [nc_iota]
    rw [nc_bs_iter, hb]

include hL ht0 in
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify by unfolding definitions. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem nc_isV (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) :
    Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) ↔ ¬ IsOddPos s := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  have hst := nc_step (D := D) hg
  have hr : t0 ∈ Finset.univ.image (X.bs (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))) := by
    rw [← hst]; exact ht0
  have hb := nc_bs_rep X _ t0 hr
  have hnP : Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) =
      addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
    simp only [Formalism.MainNotions.G.nP, if_neg (nc_notSg (D := D) hg)]
  have hs := lt_of_lt_of_eq s.isLt hn
  have key : ¬ IsOddPos s ↔ Even s.val := by
    show ¬ (s.val % 2 = 1) ↔ _
    rw [← Nat.odd_iff, Nat.not_odd_iff_even]
  rw [key]
  simp only [Formalism.MainNotions.G.IsV, hst, hnP, nc_iota, nc_bs_iter, hb]
  constructor
  · rintro ⟨i, hi, hev, heq⟩
    have hi' := nsmul_injOn_Iio_addOrderOf hi hs (add_left_cancel heq)
    rw [← hi']
    exact hev
  · intro hev
    exact ⟨s.val, hs, hev, rfl⟩

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
