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
Establish `h0` using `hL u w hg`. Simplify using `only at h0`. Take `⟨-, -, -, -, -, -, h⟩` from `h0`. Conclude with `(h t0 ht0).1`.
-/
theorem nc_n_eq : (D.gat u w hg).P.n' (Y.vOf u w hg t0) = addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  exact (h t0 ht0).1

include hL ht0 in
/- English proof (translation)
Establish `hn` using `nc_n_eq X Y hT hL u w hg t0 ht0`. Introduce `s s' hss`. Establish `hs` using `lt_of_lt_of_eq s.isLt hn`. Establish `hs'` using `lt_of_lt_of_eq s'.isLt hn`. Conclude with `Fin.ext (nsmul_injOn_Iio_addOrderOf hs hs' (add_left_cancel hss))`.
-/
theorem nc_iota_inj : Function.Injective (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  intro s s' hss
  have hs := lt_of_lt_of_eq s.isLt hn
  have hs' := lt_of_lt_of_eq s'.isLt hn
  exact Fin.ext (nsmul_injOn_Iio_addOrderOf hs hs' (add_left_cancel hss))

include hL ht0 in
/- English proof (translation)
Establish `hn` using `nc_n_eq X Y hT hL u w hg t0 ht0`. Establish `h0` using `hL u w hg`. Simplify using `only at h0`. Take `⟨-, -, -, -, -, -, h⟩` from `h0`. Establish `hst` using `nc_step (D := D) hg`.

Establish `hr : t0 ∈ Finset.univ.image (X.bs (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)))`. Rewrite using `[← hst]`. Conclude with `ht0`. Establish `hb` using `nc_bs_rep X _ t0 hr`. Establish `hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))` using `addOrderOf_pos _`.

Use extensionality with `t`. Simplify using `only [Formalism.MainNotions.G.topsOn, Finset.mem_filter, Finset.mem_image, hst]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨htT, hbt⟩`. Take `⟨i, hi⟩` from `X.bs_orb (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) t`.

Rewrite `hi` using `[hbt]`. Establish `hlt : i % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) < (D.gat u w hg).P.n' (Y.vOf u w hg t0)`. Rewrite using `[hn]`. Conclude with `Nat.mod_lt _ hpos`. Use `⟨⟨_, hlt⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[((h t0 ht0).2 _).2.1]`. Simplify using `only [mod_addOrderOf_nsmul, hi]`. Conclude with `htT`. Simplify using `only [nc_iota, mod_addOrderOf_nsmul, hi]`. Introduce and unpack `⟨s, hs, rfl⟩`.

Use `⟨((h t0 ht0).2 s).2.1.1 hs, ?_⟩` and prove the remaining obligations. Simplify using `only [nc_iota]`. Rewrite using `[nc_bs_iter, hb]`.
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
Establish `hn` using `nc_n_eq X Y hT hL u w hg t0 ht0`. Establish `h0` using `hL u w hg`. Simplify using `only at h0`. Take `⟨-, -, -, -, -, -, h⟩` from `h0`. Establish `hst` using `nc_step (D := D) hg`.

Establish `hr : t0 ∈ Finset.univ.image (X.bs (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)))`. Rewrite using `[← hst]`. Conclude with `ht0`. Establish `hb` using `nc_bs_rep X _ t0 hr`. Establish `hnP : Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) = addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))`.

Simplify using `only [Formalism.MainNotions.G.nP, if_neg (nc_notSg (D := D) hg)]`. Establish `hs` using `lt_of_lt_of_eq s.isLt hn`. Establish `key : ¬ IsOddPos s ↔ Even s.val` using `by show ¬ (s.val % 2 = 1) ↔ _`. Rewrite using `[← Nat.odd_iff, Nat.not_odd_iff_even]`. Rewrite using `[key]`.

Simplify using `only [Formalism.MainNotions.G.IsV, hst, hnP, nc_iota, nc_bs_iter, hb]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, hev, heq⟩`. Establish `hi'` using `nsmul_injOn_Iio_addOrderOf hi hs (add_left_cancel heq)`. Rewrite using `[← hi']`.

Conclude with `hev`. Introduce `hev`. Conclude with `⟨s.val, hs, hev, rfl⟩`.
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
