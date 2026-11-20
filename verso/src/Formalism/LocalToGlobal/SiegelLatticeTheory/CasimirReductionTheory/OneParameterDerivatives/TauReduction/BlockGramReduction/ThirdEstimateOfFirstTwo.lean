import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h` using `I.L_span`. Establish `h0 : Submodule.span I.E (I.L : Set (Fin I.n → I.E)) = ⊥`. Rewrite using `[Submodule.span_eq_bot]`.

Conclude with `hcon`. Rewrite `h` using `[h0]`. Use `haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩`. Conclude with `bot_ne_top h`.
-/
theorem exists_ne_zero_mem_L (I : AutInst) (hn : 1 ≤ I.n) : ∃ l ∈ I.L, l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := I.L_span
  have h0 : Submodule.span I.E (I.L : Set (Fin I.n → I.E)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact hcon
  rw [h0] at h
  haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact bot_ne_top h

/- English proof (translation)
Introduce `I hn x`. Take `⟨m, hm1, _, hLm⟩` from `h0 I x`. Take `⟨M, _, hM⟩` from `h1 I x`. Take `⟨l, hlL, hl0⟩` from `exists_ne_zero_mem_L I hn`. Establish `hml : ((m : I.E) • l) ∈ (M : Set (Fin I.n → I.E))`.

Rewrite using `[hM]`. Conclude with `hLm l hlL`. Establish `hm0 : ((m : I.E) • l) ≠ 0` using `smul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hl0`. Take `⟨t, htM, hspan, hli⟩` from `exists_linearIndependent I.E (M : Set (Fin I.n → I.E))`. Establish `htfin : t.Finite` using `hli.setFinite`.

Establish `hne : t.Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite `hspan` using `[h, Submodule.span_empty]`. Establish `h2 : ((m : I.E) • l) ∈ Submodule.span I.E (M : Set (Fin I.n → I.E))` using `Submodule.subset_span hml`.

Rewrite `h2` using `[← hspan]`. Conclude with `hm0 ((Submodule.mem_bot _).mp h2)`. Use `haveI := htfin.fintype`. Set `e` to `(Fintype.equivFin t).symm`. Use `⟨⟨Fintype.card t, ?_, fun a => (e a : Fin I.n → I.E), ?_, M, ?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `Fintype.card_pos_iff.mpr hne.to_subtype`. Conclude with `hli.comp _ e.injective`. Conclude with `hM.le`. Introduce `a`. Conclude with `htM (e a).2`.

Introduce `v hv`. Establish `hr : Set.range (fun a => (e a : Fin I.n → I.E)) = t`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `(e a).2`. Introduce `hv`. Conclude with `⟨e.symm ⟨v, hv⟩, by simp⟩`. Rewrite using `[hr, hspan]`. Conclude with `Submodule.subset_span hv`.
-/
theorem third_estimate_of_first_two (h0 : LatticeCommensurable) (h1 : LatticeFinitelyGenerated) : SubmoduleExists := by
  intro I hn x
  obtain ⟨m, hm1, _, hLm⟩ := h0 I x
  obtain ⟨M, _, hM⟩ := h1 I x
  obtain ⟨l, hlL, hl0⟩ := exists_ne_zero_mem_L I hn
  have hml : ((m : I.E) • l) ∈ (M : Set (Fin I.n → I.E)) := by
    rw [hM]
    exact hLm l hlL
  have hm0 : ((m : I.E) • l) ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hl0
  obtain ⟨t, htM, hspan, hli⟩ := exists_linearIndependent I.E (M : Set (Fin I.n → I.E))
  have htfin : t.Finite := hli.setFinite
  have hne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Submodule.span_empty] at hspan
    have h2 : ((m : I.E) • l) ∈ Submodule.span I.E (M : Set (Fin I.n → I.E)) := Submodule.subset_span hml
    rw [← hspan] at h2
    exact hm0 ((Submodule.mem_bot _).mp h2)
  haveI := htfin.fintype
  let e := (Fintype.equivFin t).symm
  refine ⟨⟨Fintype.card t, ?_, fun a => (e a : Fin I.n → I.E), ?_, M, ?_, ?_, ?_⟩⟩
  · exact Fintype.card_pos_iff.mpr hne.to_subtype
  · exact hli.comp _ e.injective
  · exact hM.le
  · intro a
    exact htM (e a).2
  · intro v hv
    have hr : Set.range (fun a => (e a : Fin I.n → I.E)) = t := by
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        exact (e a).2
      · intro hv
        exact ⟨e.symm ⟨v, hv⟩, by simp⟩
    rw [hr, hspan]
    exact Submodule.subset_span hv

end Formalism.L2.SG.Pf.Tau
