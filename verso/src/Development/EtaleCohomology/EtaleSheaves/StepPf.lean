import Development.EtaleCohomology.EtaleSheaves.AICAcycPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.AICAcycPf

namespace LateralTheory.E.StepPf

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem empty_case {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hc : Set.range f ∪ Set.range g = Set.univ) [IrreducibleSpace X] (hW : ¬ Nonempty ↥(pullback f g : Scheme.{0})) :
    Set.range f = Set.univ ∨ Set.range g = Set.univ := by
  by_contra hne
  push Not at hne
  have hfne : (Set.range f).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne.2 (by simpa [h] using hc)
  have hgne : (Set.range g).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne.1 (by simpa [h] using hc)
  have hirr : IsPreirreducible (Set.univ : Set X) := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
  obtain ⟨x, -, hxf, hxg⟩ := hirr _ _ f.isOpenEmbedding.isOpen_range g.isOpenEmbedding.isOpen_range
    (by simpa using hfne) (by simpa using hgne)
  obtain ⟨u, rfl⟩ := hxf
  obtain ⟨v, hv⟩ := hxg
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) u v hv.symm
  exact hW ⟨z⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem acyc_of_surj (q : ℕ) {V X : Scheme.{0}} (g : V ⟶ X) [IsOpenImmersion g] (hg : Set.range g = Set.univ)
    (h : Acyc q (sch.obj V)) : Acyc q (sch.obj X) := by
  have : Surjective g := ⟨Set.range_eq_univ.mp hg⟩
  have : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).mpr ⟨inferInstance, inferInstance⟩
  exact acyc_of_iso q (asIso g).symm h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion. Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem Step_of : Step := by
  intro hyp hMV hZ q U V X f g _ _ hc hX hU hV hq hAU hAV hAW
  have hXi : IsIntegral X := hX.1
  by_cases hW : Nonempty ↥(pullback f g : Scheme.{0})
  · have hAW' := hAW hW
    have : IsIntegral U := hU.1
    have := hW
    have : IsIntegral (pullback f g : Scheme.{0}) := isIntegral_of_isOpenImmersion (pullback.fst f g ≫ f)
    have hqU : IsUnit (q : Γ(U, ⊤)) := by
      have := hq.map f.appTop.hom
      simpa using this
    intro n i hn
    obtain ⟨δ, hex, -⟩ := hMV hyp (ZMod q) (tw q i)
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
    have hsU := hAU (m + 1) i hn
    have hsV := hAV (m + 1) i hn
    obtain ⟨-, h2, h3⟩ := hex f g hc m
    constructor
    suffices h0 : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 by
      intro a b; rw [h0 a, h0 b]
    intro x
    obtain ⟨w, hw⟩ := (h3 x).mp ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw]
    rcases lt_or_eq_of_le (show (0 : ℤ) ≤ m by omega) with hm | hm
    · have hsW := hAW' m i hm
      rw [Subsingleton.elim w 0, map_zero]
    · subst hm
      rw [h2]
      obtain ⟨a, ha⟩ := (hZ hyp q (pullback.fst f g) hU inferInstance hqU i).2 w
      exact ⟨a, 0, by rw [map_zero, sub_zero]; exact ha.symm⟩
  · rcases empty_case f g hc hW with h | h
    · exact acyc_of_surj q f h hAU
    · exact acyc_of_surj q g h hAV

end LateralTheory.E.StepPf
