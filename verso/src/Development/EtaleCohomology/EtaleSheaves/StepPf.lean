import Development.EtaleCohomology.EtaleSheaves.AICAcycPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.AICAcycPf

namespace LateralTheory.E.StepPf

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hfne : (Set.range f).Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`.

Conclude with `hne.2 (by simpa [h] using hc)`. Establish `hgne : (Set.range g).Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Conclude with `hne.1 (by simpa [h] using hc)`.

Establish `hirr : IsPreirreducible (Set.univ : Set X)` using `(IrreducibleSpace.isIrreducible_univ X).isPreirreducible`. Take `⟨x, -, hxf, hxg⟩` from `hirr _ _ f.isOpenEmbedding.isOpen_range g.isOpenEmbedding.isOpen_range (by simpa using hfne) (by simpa using hgne)`. Take `⟨u, rfl⟩` from `hxf`. Take `⟨v, hv⟩` from `hxg`. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) u v hv.symm`.

Conclude with `hW ⟨z⟩`.
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
Establish `: Surjective g` using `⟨Set.range_eq_univ.mp hg⟩`. Establish `: IsIso g` using `(isIso_iff_isOpenImmersion_and_surjective g).mpr ⟨inferInstance, inferInstance⟩`. Conclude with `acyc_of_iso q (asIso g).symm h`.
-/
theorem acyc_of_surj (q : ℕ) {V X : Scheme.{0}} (g : V ⟶ X) [IsOpenImmersion g] (hg : Set.range g = Set.univ)
    (h : Acyc q (sch.obj V)) : Acyc q (sch.obj X) := by
  have : Surjective g := ⟨Set.range_eq_univ.mp hg⟩
  have : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).mpr ⟨inferInstance, inferInstance⟩
  exact acyc_of_iso q (asIso g).symm h

/- English proof (translation)
Introduce `hyp hMV hZ q U V X f g _ _ hc hX hU hV hq hAU hAV hAW`. Establish `hXi : IsIntegral X` using `hX.1`. Distinguish the cases in `hW : Nonempty ↥(pullback f g : Scheme.{0})`. Establish `hAW'` using `hAW hW`. Establish `: IsIntegral U` using `hU.1`.

Use `hW` as an intermediate fact. Establish `: IsIntegral (pullback f g : Scheme.{0})` using `isIntegral_of_isOpenImmersion (pullback.fst f g ≫ f)`. Establish `hqU : IsUnit (q : Γ(U, ⊤))`. Use `hq.map f.appTop.hom` as an intermediate fact. Simplify using `using this`.

Introduce `n i hn`. Take `⟨δ, hex, -⟩` from `hMV hyp (ZMod q) (tw q i)`. Take `⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1` from `⟨n - 1, by ring⟩`. Establish `hsU` using `hAU (m + 1) i hn`. Establish `hsV` using `hAV (m + 1) i hn`.

Take `⟨-, h2, h3⟩` from `hex f g hc m`. Prove the components needed by the constructor for the conclusion. It suffices to establish `h0 : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 by`. Introduce `a b`. Rewrite using `[h0 a, h0 b]`.

Introduce `x`. Take `⟨w, hw⟩` from `(h3 x).mp ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩`. Rewrite using `[← hw]`. Break down `lt_or_eq_of_le (show (0 : ℤ) ≤ m by omega) with hm | hm` into its components or cases. Establish `hsW` using `hAW' m i hm`.

Rewrite using `[Subsingleton.elim w 0, map_zero]`. Substitute `hm` using the available equality. Rewrite using `[h2]`. Take `⟨a, ha⟩` from `(hZ hyp q (pullback.fst f g) hU inferInstance hqU i).2 w`. Conclude with `⟨a, 0, by rw [map_zero, sub_zero]; exact ha.symm⟩`.

Break down `empty_case f g hc hW with h | h` into its components or cases. Conclude with `acyc_of_surj q f h hAU`. Conclude with `acyc_of_surj q g h hAV`.
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
