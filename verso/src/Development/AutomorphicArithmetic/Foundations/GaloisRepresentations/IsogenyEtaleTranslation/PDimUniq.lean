import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

/- English proof (translation)
Use `letI := f.toAlgebra`. Establish `e₁ : Module.rank S Ω[S⁄R] = m` using `@Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ m hm`. Establish `e₂ : Module.rank S Ω[S⁄R] = n` using `@Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ n hn`. Conclude with `e₁.symm.trans e₂` after adjusting the coercions.
-/
private lemma relDim_eq_of_ringHom {R S : Type} [CommRing R] [CommRing S] [Nontrivial S] (f : R →+* S)
    {m n : ℕ} (hm : f.IsStandardSmoothOfRelativeDimension m)
    (hn : f.IsStandardSmoothOfRelativeDimension n) : m = n := by
  letI := f.toAlgebra
  have e₁ : Module.rank S Ω[S⁄R] = m :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ m hm
  have e₂ : Module.rank S Ω[S⁄R] = n :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ n hn
  exact_mod_cast e₁.symm.trans e₂

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hsub : s ⊆ nilradical S`. Introduce `t ht`. Use `haveI : Subsingleton (Localization.Away t) := hne t ht`.

Establish `h0 : algebraMap S (Localization.Away t) 1 = algebraMap S (Localization.Away t) 0` using `Subsingleton.elim _ _`. Take `⟨⟨c, hc⟩, hc'⟩` from `(IsLocalization.eq_iff_exists (Submonoid.powers t) _).1 h0`. Take `⟨k, rfl⟩` from `hc`. Conclude with `⟨k, by simpa using hc'⟩`. Establish `hle` using `Ideal.span_le.2 hsub`.

Rewrite `hle` using `[hs, top_le_iff]`. Establish `h1 : (1 : S) ∈ nilradical S` using `hle ▸ Submodule.mem_top`. Take `⟨k, hk⟩` from `h1`. Simplify using `at hk`.
-/
private lemma exists_nontrivial_away {S : Type} [CommRing S] [Nontrivial S] (s : Set S)
    (hs : Ideal.span s = ⊤) : ∃ t ∈ s, Nontrivial (Localization.Away t) := by
  by_contra hne
  push_neg at hne
  have hsub : s ⊆ nilradical S := by
    intro t ht
    haveI : Subsingleton (Localization.Away t) := hne t ht
    have h0 : algebraMap S (Localization.Away t) 1 = algebraMap S (Localization.Away t) 0 :=
      Subsingleton.elim _ _
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) _).1 h0
    obtain ⟨k, rfl⟩ := hc
    exact ⟨k, by simpa using hc'⟩
  have hle := Ideal.span_le.2 hsub
  rw [hs, top_le_iff] at hle
  have h1 : (1 : S) ∈ nilradical S := hle ▸ Submodule.mem_top
  obtain ⟨k, hk⟩ := h1
  simp at hk

/- English proof (translation)
Take `⟨U, hU, V, hV, hx, e, hmU⟩` from `hm.exists_isStandardSmoothOfRelativeDimension x`. Take `⟨s, hs, hst⟩` from `HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e`. Use `haveI : Nonempty V := ⟨⟨x, hx⟩⟩`. Take `⟨t, ht, hnt⟩` from `exists_nontrivial_away s hs`. Establish `hm'` using `(RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2 (Localization.Away t) t _ hmU`.

Conclude with `relDim_eq_of_ringHom _ hm' (hst t ht)`.
-/
private lemma relDim_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {m n : ℕ} (hm : SmoothOfRelativeDimension m f)
    (hn : SmoothOfRelativeDimension n f) (x : X) : m = n := by
  obtain ⟨U, hU, V, hV, hx, e, hmU⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hst⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨t, ht, hnt⟩ := exists_nontrivial_away s hs
  have hm' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
    (Localization.Away t) t _ hmU
  exact relDim_eq_of_ringHom _ hm' (hst t ht)

/- English proof (translation)
Introduce `Z s d d' hd hd' hZ`. Take `⟨z⟩` from `hZ`. Conclude with `relDim_eq s hd hd' z`.
-/
theorem dimUniq_of : DimUniq := by
  intro Z s d d' hd hd' hZ
  obtain ⟨z⟩ := hZ
  exact relDim_eq s hd hd' z

end UpperTheory.Gal.FixZ
