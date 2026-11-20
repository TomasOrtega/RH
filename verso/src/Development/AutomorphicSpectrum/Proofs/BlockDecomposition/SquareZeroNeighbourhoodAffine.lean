import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.SectionNbhd

/- English proof (translation)
Introduce `R _ U t e _ het`. Establish `hte : ∀ q : Sp R, t (e q) = q` using `fun q => by`. Use `congr($(het) q)` as an intermediate fact. Simplify using `using this`. Use `set c := (e.ker ^ 2).subschemeι with hc`.

Establish `hrange : ∀ x, ∃ q : Sp R, c x = e q`. Introduce `x`. Establish `h1 : c x ∈ Set.range c` using `⟨x, rfl⟩`. Rewrite `h1` using `[hc, Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow _ _ two_ne_zero, Scheme.Hom.support_ker, e.isClosedEmbedding.isClosed_range.closure_eq]`. Take `⟨q, hq⟩` from `h1`.

Conclude with `⟨q, hq.symm⟩`. Establish `haff : IsAffineHom (c ≫ t)`. Use `isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_` and prove the remaining obligations. Take `⟨V₀, hV₀, hyV₀, -⟩` from `exists_isAffineOpen_mem_and_subset (x := e y) (U := ⊤) trivial`. Take `⟨f, hfle, hyf⟩` from `(isAffineOpen_top (Sp R)).exists_basicOpen_le (V := e ⁻¹ᵁ V₀) ⟨y, hyV₀⟩ trivial`.

Use `⟨(Sp R).basicOpen f, hyf, (isAffineOpen_top (Sp R)).basicOpen f, ?_⟩` and prove the remaining obligations. Establish `hV : IsAffineOpen (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f)`. Rewrite using `[Scheme.preimage_basicOpen]`. Establish `h` using `Scheme.basicOpen_res U (V := V₀) (t.app ⊤ f) (homOfLE le_top).op`. Rewrite using `[← h]`.

Conclude with `hV₀.basicOpen _`. Establish `heq : (c ≫ t) ⁻¹ᵁ (Sp R).basicOpen f = c ⁻¹ᵁ (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hx' : t (c x) ∈ (Sp R).basicOpen f` using `hx`. Use `⟨?_, hx'⟩` and prove the remaining obligations. Take `⟨q, hq⟩` from `hrange x`. Rewrite `hx'` using `[hq, hte]`. Establish `: e q ∈ V₀` using `hfle hx'`.

Simplify `this` using `[hq]`. Introduce `hx`. Conclude with `hx.2`. Rewrite using `[heq]`. Conclude with `hV.preimage c`.

Conclude with `isAffine_of_isAffineHom (c ≫ t)`.
-/
theorem isAffine_subscheme_ker_sq :
    ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U)
      [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by
  intro R _ U t e _ het
  have hte : ∀ q : Sp R, t (e q) = q := fun q => by
    have := congr($(het) q)
    simpa using this
  set c := (e.ker ^ 2).subschemeι with hc
  have hrange : ∀ x, ∃ q : Sp R, c x = e q := by
    intro x
    have h1 : c x ∈ Set.range c := ⟨x, rfl⟩
    rw [hc, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_pow _ _ two_ne_zero, Scheme.Hom.support_ker,
      e.isClosedEmbedding.isClosed_range.closure_eq] at h1
    obtain ⟨q, hq⟩ := h1
    exact ⟨q, hq.symm⟩
  have haff : IsAffineHom (c ≫ t) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := e y) (U := ⊤) trivial
    obtain ⟨f, hfle, hyf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le
      (V := e ⁻¹ᵁ V₀) ⟨y, hyV₀⟩ trivial
    refine ⟨(Sp R).basicOpen f, hyf, (isAffineOpen_top (Sp R)).basicOpen f, ?_⟩
    have hV : IsAffineOpen (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      rw [Scheme.preimage_basicOpen]
      have h := Scheme.basicOpen_res U (V := V₀) (t.app ⊤ f) (homOfLE le_top).op
      rw [← h]
      exact hV₀.basicOpen _
    have heq : (c ≫ t) ⁻¹ᵁ (Sp R).basicOpen f = c ⁻¹ᵁ (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      ext x
      constructor
      · intro hx
        have hx' : t (c x) ∈ (Sp R).basicOpen f := hx
        refine ⟨?_, hx'⟩
        obtain ⟨q, hq⟩ := hrange x
        rw [hq, hte] at hx'
        have : e q ∈ V₀ := hfle hx'
        simpa [hq] using this
      · intro hx
        exact hx.2
    rw [heq]
    exact hV.preimage c
  exact isAffine_of_isAffineHom (c ≫ t)

end GlobalTheory.CompanionTheory.SectionNbhd
