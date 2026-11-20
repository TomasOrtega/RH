import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Introduce `hI p _ D G L R _ _ gb N' N X' X u hu π Φ hW`. Take `⟨-, o, ψ, φ, hT, rfl⟩` from `hW`. Establish `hψ : IsIso ψ` using `hI p D G L R gb X'.X X'.s N' N X'.univ o ψ u hu hT`. Establish `hl : IsIso ψ.left` using `inferInstanceAs (IsIso ((Over.forget _).map ψ))`. Establish `h₁ : IsPullback ψ.left X'.univ.A.hom o.A.hom (𝟙 _)` using `IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩`.

Establish `h₂` using `h₁.paste_horiz φ.cart.1`. Rewrite `h₂` using `[Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Gal.G3.pWitCart :
    TransIso → WitCart := by
  intro hI p _ D G L R _ _ gb N' N X' X u hu π Φ hW
  obtain ⟨-, o, ψ, φ, hT, rfl⟩ := hW
  have hψ : IsIso ψ := hI p D G L R gb X'.X X'.s N' N X'.univ o ψ u hu hT
  have hl : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget _).map ψ))
  have h₁ : IsPullback ψ.left X'.univ.A.hom o.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz φ.cart.1
  rwa [Category.id_comp] at h₂
