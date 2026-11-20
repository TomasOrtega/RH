import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
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
