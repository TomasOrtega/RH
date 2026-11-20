import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

/- English proof (translation)
Introduce `V₁ _ _ D N₁ X C _ e T v c₀ h hv`. Take `⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅⟩` from `h`. Use `⟨(algebraMap V₁ (FractionRing V₁) v) • th, g, b, w, h₁, h₂, h₃, h₄, ?_, ⟨c₀, hv⟩⟩` and prove the remaining obligations. Introduce `mu c z J hJ`. Establish `H` using `h₅ mu c z J hJ`.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.DVR.sval_smul _ _ _ _ z hJ]`. Establish `e₁ : (lift (𝟙 (TF (R` using `V₁) (FractionRing V₁))) (g c).b).left ≫ (fst (TF (R := V₁) (FractionRing V₁)) D.P.A).left = 𝟙 _ := by`. Rewrite using `[← Over.comp_left, lift_fst, Over.id_left]`. Rewrite using `[e₁]`. Establish `e₂ : GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c * v)) = GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) v) * GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c))`.

Simplify using `only [GlobalTheory.UT.cst, map_mul]`. Rewrite using `[gs_mul _ z ⊤ trivial, mul_comm]`. Rewrite using `[e₂, _root_.mul_assoc, H]`. Simplify using `only [GlobalTheory.UT.cst, _root_.mul_assoc]`.
-/
theorem isThetaTerms_of_mul_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  intro V₁ _ _ D N₁ X C _ e T v c₀ h hv
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨(algebraMap V₁ (FractionRing V₁) v) • th, g, b, w, h₁, h₂, h₃, h₄, ?_, ⟨c₀, hv⟩⟩
  intro mu c z J hJ
  have H := h₅ mu c z J hJ
  rw [ReciprocityTheory.ChartRestriction.G.DVR.sval_smul _ _ _ _ z hJ]
  have e₁ : (lift (𝟙 (TF (R := V₁) (FractionRing V₁))) (g c).b).left ≫
      (fst (TF (R := V₁) (FractionRing V₁)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  rw [e₁]
  have e₂ : GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c * v)) =
      GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) v) *
        GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c)) := by
    simp only [GlobalTheory.UT.cst, map_mul]
    rw [gs_mul _ z ⊤ trivial, mul_comm]
  rw [e₂, _root_.mul_assoc, H]
  simp only [GlobalTheory.UT.cst, _root_.mul_assoc]

end GlobalTheory.Poinc.Sep
