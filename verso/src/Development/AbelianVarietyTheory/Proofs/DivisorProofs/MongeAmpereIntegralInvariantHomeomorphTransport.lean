import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt

namespace MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MaTransport

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def carryPartition (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A) :
    ChartPartition (tAtlas A h) where
  χ j := P.χ j ∘ h.symm
  smooth j k := by
    have e₁ : (P.χ j ∘ h.symm) ∘ ((tAtlas A h).chart k).symm = P.χ j ∘ (A.chart k).symm :=
      funext fun y => by simp [tAtlas_symm]
    rw [e₁]
    exact P.smooth j k
  nonneg j x := P.nonneg j _
  tsupport_subset j := fun x hx =>
    P.tsupport_subset j (tsupport_comp_subset_preimage (P.χ j) h.symm.continuous hx)
  sum_eq_one x := P.sum_eq_one (h.symm x)

/- English proof (translation)
Use `⟨fun x j => ?_, fun x x' y hy => ?_⟩` and prove the remaining obligations. Conclude with `hQ.1 (h x) j`. Take `⟨W, hW, hyW, G, hG, hd⟩` from `hQ.2 (h x) (h x') (h y) hy`. Use `⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, fun j => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `hG j`.

Conclude with `hd (h z) hz`.
-/
theorem isPotential_pullback (A : FinHolAtlas e X) (h : X ≃ₜ X') {Q : LocPot X'}
    (hQ : IsPotential (tAtlas A h) Q) : IsPotential A (Q.pullback h h.continuous) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · exact hQ.1 (h x) j
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hQ.2 (h x) (h x') (h y) hy
    refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, fun j => ?_, fun z hz => ?_⟩
    · exact hG j
    · exact hd (h z) hz

/- English proof (translation)
Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `P.χ j (h.symm (h ((A.chart j).symm y))) * g (h ((A.chart j).symm y)) * _ = P.χ j ((A.chart j).symm y) * g (h ((A.chart j).symm y)) * _`. Rewrite using `[h.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem integralWith_carry (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A)
    (Φ : Fin e → LocPot X') (g : X' → ℝ) :
    integralWith (tAtlas A h) (carryPartition A h P) Φ g =
      integralWith A P (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change P.χ j (h.symm (h ((A.chart j).symm y))) * g (h ((A.chart j).symm y)) * _ =
    P.χ j ((A.chart j).symm y) * g (h ((A.chart j).symm y)) * _
  rw [h.symm_apply_apply]
  rfl

/- English proof (translation)
Take `⟨P⟩` from `existsPartition A`. Establish `hΨ : ∀ i, IsPotential A ((Φ i).pullback h h.continuous)` using `fun i => isPotential_pullback A h (hΦ i)`. Rewrite using `[mIntEq (tAtlas A h) (carryPartition A h P) Φ hΦ g (mIntegrableCont _ Φ hΦ g hg), mIntEq A P _ hΨ (g ∘ h) (mIntegrableCont A _ hΨ _ (hg.comp h.continuous)), integralWith_carry]`.
-/
theorem mInt_tAtlas (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X]
    [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X')
    (Φ : Fin e → LocPot X') (g : X' → ℝ) (hΦ : ∀ i, IsPotential (tAtlas A h) (Φ i))
    (hg : Continuous g) :
    mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  obtain ⟨P⟩ := existsPartition A
  have hΨ : ∀ i, IsPotential A ((Φ i).pullback h h.continuous) :=
    fun i => isPotential_pullback A h (hΦ i)
  rw [mIntEq (tAtlas A h) (carryPartition A h P) Φ hΦ g (mIntegrableCont _ Φ hΦ g hg),
    mIntEq A P _ hΨ (g ∘ h) (mIntegrableCont A _ hΨ _ (hg.comp h.continuous)),
    integralWith_carry]

end GlobalTheory.CompanionTheory.MaTransport

end
end

end MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
/- English proof (translation)
Apply the tactic sequence `first | exact @MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | exact MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | (intros; apply MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas <;> assumption)`.
-/
theorem _root_.GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X] [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (Φ : Fin e → LocPot X') (g : X' → ℝ), (∀ i, IsPotential (tAtlas A h) (Φ i)) → Continuous g → mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  first | exact @MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | exact MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | (intros; apply MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas <;> assumption)

end
