import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

/- English proof (translation)
Establish `hsub : ∀ a b : Sp ℂ, a = b` using `fun a b => Subsingleton.elim (α := PrimeSpectrum ℂ) a b`. Prove the components needed by the constructor for the conclusion. Introduce `h p _`. Establish `hq : x.base ((spMap σ).base p) ∈ U` using `h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)`. Rewrite `hq` using `[hsub ((spMap σ).base p) p]`. Then use the resulting hypothesis.

Introduce `h p _`. Conclude with `h (show (spMap σ).base p ∈ (⊤ : (Sp ℂ).Opens) from trivial)`.
-/
theorem top_le_spMap_comp_iff {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  have hsub : ∀ a b : Sp ℂ, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum ℂ) a b
  constructor
  · intro h p _
    have hq : x.base ((spMap σ).base p) ∈ U := h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    rwa [hsub ((spMap σ).base p) p] at hq
  · intro h p _
    exact h (show (spMap σ).base p ∈ (⊤ : (Sp ℂ).Opens) from trivial)

/- English proof (translation)
Establish `h` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)`. Conclude with `congrArg (fun φ => CommRingCat.Hom.hom φ z) h`.
-/
private theorem gammaSpecIso_appLE_spMap_apply (z : Γ(Sp ℂ, ⊤)) (σ : ℂ →+* ℂ)
    (e : (⊤ : (Sp ℂ).Opens) ≤ (spMap σ) ⁻¹ᵁ ⊤) :
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
      ((CommRingCat.Hom.hom (Scheme.Hom.appLE (spMap σ) ⊤ ⊤ e)) z) =
    σ ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) z) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
  exact congrArg (fun φ => CommRingCat.Hom.hom φ z) h

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'`. Distinguish the cases in `hx : ⊤ ≤ x ⁻¹ᵁ U`. Establish `hc : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U` using `(top_le_spMap_comp_iff σ x U).2 hx`. Rewrite using `[dif_pos hc, dif_pos hx]`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt`.

Rewrite using `[← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ hx (by simp)]`. Rewrite using `[CommRingCat.hom_comp, RingHom.comp_apply]`. Conclude with `gammaSpecIso_appLE_spMap_apply _ σ _`. Establish `hc : ¬ ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U` using `fun h => hx ((top_le_spMap_comp_iff σ x U).1 h)`. Rewrite using `[dif_neg hc, dif_neg hx, map_zero]`.
-/
theorem valAt'_spMap_comp {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (spMap σ ≫ x) U f = σ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ U
  · have hc : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := (top_le_spMap_comp_iff σ x U).2 hx
    rw [dif_pos hc, dif_pos hx]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
    rw [← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ hx (by simp)]
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact gammaSpecIso_appLE_spMap_apply _ σ _
  · have hc : ¬ ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun h => hx ((top_le_spMap_comp_iff σ x U).1 h)
    rw [dif_neg hc, dif_neg hx, map_zero]

/- English proof (translation)
Introduce `b hb`. Take `⟨L, hL⟩` from `hg (star b) hb`. Establish `h1 : HasFDerivWithinAt (star : (Fin m → ℂ) → (Fin m → ℂ)) ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) (star ⁻¹' S) b` using `((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)).hasFDerivWithinAt`. Establish `h2 : HasFDerivWithinAt g (L.restrictScalars ℝ) S (star b)` using `hL.restrictScalars ℝ`. Establish `h3` using `h2.comp b h1 (fun y hy => hy)`.

Establish `hR` using `((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasFDerivWithinAt b h3`. Set `L' : (Fin m → ℂ) →L[ℂ] ℂ` to `{ toFun := fun v => star (L (star v)) map_add' := fun v w => by simp [star_add, map_add] map_smul' := fun c v => by simp [star_smul, map_smul] cont := continuous_star.comp (L.continuous.comp continuous_star) }`. Conclude with `⟨L', HasFDerivWithinAt.of_restrictScalars (𝕜 := ℝ) hR (by ext v; rfl)⟩`.
-/
private theorem differentiableOn_conj_comp_star {m : ℕ} {g : (Fin m → ℂ) → ℂ} {S : Set (Fin m → ℂ)}
    (hg : DifferentiableOn ℂ g S) :
    DifferentiableOn ℂ (fun b => starRingEnd ℂ (g (star b))) (star ⁻¹' S) := by
  intro b hb
  obtain ⟨L, hL⟩ := hg (star b) hb
  have h1 : HasFDerivWithinAt (star : (Fin m → ℂ) → (Fin m → ℂ))
      ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) (star ⁻¹' S) b :=
    ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt g (L.restrictScalars ℝ) S (star b) := hL.restrictScalars ℝ
  have h3 := h2.comp b h1 (fun y hy => hy)
  have hR := ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasFDerivWithinAt b h3
  let L' : (Fin m → ℂ) →L[ℂ] ℂ :=
    { toFun := fun v => star (L (star v))
      map_add' := fun v w => by simp [star_add, map_add]
      map_smul' := fun c v => by simp [star_smul, map_smul]
      cont := continuous_star.comp (L.continuous.comp continuous_star) }
  exact ⟨L', HasFDerivWithinAt.of_restrictScalars (𝕜 := ℝ) hR (by ext v; rfl)⟩

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo at hy ⊢`. Introduce `U f`. Take `⟨ho, hd⟩` from `hy U f`. Establish `hset : {b | b ∈ star ⁻¹' B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (spMap (starRingEnd ℂ) ≫ y (star b)).base).obj U} = star ⁻¹' {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (y b).base).obj U}`. Use extensionality with `b`.

Conclude with `and_congr_right fun _ => top_le_spMap_comp_iff (starRingEnd ℂ) (y (star b)) U`. Rewrite using `[hset]`. Use `⟨ho.preimage continuous_star, ?_⟩` and prove the remaining obligations. Use `(differentiableOn_conj_comp_star hd).congr ?_` and prove the remaining obligations. Introduce `b _`.

Conclude with `valAt'_spMap_comp (starRingEnd ℂ) (y (star b)) U f`.
-/
theorem isHolTo_conj (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (hy : IsHolTo B y) :
    IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ star ⁻¹' B ∧
        ⊤ ≤ (TopologicalSpace.Opens.map (spMap (starRingEnd ℂ) ≫ y (star b)).base).obj U}
      = star ⁻¹' {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (y b).base).obj U} := by
    ext b
    exact and_congr_right fun _ => top_le_spMap_comp_iff (starRingEnd ℂ) (y (star b)) U
  rw [hset]
  refine ⟨ho.preimage continuous_star, ?_⟩
  refine (differentiableOn_conj_comp_star hd).congr ?_
  intro b _
  exact valAt'_spMap_comp (starRingEnd ℂ) (y (star b)) U f

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
