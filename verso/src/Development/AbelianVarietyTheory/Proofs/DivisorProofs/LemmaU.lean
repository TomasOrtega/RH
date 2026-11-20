import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalUnitLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitIntegralAtPlaceForConfigurationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAIdeleUnitIntegralIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFixesSphericalVacuumVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitIndicatorIntegralValueStatement

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.UnrLocA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hψ : Continuous B.ψ` using `hX.base.std.1`. Establish `hM` using `hX.geo.hM`. Establish `hvac : G.M.vac v ∈ SB _` using `(hM.vac v).1`. Use function extensionality and compare the values at `y`. Rewrite using `[coneFin_of_fixed hμK hvac (GlobalTheory.T.stabilizer_fixes_spherical_vacuum_vector σ B G X om om' hX K hK v hv)]`.

Use `set S : Set (idelesAt E (evFin F v)) := {l | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} with hS`. Establish `key : ∀ l : idelesAt E (evFin F v), ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) (G.M.vac v)) y * (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) = S.indicator (fun l => (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) l * G₁.M.vac v y`. Introduce `l`. Rewrite using `[(locOp_rho G.M.co hψ v (shiftA H H' l.1) hvac).2]`. Distinguish the cases in `hl : l ∈ S`.

Rewrite using `[GlobalTheory.T.config_a_local_unit_levi σ B G G₁ H H' X om om' hX hC v l.1 l.2 hl, (hev v).1, Set.indicator_of_mem hl]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l.1)) (G.M.vac v)) = 0`. Take `⟨γ, hγv, hγ0, hγL, hne⟩` from `GlobalTheory.T.config_a_idele_unit_integral_identity σ B G G₁ H H' X om om' hX hC v l.1 l.2 hl`. Establish `hsb : schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l.1)) (G.M.vac v) ∈ SB _` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v _ _ hvac`.

Establish `h1` using `GlobalTheory.T.good_model_eigen_continuous B G.M G₁.M H.ι H'.ι (isoA H H') e he hψ hM hM₁ ei ev hei hev hfac v γ (Or.inl hγ0) hγv _ hsb`. Rewrite `h1` using `[GlobalTheory.T.orbit_integral_at_place_for_configuration σ B G G₁ H H' X om om' hX hC v γ hγv hγ0 hγL, map_smul]`. Establish `h2 : (GlobalTheory.LatVac.psiAt B.ψ v (evFin F v (symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) γ (shiftA H H' l.1))) - 1) • ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l.1)) (G.M.vac v)) = 0`. Rewrite using `[sub_smul, one_smul, h1, sub_self]`. Conclude with `(smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)`.

Rewrite using `[h0, Set.indicator_of_notMem hl]`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[key]`. Rewrite using `[integral_mul_const]`. Establish `hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt X.ν w`.

Introduce `w hw`. Rewrite using `[Chars.ν, div_eq_mul_inv]`. Conclude with `(hX.chars.unrα w fun h => hv (hw ▸ h)).mul (hX.chars.unrβ w fun h => hv (hw ▸ h)).inv`. Establish `hpos : 0 < (b + 2 - a') / 2` using `by have := hX.geo.eBig; omega`. Establish `h𝔞 : idA σ H.𝔟 H'.𝔟 ≠ 0`.

Take `⟨h𝔟0, -⟩` from `GlobalTheory.PlaneIdeal.plane_ideal_trivial σ B H G.V G₁.V 0 (b + 1) _ _ hX.base hX.geo.hV hC.hH (by omega) (by omega)`. Take `⟨h𝔠0, -⟩` from `GlobalTheory.T.adapted_plane_skew_ideal_coprime_lt σ B H' G.W G₁.W 0 (b + 1) _ _ hX.base hX.geo.hW hC.hH' (by omega) (by omega)`. Conclude with `mul_ne_zero (mul_ne_zero h𝔟0 (inv_ne_zero (conjI_ne_zero σ h𝔠0))) (inv_ne_zero diffE_ne_zero)`. Rewrite using `[GlobalTheory.T.local_unit_indicator_integral_value X.ν _ h𝔞 v hunr _ hpos μ hμ]`. Both sides reduce to the same expression.
-/
theorem lemmaU (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')) (hC : CfgA B G G₁ H H') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (hX : IsTriple B G X om om') (hM₁ : G₁.M.IsGood B.ψ)
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _)
    (hfac : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K) (v : Pl F) (hv : v ∉ X.T)
    (μK : Measure (KAt K (evFin F v))) (hμK : IsNormK K (evFin F v) μK)
    (μ : Measure (idelesAt E (evFin F v))) (hμ : IsNormE E v μ) :
    coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (G.M.vac v) =
      unrFac X.ν (idA σ H.𝔟 H'.𝔟) (((b + 2 - a') / 2 : ℕ) : ℂ) v • G₁.M.vac v := by
  have hψ : Continuous B.ψ := hX.base.std.1
  have hM := hX.geo.hM
  have hvac : G.M.vac v ∈ SB _ := (hM.vac v).1
  funext y
  rw [coneFin_of_fixed hμK hvac (GlobalTheory.T.stabilizer_fixes_spherical_vacuum_vector σ B G X om om' hX K hK v hv)]
  set S : Set (idelesAt E (evFin F v)) :=
    {l | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} with hS
  have key : ∀ l : idelesAt E (evFin F v),
      ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) (G.M.vac v)) y * (X.ν l.1 : ℂ) *
        ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) =
      S.indicator (fun l => (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) l * G₁.M.vac v y := by
    intro l
    rw [(locOp_rho G.M.co hψ v (shiftA H H' l.1) hvac).2]
    by_cases hl : l ∈ S
    · rw [GlobalTheory.T.config_a_local_unit_levi σ B G G₁ H H' X om om' hX hC v l.1 l.2 hl, (hev v).1, Set.indicator_of_mem hl]
      ring
    · have h0 : ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l.1)) (G.M.vac v)) = 0 := by
        obtain ⟨γ, hγv, hγ0, hγL, hne⟩ := GlobalTheory.T.config_a_idele_unit_integral_identity σ B G G₁ H H' X om om' hX hC v l.1 l.2 hl
        have hsb : schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l.1)) (G.M.vac v) ∈ SB _ :=
          GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v _ _ hvac
        have h1 := GlobalTheory.T.good_model_eigen_continuous B G.M G₁.M H.ι H'.ι (isoA H H') e he hψ hM hM₁ ei ev hei hev hfac v γ (Or.inl hγ0) hγv _ hsb
        rw [GlobalTheory.T.orbit_integral_at_place_for_configuration σ B G G₁ H H' X om om' hX hC v γ hγv hγ0 hγL, map_smul] at h1
        have h2 : (GlobalTheory.LatVac.psiAt B.ψ v (evFin F v (symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) γ (shiftA H H' l.1))) - 1) •
            ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l.1)) (G.M.vac v)) = 0 := by
          rw [sub_smul, one_smul, h1, sub_self]
        exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
      rw [h0, Set.indicator_of_notMem hl]
      simp
  simp_rw [key]
  rw [integral_mul_const]
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt X.ν w := by
    intro w hw
    rw [Chars.ν, div_eq_mul_inv]
    exact (hX.chars.unrα w fun h => hv (hw ▸ h)).mul (hX.chars.unrβ w fun h => hv (hw ▸ h)).inv
  have hpos : 0 < (b + 2 - a') / 2 := by have := hX.geo.eBig; omega
  have h𝔞 : idA σ H.𝔟 H'.𝔟 ≠ 0 := by
    obtain ⟨h𝔟0, -⟩ := GlobalTheory.PlaneIdeal.plane_ideal_trivial σ B H G.V G₁.V 0 (b + 1) _ _ hX.base hX.geo.hV hC.hH (by omega) (by omega)
    obtain ⟨h𝔠0, -⟩ := GlobalTheory.T.adapted_plane_skew_ideal_coprime_lt σ B H' G.W G₁.W 0 (b + 1) _ _ hX.base hX.geo.hW hC.hH' (by omega) (by omega)
    exact mul_ne_zero (mul_ne_zero h𝔟0 (inv_ne_zero (conjI_ne_zero σ h𝔠0))) (inv_ne_zero diffE_ne_zero)
  rw [GlobalTheory.T.local_unit_indicator_integral_value X.ν _ h𝔞 v hunr _ hpos μ hμ]
  rfl

end GlobalTheory.UnrLocA

end
