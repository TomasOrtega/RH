import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionIntegralFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BoundaryUnitAtEqualCharacteristicPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionIntegralFrameStatement

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
namespace GlobalTheory.FlatCore.Bdry
/- English proof (translation)
Introduce `hP hQ2 E _ _ _ H Dw l Xo c r U x hL Z τ s T io y₀ hv hZ`. Take `⟨s₀, hs₀⟩` from `_root_.GlobalTheory.T.boundary_isUnit_at_eqChar_points hP hQ2 E H Dw l Xo c r U x hL Z τ ⟨s⟩`. Take `⟨a, ha, hsa⟩` from `GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight E H Dw l Xo c r U x hL.unf hL.geo Z (flatWt Dw τ) s₀ s`. Establish `h0 : io a ≠ 0` using `(map_ne_zero io).2 ha`. Rewrite using `[hsa, evI_smul, nval_mul, hs₀ T io y₀ hv hZ, nval_of_ne h0, hv a ha]`.

Simplify using the standard rewrite rules.
-/
theorem nval_evI_eq_zero_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  intro hP hQ2 E _ _ _ H Dw l Xo c r U x hL Z τ s T io y₀ hv hZ
  obtain ⟨s₀, hs₀⟩ := _root_.GlobalTheory.T.boundary_isUnit_at_eqChar_points hP hQ2 E H Dw l Xo c r U x hL Z τ ⟨s⟩
  obtain ⟨a, ha, hsa⟩ := GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight E H Dw l Xo c r U x hL.unf hL.geo Z (flatWt Dw τ) s₀ s
  have h0 : io a ≠ 0 := (map_ne_zero io).2 ha
  rw [hsa, evI_smul, nval_mul, hs₀ T io y₀ hv hZ, nval_of_ne h0, hv a ha]
  simp
end GlobalTheory.FlatCore.Bdry
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | exact _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | (intros; apply _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.archimedean_section_integral_frame_of_laws : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  first | exact @_root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | exact _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | (intros; apply _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt <;> assumption)
end
