import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopePhiGroupExtensionDvr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopePhiGroupExtensionDvrStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PeriodMinPos
/- English proof (translation)
Introduce `_ E _ _ _ H Dw l Xo c T io y φ hφ G t' m1 m2 hG`. Take `⟨G₀, t₀, m1₀, m2₀, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩` from `hφ`. Take `⟨m⟩` from `GlobalTheory.SlopeRec.nonempty_sabMap_of_models m1 m2 m1₀ m2₀`. Establish `hG₀ : (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G₀.G` using `fun h => hG ((abLocus_pullback abLocusOne G.semi m.cart.1 _).2 h)`. Establish `hnt : ¬ Subsingleton P.D.toPre.X` using `fun h => hG₀ ((GlobalTheory.TorRef.closed_mem_abLocus_iff T P).2 h)`.

Rewrite `hnt` using `[not_subsingleton_iff_nontrivial]`. Take `⟨a, ha⟩` from `exists_ne (0 : P.D.toPre.X)`. Establish `hQa : 1 ≤ Q a` using `ReciprocityTheory.ChartRestriction.G.DVR.QForm.Q_pos hϖ P.D hQ ha`. Establish `hint : ∀ a c, ∃ z : ℤ, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a c = z`. Introduce `a c`.

Use `⟨Q (a + c) - Q a - Q c, ?_⟩` and prove the remaining obligations. Establish `h1` using `hβ (a + c)`. Establish `hs` using `β.2.1 c a`. Simplify using `only [map_add, LinearMap.add_apply] at h1`. Rewrite `h1` using `[hβ a, hβ c]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos : ∀ a, 0 ≤ (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a` using `fun a => by`. Rewrite using `[hβ]; exact mul_nonneg zero_le_two (by exact_mod_cast h0 a)`. Establish `hne : β ≠ 0` using `fun e => by`.

Establish `h1` using `hβ a`. Rewrite `h1` using `[e]`. Establish `: (1 : ℝ) ≤ Q a` using `by exact_mod_cast hQa`. Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `haveI : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _`. Use `haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X`. Establish `h1` using `GlobalTheory.LeastExponentProbe.one_le_phiC (fun _ => rfl) β hint hpos hne`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem period_minimum_phi_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  intro _ E _ _ _ H Dw l Xo c T io y φ hφ G t' m1 m2 hG
  obtain ⟨G₀, t₀, m1₀, m2₀, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩ := hφ
  obtain ⟨m⟩ := GlobalTheory.SlopeRec.nonempty_sabMap_of_models m1 m2 m1₀ m2₀
  have hG₀ : (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G₀.G := fun h =>
    hG ((abLocus_pullback abLocusOne G.semi m.cart.1 _).2 h)
  have hnt : ¬ Subsingleton P.D.toPre.X := fun h =>
    hG₀ ((GlobalTheory.TorRef.closed_mem_abLocus_iff T P).2 h)
  rw [not_subsingleton_iff_nontrivial] at hnt
  obtain ⟨a, ha⟩ := exists_ne (0 : P.D.toPre.X)
  have hQa : 1 ≤ Q a := ReciprocityTheory.ChartRestriction.G.DVR.QForm.Q_pos hϖ P.D hQ ha
  have hint : ∀ a c, ∃ z : ℤ, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a c = z := by
    intro a c
    refine ⟨Q (a + c) - Q a - Q c, ?_⟩
    have h1 := hβ (a + c)
    have hs := β.2.1 c a
    simp only [map_add, LinearMap.add_apply] at h1
    rw [hβ a, hβ c] at h1
    push_cast
    linarith
  have hpos : ∀ a, 0 ≤ (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβ]; exact mul_nonneg zero_le_two (by exact_mod_cast h0 a)
  have hne : β ≠ 0 := fun e => by
    have h1 := hβ a
    rw [e] at h1
    have : (1 : ℝ) ≤ Q a := by exact_mod_cast hQa
    simp at h1
    linarith
  haveI : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have h1 := GlobalTheory.LeastExponentProbe.one_le_phiC (fun _ => rfl) β hint hpos hne
  linarith
end GlobalTheory.PeriodMinPos
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | exact _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | (intros; apply _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.minimal_period_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  first | exact @_root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | exact _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | (intros; apply _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos <;> assumption)
end
