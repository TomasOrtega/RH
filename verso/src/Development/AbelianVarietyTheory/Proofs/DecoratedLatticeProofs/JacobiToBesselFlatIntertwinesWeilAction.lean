import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelValueAtZeroEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmIntegralComm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FlatComm

variable {D : D7}

/- English proof (translation)
Establish `h1 : mt B.V (embA B.d B.o h) ⬝ B.d.jX = B.d.jX` using `B.d.wittDecomp_anisotropicEmbedding_inclX _`. Establish `h2 : mt B.V (embA B.d B.o h) *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ)`. Establish `e1 : mt B.V (embA B.d B.o h) ⬝ B.d.j0 = B.d.j0 ⬝ mt B.V₀ (B.o.emb (h, 1))` using `B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _`. Establish `e2` using `B.o.emb_jB h 1`. Rewrite `e2` using `[mt_one, Matrix.mul_one]`.

Rewrite using `[vecB, ratV_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1, Matrix.mul_assoc]`. Conclude with `congrArg (fun M => (B.d.j0 ⬝ M) *ᵥ ratV B.ζ) e2`. Use function extensionality and compare the values at `k j`. Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations. Use `congrFun h2 k` as an intermediate fact.

Simplify using `only [x0, xLast, Matrix.mul_apply, Matrix.of_apply, Fin.snoc_last]`. Conclude with `this`. Use `congrFun (congrFun h1 k) i` as an intermediate fact. Simplify using `only [x0, xLast, Matrix.mul_apply, Matrix.of_apply, Fin.snoc_castSucc]`. Conclude with `this`.
-/
theorem besselAnisotropicEmbedding_fixes_basePoint {σ : ℕ} (B : BesLev D σ) (h : GA D B.A) : mt B.V (embA B.d B.o h) ⬝ x0 B = x0 B := by
  have h1 : mt B.V (embA B.d B.o h) ⬝ B.d.jX = B.d.jX := B.d.wittDecomp_anisotropicEmbedding_inclX _
  have h2 : mt B.V (embA B.d B.o h) *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) := by
    have e1 : mt B.V (embA B.d B.o h) ⬝ B.d.j0 = B.d.j0 ⬝ mt B.V₀ (B.o.emb (h, 1)) := B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _
    have e2 := B.o.emb_jB h 1
    rw [mt_one, Matrix.mul_one] at e2
    rw [vecB, ratV_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1, Matrix.mul_assoc]
    exact congrArg (fun M => (B.d.j0 ⬝ M) *ᵥ ratV B.ζ) e2
  funext k j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have := congrFun h2 k
    simp only [x0, xLast, Matrix.mul_apply, Matrix.of_apply, Fin.snoc_last]
    exact this
  · have := congrFun (congrFun h1 k) i
    simp only [x0, xLast, Matrix.mul_apply, Matrix.of_apply, Fin.snoc_castSucc]
    exact this

/- English proof (translation)
Establish `hv : Continuous (fun u : UX D ρ => u.1.1)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hs : Continuous fun u : UX D ρ => upSum u.1.1`. Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hv.matrix_elem i j`.

Conclude with `continuous_const`. Establish `ht : Continuous (Algebra.trace (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap _`. Conclude with `hψ.comp (ht.comp hs)`.
-/
theorem continuous_psiUni {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have hv : Continuous (fun u : UX D ρ => u.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hs : Continuous fun u : UX D ρ => upSum u.1.1 := by
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · exact hv.matrix_elem i j
    · exact continuous_const
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.comp (ht.comp hs)

/- English proof (translation)
Use `haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ`. Conclude with `instSFiniteOfSigmaFinite`.
-/
theorem sFinite_of_haar {G : Type} [MeasurableSpace G] [Group G] [TopologicalSpace G] (hl : LocallyCompactSpace G)
    (hs : SecondCountableTopology G) (μ : Measure G) (hμ : μ.IsHaarMeasure) : SFinite μ := by
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  exact instSFiniteOfSigmaFinite

set_option maxHeartbeats 600000 in

/- English proof (translation)
Introduce `D hD ψ σ J B s Ψ hΨ g h`. Take `⟨x, hx, hx0⟩` from `GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint D σ B`. Take `⟨k1, k2, k3⟩` from `GlobalTheory.UnitU.topology D (σ + 1)`. Use `haveI : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩`. Use `haveI : SFinite s.vU.ν := sFinite_of_haar k1 k2 _ s.vU.unit.1`.

Establish `hstd` using `s.weil.std`. Use `set p : GA D J.W × GA D B.V := (J.d.emb0 g, embA B.d B.o h) with hp`. Set `F : (WO J.W B.V → ℂ) → UX D (σ + 1) → WO J.W₀ B.V₀ → ℂ` to `fun Φ u w => flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (rat x) 0 Φ w u`. Establish `hF : ∀ Φ u, F Φ u = star (psiUni ψ u.1) • evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (x0 B ⬝ u.1.1) 0` using `fun Φ u => by`. Rewrite using `[← hx0]`.

Both sides reduce to the same expression. Establish `hflat : ∀ Φ, flatFB s Φ = fun w => ∫ u, F Φ u w ∂s.vU.ν` using `fun Φ => by`. Simplify using `only [F, hx0]`. Both sides reduce to the same expression. Establish `key : ∀ u, s.om₀ (g, B.o.emb (h, 1)) (F Ψ u) = F (s.om p Ψ) u` using `fun u => by`.

Establish `e` using `GlobalTheory.Unf.FB.evalAt_zero_equivariant D hD ψ σ J B s Ψ hΨ g 1 (one_mem _) h (x0 B ⬝ u.1.1)`. Rewrite `e` using `[one_mul, ← map_inv, ← Matrix.mul_assoc, besselAnisotropicEmbedding_fixes_basePoint]`. Rewrite using `[hF, hF, map_smul, ← e]`. Establish `hv : Continuous (fun u : UX D (σ + 1) => u.1.1)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hc : ∀ q, Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => F (s.om q Ψ) r.1 r.2` using `fun q => by`.

Establish `c` using `(GlobalTheory.MixCont.mixed_coords_continuous D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil Ψ hΨ).2`. Establish `c2 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => (q, (rat x : Mx D B.V.rank (σ + 1)) ⬝ r.1.1.1, (0 : Mx D J.W₀.rank σ), r.2)` using `continuous_const.prodMk ((continuous_const.matrix_mul (hv.comp continuous_fst)).prodMk (continuous_const.prodMk continuous_snd))`. Establish `c3` using `c.comp c2`. Establish `c4 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => star (psiUni ψ r.1.1)` using `((continuous_psiUni hstd.1.1 _).comp continuous_fst).star`. Establish `c5` using `c4.mul c3`.

Simplify using `only [Function.comp_def] at c5`. Conclude with `c5`. Establish `h1 : s.om 1 Ψ = Ψ` using `by rw [map_one]; rfl`. Take `⟨M, hM, hb⟩` from `GlobalTheory.Unf.flatFun_majorant D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil s.vU x hx.1 Ψ hΨ {1, p} (Set.toFinite _).isCompact`. Establish `hth : ∀ u, IsThetaFunO ψ J.W₀ B.V₀ (F Ψ u)` using `fun u => by`.

Take `⟨mS, mT⟩` from `GlobalTheory.MixValues.mixed_values D ψ hstd`. Rewrite using `[hF]`. Conclude with `GlobalTheory.OrientedHeis.theta_smul _ (mT _ _ _ _ B.d _ _ s.vT.covol _ (mS _ _ _ _ J.d _ _ s.vS.covol _ hΨ _) _)`. Establish `main` using `GlobalTheory.CommInt.om_integral_comm D ψ J.W₀ B.V₀ _ _ s.om₀ s.weil₀ (UX D (σ + 1)) s.vU.ν (F Ψ) (g, B.o.emb (h, 1)) M hth (by have := hc 1; rwa [h1] at this) (by simp only [key]; exact hc p) hM (fun u w => ⟨by have := hb 1 (by simp) 0 w u; rwa [h1] at this, by rw [key]; exact h …`. Rewrite using `[hflat, hflat]`.

Use function extensionality and compare the values at `w`. Rewrite using `[main w]`. Simplify using `only [key]`.
-/
theorem flatFB_om : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀) (h : GA D B.A), flatFB s (s.om (J.d.emb0 g, embA B.d B.o h) Ψ) = s.om₀ (g, B.o.emb (h, 1)) (flatFB s Ψ) := by
  intro D hD ψ σ J B s Ψ hΨ g h
  obtain ⟨x, hx, hx0⟩ := GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint D σ B
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D (σ + 1)
  haveI : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := sFinite_of_haar k1 k2 _ s.vU.unit.1
  have hstd := s.weil.std
  set p : GA D J.W × GA D B.V := (J.d.emb0 g, embA B.d B.o h) with hp
  let F : (WO J.W B.V → ℂ) → UX D (σ + 1) → WO J.W₀ B.V₀ → ℂ := fun Φ u w =>
    flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (rat x) 0 Φ w u
  have hF : ∀ Φ u, F Φ u = star (psiUni ψ u.1) •
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (x0 B ⬝ u.1.1) 0 := fun Φ u => by
    rw [← hx0]; rfl
  have hflat : ∀ Φ, flatFB s Φ = fun w => ∫ u, F Φ u w ∂s.vU.ν := fun Φ => by
    simp only [F, hx0]; rfl
  have key : ∀ u, s.om₀ (g, B.o.emb (h, 1)) (F Ψ u) = F (s.om p Ψ) u := fun u => by
    have e := GlobalTheory.Unf.FB.evalAt_zero_equivariant D hD ψ σ J B s Ψ hΨ g 1 (one_mem _) h (x0 B ⬝ u.1.1)
    rw [one_mul, ← map_inv, ← Matrix.mul_assoc, besselAnisotropicEmbedding_fixes_basePoint] at e
    rw [hF, hF, map_smul, ← e]
  have hv : Continuous (fun u : UX D (σ + 1) => u.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hc : ∀ q, Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => F (s.om q Ψ) r.1 r.2 := fun q => by
    have c := (GlobalTheory.MixCont.mixed_coords_continuous D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil Ψ hΨ).2
    have c2 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ =>
        (q, (rat x : Mx D B.V.rank (σ + 1)) ⬝ r.1.1.1, (0 : Mx D J.W₀.rank σ), r.2) :=
      continuous_const.prodMk ((continuous_const.matrix_mul (hv.comp continuous_fst)).prodMk
        (continuous_const.prodMk continuous_snd))
    have c3 := c.comp c2
    have c4 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => star (psiUni ψ r.1.1) :=
      ((continuous_psiUni hstd.1.1 _).comp continuous_fst).star
    have c5 := c4.mul c3
    simp only [Function.comp_def] at c5
    exact c5
  have h1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  obtain ⟨M, hM, hb⟩ := GlobalTheory.Unf.flatFun_majorant D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil s.vU x hx.1 Ψ hΨ
    {1, p} (Set.toFinite _).isCompact
  have hth : ∀ u, IsThetaFunO ψ J.W₀ B.V₀ (F Ψ u) := fun u => by
    obtain ⟨mS, mT⟩ := GlobalTheory.MixValues.mixed_values D ψ hstd
    rw [hF]
    exact GlobalTheory.OrientedHeis.theta_smul _ (mT _ _ _ _ B.d _ _ s.vT.covol _ (mS _ _ _ _ J.d _ _ s.vS.covol _ hΨ _) _)
  have main := GlobalTheory.CommInt.om_integral_comm D ψ J.W₀ B.V₀ _ _ s.om₀ s.weil₀ (UX D (σ + 1)) s.vU.ν (F Ψ) (g, B.o.emb (h, 1)) M hth
    (by have := hc 1; rwa [h1] at this) (by simp only [key]; exact hc p) hM
    (fun u w => ⟨by have := hb 1 (by simp) 0 w u; rwa [h1] at this, by rw [key]; exact hb p (by simp) 0 w u⟩)
    (GlobalTheory.Unf.Flat.flatLaw D ψ hstd J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT s.vU x hx.1 0 Ψ hΨ).2
  rw [hflat, hflat]
  funext w
  rw [main w]
  simp only [key]

end GlobalTheory.Unf.FlatComm

end
