import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingRealStatement

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.BdryUnitVal
end GlobalTheory.BdryUnitVal
namespace GlobalTheory.BdryUnitVal
end GlobalTheory.BdryUnitVal
namespace GlobalTheory.BdryUnitVal
/- English proof (translation)
Introduce `_ E _ _ _ H Dw l Xo c Y Z V τ sig f hVZ hsig hvn hrd T io y₀ hio hlies`. Use `letI := io.toAlgebra`. Take `⟨φ, hφ⟩` from `exists_factor T io hio`. Establish `hy : ∀ s, GlobalTheory.AllWt.ptF y₀.1 s ∈ (V : Set (Xo.XF c))` using `fun s => hVZ ▸ hlies s`. Take `⟨χ, hχ1, hχ2, hχ3⟩` from `pt_ext E H Dw l Xo c Y V T io φ hφ y₀.1 hy`.

Establish `hp : Dw.mult τ.1 = Dw.p` using `by rw [Datum.mult, if_pos τ.2]`. Establish `hq : Dw.mult (conjEmb τ.1) = Dw.q` using `by rw [Datum.mult, if_neg (conj_ne τ)]`. Take `⟨v, hv, hsv⟩` from `GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 τ.1 Dw.p hp`. Take `⟨w, hw, hsw⟩` from `GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 (conjEmb τ.1) Dw.q hq`. Set `aT : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.V φ` to `⟨χ, hχ1, hχ3, v, w, hv, hw⟩`.

Establish `hx : (spMap (algebraMap T.V T.Fr) ≫ χ) ≫ pullback.fst _ _ = spMap (algebraMap T.V T.Fr) ≫ (χ ≫ pullback.fst _ _)` using `Category.assoc _ _ _`. Take `⟨v', hv', ev⟩` from `GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hv`. Take `⟨w', hw', ew⟩` from `GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hw`. Rewrite `hv'`, `hw'` using `[hφ]`. Set `aK : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.Fr io` to `⟨spMap (algebraMap T.V T.Fr) ≫ χ, by rw [Category.assoc, hχ1, ← GlobalTheory.DetExtendZero.spMap_comp, hφ], by`.

Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `hχ3 ⟨_, rfl⟩, v', w', hv', hw'⟩`. Establish `hc : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsChange aT aK (algebraMap T.V T.Fr) 1 1`. Use `⟨hφ, rfl, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.DetExtendZero.comb_one (fun k => (aK.v_basis.1 k).1) i` as an intermediate fact. Use `this using 2 with k` and compare the differences between its conclusion and the goal. Conclude with `(ev k).symm`. Use `GlobalTheory.DetExtendZero.comb_one (fun k => (aK.w_basis.1 k).1) i` as an intermediate fact. Use `this using 2 with k` and compare the differences between its conclusion and the goal.

Conclude with `(ew k).symm`. Establish `e` using `hsig T.V T.Fr φ io aT aK (algebraMap T.V T.Fr) 1 1 hc`. Simplify using `only [Matrix.det_one, mul_one] at e`. Establish `hm : Matches Y V τ y₀.1 aK` using `⟨hχ2.symm, fun i => ⟨Fin.cast hp.symm i, rfl, by`. Express the relevant statement in the definitionally equal form `SameVec Y y₀.1 _ (v' i).left`.

Rewrite using `[ev]; exact hsv i⟩, fun i => ⟨Fin.cast hq.symm i, rfl, by`. Express the relevant statement in the definitionally equal form `SameVec Y y₀.1 _ (w' i).left`. Rewrite using `[ew]`. Conclude with `hsw i⟩⟩`. Establish `hr` using `hrd T.Fr y₀.1 y₀.2.1 aK hm`.

Express the relevant statement in the definitionally equal form `nval T.V 1 (evR Xo c f y₀.1) = 0`. Rewrite using `[hr]`. Express the relevant statement in the definitionally equal form `nval T.V 1 (sig T.Fr io aK) = 0`. Rewrite using `[e]`. Conclude with `nval_unit T _ (hvn T.V φ aT)`.
-/
theorem boundary_unit_at_integral_points : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  intro _ E _ _ _ H Dw l Xo c Y Z V τ sig f hVZ hsig hvn hrd T io y₀ hio hlies
  letI := io.toAlgebra
  obtain ⟨φ, hφ⟩ := exists_factor T io hio
  have hy : ∀ s, GlobalTheory.AllWt.ptF y₀.1 s ∈ (V : Set (Xo.XF c)) := fun s => hVZ ▸ hlies s
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := pt_ext E H Dw l Xo c Y V T io φ hφ y₀.1 hy
  have hp : Dw.mult τ.1 = Dw.p := by rw [Datum.mult, if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by rw [Datum.mult, if_neg (conj_ne τ)]
  obtain ⟨v, hv, hsv⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 τ.1 Dw.p hp
  obtain ⟨w, hw, hsw⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 (conjEmb τ.1) Dw.q hq
  let aT : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.V φ := ⟨χ, hχ1, hχ3, v, w, hv, hw⟩
  have hx : (spMap (algebraMap T.V T.Fr) ≫ χ) ≫ pullback.fst _ _ =
      spMap (algebraMap T.V T.Fr) ≫ (χ ≫ pullback.fst _ _) := Category.assoc _ _ _
  obtain ⟨v', hv', ev⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hv
  obtain ⟨w', hw', ew⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hw
  rw [hφ] at hv' hw'
  let aK : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.Fr io :=
    ⟨spMap (algebraMap T.V T.Fr) ≫ χ, by rw [Category.assoc, hχ1, ← GlobalTheory.DetExtendZero.spMap_comp, hφ], by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hχ3 ⟨_, rfl⟩, v', w', hv', hw'⟩
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsChange aT aK (algebraMap T.V T.Fr) 1 1 := by
    refine ⟨hφ, rfl, fun i => ?_, fun i => ?_⟩
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.v_basis.1 k).1) i
      convert this using 2 with k
      exact (ev k).symm
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.w_basis.1 k).1) i
      convert this using 2 with k
      exact (ew k).symm
  have e := hsig T.V T.Fr φ io aT aK (algebraMap T.V T.Fr) 1 1 hc
  simp only [Matrix.det_one, mul_one] at e
  have hm : Matches Y V τ y₀.1 aK :=
    ⟨hχ2.symm, fun i => ⟨Fin.cast hp.symm i, rfl, by
      change SameVec Y y₀.1 _ (v' i).left
      rw [ev]; exact hsv i⟩, fun i => ⟨Fin.cast hq.symm i, rfl, by
      change SameVec Y y₀.1 _ (w' i).left
      rw [ew]; exact hsw i⟩⟩
  have hr := hrd T.Fr y₀.1 y₀.2.1 aK hm
  change nval T.V 1 (evR Xo c f y₀.1) = 0
  rw [hr]
  change nval T.V 1 (sig T.Fr io aK) = 0
  rw [e]
  exact nval_unit T _ (hvn T.V φ aT)
end GlobalTheory.BdryUnitVal
end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points | exact _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points | (intros; apply _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.boundary_unit_valuation_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  first | exact @_root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points | exact _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points | (intros; apply _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points <;> assumption)
end
