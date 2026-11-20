import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPtStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatioStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartHolomorphicCoordinatesNearFrameStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrixStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactorStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFramesStatement

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FrameUnif.NormUnHol

/- English proof (translation)
Repeatedly rewrite using `[Matrix.det_apply']`. Use `DifferentiableOn.fun_sum fun π _ => ?_` and prove the remaining obligations. Establish `key : DifferentiableOn ℂ (∏ i, fun b => h b (π i) i) s` using `Finset.prod_induction _ (fun f => DifferentiableOn ℂ f s) (fun _ _ ha hb => ha.mul hb) (differentiableOn_const (1 : ℂ)) (fun i _ => hh _ _)`. Establish `e : (∏ i, fun b => h b (π i) i) = fun b => ∏ i, h b (π i) i`. Use function extensionality and compare the values at `b`.

Simplify using `[Finset.prod_apply]`. Conclude with `(differentiableOn_const _).mul (e ▸ key)`.
-/
theorem differentiableOn_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ} {s : Set V}
    {h : V → Matrix (Fin g) (Fin g) ℂ} (hh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) s) :
    DifferentiableOn ℂ (fun b => (h b).det) s := by
  simp_rw [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun π _ => ?_
  have key : DifferentiableOn ℂ (∏ i, fun b => h b (π i) i) s :=
    Finset.prod_induction _ (fun f => DifferentiableOn ℂ f s) (fun _ _ ha hb => ha.mul hb)
      (differentiableOn_const (1 : ℂ)) (fun i _ => hh _ _)
  have e : (∏ i, fun b => h b (π i) i) = fun b => ∏ i, h b (π i) i := by
    funext b; simp [Finset.prod_apply]
  exact (differentiableOn_const _).mul (e ▸ key)

/- English proof (translation)
Establish `hpos : ∀ j, 0 < 2 * ‖ty j ξ‖` using `fun j => by`. Establish `: ty j ξ ≠ 0` using `(map_ne_zero (ty j)).mpr hξ`. Check the signs of the components of the expression. Conclude with `(Real.sqrt_pos.mpr (div_pos (by positivity) (Finset.prod_pos fun j _ => hpos j))).ne'`.
-/
theorem normConst_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ : E} (hξ : ξ ≠ 0) :
    Real.sqrt (2 ^ g / ∏ j, (2 * ‖ty j ξ‖)) ≠ 0 := by
  have hpos : ∀ j, 0 < 2 * ‖ty j ξ‖ := fun j => by
    have : ty j ξ ≠ 0 := (map_ne_zero (ty j)).mpr hξ
    positivity
  exact (Real.sqrt_pos.mpr (div_pos (by positivity) (Finset.prod_pos fun j _ => hpos j))).ne'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

/- English proof (translation)
Unfold `wchar ex`. Simplify using `[Fintype.prod_option]`.
-/
theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : Sˣ) :
    wchar (ex Dw a n) (fun i => Option.elim i t₀ (fun _ => 1)) = (t₀ : S) ^ n := by
  unfold wchar ex
  simp [Fintype.prod_option]

/- English proof (translation)
Introduce `b₀ hb₀`. Take `⟨p, y₀, B, ψ, hBo, hb₀B, hBd, hψu, hψd⟩` from `GlobalTheory.T.exists_chart_holomorphic_coordinates_near_frame hbc E H Dw l Xo c σ g e F r M k T b₀ hb₀`. Use `choose z hz using fun b => GlobalTheory.Frames.FramedBaseChange.exists_frMap hbc E H Dw l Xo c p.R (CAt σ) (ψ b) y₀`. Establish `hx : ∀ b ∈ B, (y b).x = (z b).x`. Introduce `b hb`.

Rewrite using `[(hy b (hBd hb)).1, hψu b hb]`. Conclude with `((hz b).1).symm`. Establish `hch : ∀ b, ∃ (gch : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sch : CAt σ), b ∈ B → FrChg gch sch (z b) (y b)`. Introduce `b`. Distinguish the cases in `hb : b ∈ B`.

Take `⟨gch, u, -, hc⟩` from `(GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) (z b) (y b)).1 (hx b hb)`. Conclude with `⟨gch, u, fun _ => hc⟩`. Conclude with `⟨fun _ => 0, 0, fun h => absurd h hb⟩`. Use `choose gch sch hgs using hch`. Establish `hall : ∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (gch b) (sch b) (z b) (y b) ∧ IsThetaPt T b 1 (y b)` using `fun b hb => ⟨hz b, hgs b hb, hy b (hBd hb)⟩`.

Establish `hG` using `GlobalTheory.T.differentiableOn_exponential_frame_matrix E H Dw l Xo c σ g e F r M k T p.R y₀ B ψ (fun _ => 1) z y gch sch hBo hBd hψd hall`. Establish `hS` using `GlobalTheory.T.differentiableOn_theta_algebraic_generator_factor htw E H Dw l Xo c σ g e F r M k T p.R y₀ B ψ (fun _ => 1) z y gch sch hBo hBd hψd hall (differentiableOn_const 1)`. Establish `hB` using `GlobalTheory.T.differentiableOn_natural_rule_holomorphic_frames hbc E H Dw l Xo c σ (Fin T.m → ℂ) B p y₀ ψ z y gch sch (fun b hb => ⟨hz b, hgs b hb⟩) hψd hG hS a n f hf`. Conclude with `(hB.differentiableAt (hBo.mem_nhds hb₀B)).differentiableWithinAt`.
-/
theorem differentiableOn_thetaPt (hbc : Out.SecBaseChangeSt) (htw : Out.SecTwistSt) {g : ℕ}
    {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {r : ℕ} {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k)
    (y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (hy : ∀ b ∈ T.co ⁻¹' (M.X k).dom, IsThetaPt T b 1 (y b))
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (hf : f ∈ sec Xo c a n) :
    DifferentiableOn ℂ (fun b => toC (evR Xo c f (y b))) (T.co ⁻¹' (M.X k).dom) := by
  intro b₀ hb₀
  obtain ⟨p, y₀, B, ψ, hBo, hb₀B, hBd, hψu, hψd⟩ :=
    GlobalTheory.T.exists_chart_holomorphic_coordinates_near_frame hbc E H Dw l Xo c σ g e F r M k T b₀ hb₀
  choose z hz using fun b =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hbc E H Dw l Xo c p.R (CAt σ) (ψ b) y₀
  have hx : ∀ b ∈ B, (y b).x = (z b).x := by
    intro b hb
    rw [(hy b (hBd hb)).1, hψu b hb]
    exact ((hz b).1).symm
  have hch : ∀ b, ∃ (gch : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))
      (sch : CAt σ), b ∈ B → FrChg gch sch (z b) (y b) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨gch, u, -, hc⟩ :=
        (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) (z b) (y b)).1 (hx b hb)
      exact ⟨gch, u, fun _ => hc⟩
    · exact ⟨fun _ => 0, 0, fun h => absurd h hb⟩
  choose gch sch hgs using hch
  have hall : ∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (gch b) (sch b) (z b) (y b) ∧
      IsThetaPt T b 1 (y b) := fun b hb => ⟨hz b, hgs b hb, hy b (hBd hb)⟩
  have hG := GlobalTheory.T.differentiableOn_exponential_frame_matrix E H Dw l Xo c σ g e F r M k T p.R y₀ B ψ (fun _ => 1) z y gch sch
    hBo hBd hψd hall
  have hS := GlobalTheory.T.differentiableOn_theta_algebraic_generator_factor htw E H Dw l Xo c σ g e F r M k T p.R y₀ B ψ (fun _ => 1) z y gch sch
    hBo hBd hψd hall (differentiableOn_const 1)
  have hB := GlobalTheory.T.differentiableOn_natural_rule_holomorphic_frames hbc E H Dw l Xo c σ (Fin T.m → ℂ) B p y₀ ψ z y gch sch
    (fun b hb => ⟨hz b, hgs b hb⟩) hψd hG hS a n f hf
  exact (hB.differentiableAt (hBo.mem_nhds hb₀B)).differentiableWithinAt

/- English proof (translation)
Introduce `hbc htw E _ _ _ H Dw l Xo c σ g e F r M un k T hT a n hD f hf`. Take `⟨m, hm⟩` from `hD.2`. Break down `Set.eq_empty_or_nonempty (M.X k).dom with h0 | ⟨x₀, hx₀⟩` into its components or cases. Rewrite using `[h0]`. Conclude with `differentiableOn_empty`.

Establish `hx₀' : T.co.symm x₀ ∈ T.co ⁻¹' (M.X k).dom` using `by simpa using hx₀`. Take `⟨y₀, -⟩` from `GlobalTheory.T.exists_isThetaPt' htw E H Dw l Xo c σ g e F r M k T _ hx₀' 1 one_ne_zero`. Establish `hy1 : ∀ b, ∃ y : FrPt Xo c (CAt σ), b ∈ T.co ⁻¹' (M.X k).dom → IsThetaPt T b 1 y`. Introduce `b`. Distinguish the cases in `hb : b ∈ T.co ⁻¹' (M.X k).dom`.

Take `⟨y, hy⟩` from `GlobalTheory.T.exists_isThetaPt' htw E H Dw l Xo c σ g e F r M k T b hb 1 one_ne_zero`. Conclude with `⟨y, fun _ => hy⟩`. Conclude with `⟨y₀, fun h => absurd h hb⟩`. Use `choose y hy using hy1`. Establish `hth` using `differentiableOn_thetaPt hbc htw T y hy a n f hf`.

Establish `key : ∀ x (hx : x ∈ (M.X k).dom), toC (evR Xo c f (un k ⟨x, hx⟩)) = ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x)).det) ^ m * toC (evR Xo c f (y (T.co.symm x)))`. Introduce `x hx`. Establish `hb : T.co.symm x ∈ T.co ⁻¹' (M.X k).dom` using `by simpa using hx`. Take `⟨κ, hκ2, hθ⟩` from `hT ⟨x, hx⟩`. Establish `hN : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (normConst_ne_zero _ (M.X k).ξ0_ne)`.

Establish `hdet : (T.h (T.co.symm x)).det ≠ 0` using `(T.norm _ hb).1.ne_zero`. Establish `hκ : κ ≠ 0`. Introduce `h0`. Apply `mul_ne_zero hN hdet` to reduce the goal to its premises. Rewrite using `[← hκ2, h0]`.

Expand and normalize the polynomial expressions, which then agree. Set `t₀ : (CAt σ)ˣ` to `⟨(κ : ℂ), (κ⁻¹ : ℂ), mul_inv_cancel₀ hκ, inv_mul_cancel₀ hκ⟩`. Establish `hθ' : IsThetaPt T (T.co.symm x) (toC (t₀ : CAt σ) * 1) (un k ⟨x, hx⟩)`. Establish `h1 : toC (t₀ : CAt σ) * 1 = κ` using `by show κ * 1 = κ`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Conclude with `hθ`. Establish `hbor` using `GlobalTheory.T.thetaPoints_frame_ratio htw E H Dw l Xo c σ g e F r M k T (T.co.symm x) hb 1 t₀ _ _ (hy _ hb) hθ'`. Establish `hred : IsReduced (CAt σ)` using `by show IsReduced ℂ infer_instance`. Establish `hev` using `(GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hbc E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred a n f hf _ _ _ hbor`.

Rewrite using `[hev, wchar_gen]`. Establish `e1 : toC ((t₀ : CAt σ) ^ n * evR Xo c f (y (T.co.symm x))) = κ ^ n * toC (evR Xo c f (y (T.co.symm x)))` using `rfl`. Rewrite using `[e1, hm, ← two_mul, pow_mul, hκ2]`. Establish `hΦ : DifferentiableOn ℂ (fun b => ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h b).det) ^ m * toC (evR Xo c f (y b))) (T.co ⁻¹' (M.X k).dom)` using `(((differentiableOn_const _).mul (differentiableOn_det fun i j => (T.hol i j).1)).pow m).mul hth`. Establish `hcomp` using `hΦ.comp T.co.symm.differentiableOn (fun x hx => by simpa using hx)`.

Use `hcomp.congr fun x hx => ?_` and prove the remaining obligations. Unfold `rdU unfOf`. Simplify using `only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]`. Conclude with `key x hx`.
-/
theorem differentiableOn_rdU : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), IsNormUn T (un k) → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, DifferentiableOn ℂ (rdU (unfOf e F M un) f k) (M.X k).dom := by
  intro hbc htw E _ _ _ H Dw l Xo c σ g e F r M un k T hT a n hD f hf
  obtain ⟨m, hm⟩ := hD.2
  rcases Set.eq_empty_or_nonempty (M.X k).dom with h0 | ⟨x₀, hx₀⟩
  · rw [h0]
    exact differentiableOn_empty
  have hx₀' : T.co.symm x₀ ∈ T.co ⁻¹' (M.X k).dom := by simpa using hx₀
  obtain ⟨y₀, -⟩ := GlobalTheory.T.exists_isThetaPt' htw E H Dw l Xo c σ g e F r M k T _ hx₀' 1 one_ne_zero
  have hy1 : ∀ b, ∃ y : FrPt Xo c (CAt σ), b ∈ T.co ⁻¹' (M.X k).dom → IsThetaPt T b 1 y := by
    intro b
    by_cases hb : b ∈ T.co ⁻¹' (M.X k).dom
    · obtain ⟨y, hy⟩ := GlobalTheory.T.exists_isThetaPt' htw E H Dw l Xo c σ g e F r M k T b hb 1 one_ne_zero
      exact ⟨y, fun _ => hy⟩
    · exact ⟨y₀, fun h => absurd h hb⟩
  choose y hy using hy1
  have hth := differentiableOn_thetaPt hbc htw T y hy a n f hf
  have key : ∀ x (hx : x ∈ (M.X k).dom),
      toC (evR Xo c f (un k ⟨x, hx⟩)) =
        ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x)).det) ^ m *
          toC (evR Xo c f (y (T.co.symm x))) := by
    intro x hx
    have hb : T.co.symm x ∈ T.co ⁻¹' (M.X k).dom := by simpa using hx
    obtain ⟨κ, hκ2, hθ⟩ := hT ⟨x, hx⟩
    have hN : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (normConst_ne_zero _ (M.X k).ξ0_ne)
    have hdet : (T.h (T.co.symm x)).det ≠ 0 := (T.norm _ hb).1.ne_zero
    have hκ : κ ≠ 0 := by
      intro h0
      apply mul_ne_zero hN hdet
      rw [← hκ2, h0]
      ring
    let t₀ : (CAt σ)ˣ := ⟨(κ : ℂ), (κ⁻¹ : ℂ), mul_inv_cancel₀ hκ, inv_mul_cancel₀ hκ⟩
    have hθ' : IsThetaPt T (T.co.symm x) (toC (t₀ : CAt σ) * 1) (un k ⟨x, hx⟩) := by
      have h1 : toC (t₀ : CAt σ) * 1 = κ := by
        show κ * 1 = κ
        ring
      rw [h1]
      exact hθ
    have hbor := GlobalTheory.T.thetaPoints_frame_ratio htw E H Dw l Xo c σ g e F r M k T (T.co.symm x) hb 1 t₀ _ _
      (hy _ hb) hθ'
    have hred : IsReduced (CAt σ) := by
      show IsReduced ℂ
      infer_instance
    have hev := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hbc E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred a n f hf _ _ _ hbor
    rw [hev, wchar_gen]
    have e1 : toC ((t₀ : CAt σ) ^ n * evR Xo c f (y (T.co.symm x))) =
        κ ^ n * toC (evR Xo c f (y (T.co.symm x))) := rfl
    rw [e1, hm, ← two_mul, pow_mul, hκ2]
  have hΦ : DifferentiableOn ℂ (fun b => ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) *
      (T.h b).det) ^ m * toC (evR Xo c f (y b))) (T.co ⁻¹' (M.X k).dom) :=
    (((differentiableOn_const _).mul (differentiableOn_det fun i j => (T.hol i j).1)).pow m).mul hth
  have hcomp := hΦ.comp T.co.symm.differentiableOn (fun x hx => by simpa using hx)
  refine hcomp.congr fun x hx => ?_
  unfold rdU unfOf
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
  exact key x hx

end GlobalTheory.FrameUnif.NormUnHol
