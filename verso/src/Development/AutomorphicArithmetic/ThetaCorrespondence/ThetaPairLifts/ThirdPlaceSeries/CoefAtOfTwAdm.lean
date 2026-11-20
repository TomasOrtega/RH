import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjCoefAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open GlobalTheory.ConjTwist
set_option maxHeartbeats 4000000 in
/- English proof (translation)
Introduce `hA`. Use `_root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt) fun Fm x hx i p hr hm w _ j H => ?_` and prove the remaining obligations. Take `⟨⟨-, -, hin⟩, hlow⟩` from `H`. Establish `hR` using `_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hr hm _ hin hlow j`. Introduce `ρ ν hρ hp hN`.

Take `⟨hν0, c₀, hsc, n, hn, hνn⟩` from `hN`. Take `⟨-, -, -, -, u, hu, -⟩` from `id hsc`. Take `⟨c, hc⟩` from `GlobalTheory.ExtCoeff.exists_extC _ _ _ _ _ _ _ j Unit (fun _ => p.P.A3.A.μ0) (p.O j)`. Establish `hB` using `hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)`. Establish `hBo` using `baseOf_of_realPin hR.core.lev hρ hp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)`.

Establish `H1` using `GlobalTheory.CoefLatConj.coefLat_conj (Fm.D x i) _ _ _ p.P.A3.A p.T p.R.toRealDat (F2 p) p.κ p.v₀ p.O hR.core hR.fw hR.io j hR.pins c hc u hu _ hB hBo`. Take `⟨κ, hκ0, hκ, H2⟩` from `H1`. Establish `hspan` using `(H2.2 _ (Formalism.L2.Host.embLL0 _) (labLL0 _) (smallInt _) (smallInt_isCoefRing _)).1`. Establish `hO : OMPins p.T p.R.toRealDat p.κ p.v₀ p.O j` using `hR.pins`. Establish `hfield` using `hO.2.lift.field`.

Establish `hc0` using `hO.2.lift.c0`. Take `⟨gramR, c0R, c0L, hft, hbc⟩` from `hc0`. Establish `hcL : ∀ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j), c (GlobalTheory.CoefModel.mapVV (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) F) = c0L j F` using `fun F => by`. Take `⟨v', hv', hv0⟩` from `hbc F`. Use `(hc v' _ ?_).trans hv0` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `MvPolynomial.map (Fm.D x i).what₂.embLL _ = _`. Rewrite using `[hv', MvPolynomial.map_map, hfield]`. Establish `hκs : IsScale p.R p.v₀ (baseW (Fm.ex x hx i) w j ρ) κ` using `⟨gramR, c0R, c0L, hft, u, hu, fun F => (congrArg (fun z => harmFn _ _ _ (p.R.ioP j (PiTensorProduct.tprod ℂ u) z)) (hcL F)).symm.trans ((hκ _).trans (congrArg (κ • ·) (coefFn_map_eq _ _ _)))⟩`. Take `⟨k, hk, hkk⟩` from `scale_pow_eq_of_isScale p.R p.v₀ _ hsc hκs`. Establish `hφc : phs p j * c₀ ≠ 0` using `fun h0 => hν0 ((pow_eq_zero_iff hn).1 (hνn.trans (by rw [h0, zero_pow hn])))`.

Establish `hφ : phs p j ≠ 0` using `left_ne_zero_of_mul hφc`. Use `⟨c, u, ν / (phs p j * κ), hc, hu, ⟨n * k, Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hk), ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : ν ^ (n * k) = (phs p j * κ) ^ (n * k)`. Rewrite using `[pow_mul, hνn, ← pow_mul, mul_pow, mul_pow, mul_comm n k, pow_mul c₀, pow_mul κ, hkk]`. Rewrite using `[div_pow, e, div_self (pow_ne_zero _ (mul_ne_zero hφ hκ0))]`.

Introduce `h₀ P hP`. Take `⟨y, hPy, hy⟩` from `exists_fixed_of_mem_span j (p.R.ioP j (PiTensorProduct.tprod ℂ u)) c κ⁻¹ _ ((hspan (finPt _ h₀)).le hP)`. Use `⟨y, ?_, hy⟩` and prove the remaining obligations. Establish `e : ν * κ⁻¹ = ν / (phs p j * κ) * phs p j` using `by field_simp`. Conclude with `(congrArg (ν • ·) hPy).trans ((smul_smul ν κ⁻¹ _).trans (congrArg (· • _) e))`.
-/
theorem coefAt_of_twAdm_alt : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.CoefficientCondition := by
  intro hA
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨-, -, hin⟩, hlow⟩ := H
  have hR := _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hr hm _ hin hlow j
  intro ρ ν hρ hp hN
  obtain ⟨hν0, c₀, hsc, n, hn, hνn⟩ := hN
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hsc
  obtain ⟨c, hc⟩ := GlobalTheory.ExtCoeff.exists_extC _ _ _ _ _ _ _ j Unit (fun _ => p.P.A3.A.μ0) (p.O j)
  have hB := hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hBo := baseOf_of_realPin hR.core.lev hρ hp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have H1 := GlobalTheory.CoefLatConj.coefLat_conj (Fm.D x i) _ _ _ p.P.A3.A p.T p.R.toRealDat (F2 p) p.κ p.v₀ p.O hR.core hR.fw hR.io j
    hR.pins c hc u hu _ hB hBo
  obtain ⟨κ, hκ0, hκ, H2⟩ := H1
  have hspan := (H2.2 _ (Formalism.L2.Host.embLL0 _) (labLL0 _) (smallInt _) (smallInt_isCoefRing _)).1
  have hO : OMPins p.T p.R.toRealDat p.κ p.v₀ p.O j := hR.pins
  have hfield := hO.2.lift.field
  have hc0 := hO.2.lift.c0
  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hc0
  have hcL : ∀ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j),
      c (GlobalTheory.CoefModel.mapVV (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) F) = c0L j F := fun F => by
    obtain ⟨v', hv', hv0⟩ := hbc F
    refine (hc v' _ ?_).trans hv0
    change MvPolynomial.map (Fm.D x i).what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]
  have hκs : IsScale p.R p.v₀ (baseW (Fm.ex x hx i) w j ρ) κ := ⟨gramR, c0R, c0L, hft, u, hu, fun F =>
    (congrArg (fun z => harmFn _ _ _ (p.R.ioP j (PiTensorProduct.tprod ℂ u) z)) (hcL F)).symm.trans
      ((hκ _).trans (congrArg (κ • ·) (coefFn_map_eq _ _ _)))⟩
  obtain ⟨k, hk, hkk⟩ := scale_pow_eq_of_isScale p.R p.v₀ _ hsc hκs
  have hφc : phs p j * c₀ ≠ 0 := fun h0 => hν0 ((pow_eq_zero_iff hn).1 (hνn.trans (by rw [h0, zero_pow hn])))
  have hφ : phs p j ≠ 0 := left_ne_zero_of_mul hφc
  refine ⟨c, u, ν / (phs p j * κ), hc, hu, ⟨n * k, Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hk), ?_⟩, ?_⟩
  · have e : ν ^ (n * k) = (phs p j * κ) ^ (n * k) := by
      rw [pow_mul, hνn, ← pow_mul, mul_pow, mul_pow, mul_comm n k, pow_mul c₀, pow_mul κ, hkk]
    rw [div_pow, e, div_self (pow_ne_zero _ (mul_ne_zero hφ hκ0))]
  · intro h₀ P hP
    obtain ⟨y, hPy, hy⟩ := exists_fixed_of_mem_span j (p.R.ioP j (PiTensorProduct.tprod ℂ u)) c κ⁻¹ _
      ((hspan (finPt _ h₀)).le hP)
    refine ⟨y, ?_, hy⟩
    have e : ν * κ⁻¹ = ν / (phs p j * κ) * phs p j := by field_simp
    exact (congrArg (ν • ·) hPy).trans ((smul_smul ν κ⁻¹ _).trans (congrArg (· • _) e))
end GlobalTheory.BigOn.Exp.TwConj
end
end
