import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical
open GlobalTheory.CxPts GlobalTheory.Cartier.CartierDiv
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatChain

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ σ' : k →+* ℂ}

omit [IsIntegral X] in

/- English proof (translation)
Introduce `h` and use `h <| by refine (isUnit_map_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of ℂ) y.1).hom _).1 ?_ rw [map_natCast] exact (Nat.cast_ne_zero.2 hp : (p : ℂ) ≠ 0).isUnit`.
-/
theorem not_ov_under {p : ℕ} (hp : p ≠ 0) (y : CxPts q σ) : ¬ Ov p (under y) := fun h => h <| by
  refine (isUnit_map_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of ℂ) y.1).hom _).1 ?_
  rw [map_natCast]
  exact (Nat.cast_ne_zero.2 hp : (p : ℂ) ≠ 0).isUnit

/- English proof (translation)
Establish `h0` using `ratVal_ne_zero hf`. Take `⟨U, hU, a, rfl⟩` from `hf.regAt.exists_fnOf`. Establish `hy : y ∈ ptsIn q σ U` using `mem_ptsIn.2 hU`. Rewrite `h0` using `[ratVal_fnOf hy]`. Establish `hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2` using `(contDiff_apply ℝ ℂ ()).norm_sq ℂ`.

Use `⟨U, Unit, inferInstance, fun _ => a, fun v => Real.log (‖v ()‖ ^ 2), {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const, pow_ne_zero _ (norm_ne_zero_iff.2 h0), hs.contDiffOn.log fun _ h => h, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(isOpen_ptsIn (p := q) (σ := σ) U).mem_nhds hy] with z hz`. Rewrite using `[ratVal_fnOf hz]`.
-/
theorem cInfAt_log_ratVal {f : X.functionField} {y : CxPts q σ} (hf : UnitAt (under y) f) :
    CInfAt (fun z : CxPts q σ => Real.log (‖ratVal f z‖ ^ 2)) y := by
  have h0 := ratVal_ne_zero hf
  obtain ⟨U, hU, a, rfl⟩ := hf.regAt.exists_fnOf
  have hy : y ∈ ptsIn q σ U := mem_ptsIn.2 hU
  rw [ratVal_fnOf hy] at h0
  have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ ℂ ()).norm_sq ℂ
  refine ⟨U, Unit, inferInstance, fun _ => a, fun v => Real.log (‖v ()‖ ^ 2),
    {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const,
    pow_ne_zero _ (norm_ne_zero_iff.2 h0), hs.contDiffOn.log fun _ h => h, ?_⟩
  filter_upwards [(isOpen_ptsIn (p := q) (σ := σ) U).mem_nhds hy] with z hz
  rw [ratVal_fnOf hz]

/- English proof (translation)
Take `⟨U, hU, a, rfl⟩` from `hf.exists_fnOf`. Establish `hy : y ∈ ptsIn q σ U` using `mem_ptsIn.2 hU`. Establish `hy' : y' ∈ ptsIn q σ' U`. Express the relevant statement in the definitionally equal form `⊤ ≤ y'.1 ⁻¹ᵁ _`. Rewrite using `[h]`.

Conclude with `fun x _ => hy (Set.mem_univ _)`. Rewrite using `[ratVal_fnOf hy, ratVal_fnOf hy', CxPts.ev_conj h hy, RCLike.norm_conj]`.
-/
theorem norm_ratVal_conj {f : X.functionField} {y : CxPts q σ} {y' : CxPts q σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hf : RegAt (under y) f) : ‖ratVal f y'‖ = ‖ratVal f y‖ := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn q σ U := mem_ptsIn.2 hU
  have hy' : y' ∈ ptsIn q σ' U := by
    change ⊤ ≤ y'.1 ⁻¹ᵁ _
    rw [h]
    exact fun x _ => hy (Set.mem_univ _)
  rw [ratVal_fnOf hy, ratVal_fnOf hy', CxPts.ev_conj h hy, RCLike.norm_conj]

def unitMetric {L : LB X} (hL : L.IsLB) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    (hu : ∀ (σ : k →+* ℂ) (y : CxPts q σ) (i : L.ι), y ∈ ptsIn q σ (L.U i) → UnitAt (under y) (r i : X.functionField)) :
    HermLB q where
  B := L
  isLB := hL
  φ σ :=
    { isLB := hL
      φ := fun i y => Real.log (‖ratVal (r i : X.functionField) y‖ ^ 2)
      trans := fun i j y hi hj => by
        have hij := mem_ptsIn_inf.2 ⟨hi, hj⟩
        have h := hu σ y j hj
        rw [hr i j (gen_mem (mem_ptsIn.1 hij)), ratVal_mul (regAt_fnOf (mem_ptsIn.1 hij) _ _) h.regAt,
          ratVal_fnOf hij, log_normSq_mul (ev_ne_zero hij (Units.isUnit _)) (ratVal_ne_zero h), CxPts.gv]
        ring }
  cInf σ i y hy := cInfAt_log_ratVal (hu σ y i hy)
  conj σ σ' i y y' h hy := by
    change Real.log _ = Real.log _
    rw [norm_ratVal_conj h (hu σ y i hy).regAt]

/- English proof (translation)
Introduce `k _ X _ q p hp E hE`. Establish `P` using `presents_toLB E`. Establish `off (σ : k →+* ℂ) (y : CxPts q σ) : under y ∉ E.supp` using `fun h => h (hE _ (not_ov_under hp y))`. Use `⟨unitMetric P.isLB P.isRatSec fun σ y i hi => not_not.1 (mt (P.isEqn i _ (mem_ptsIn.1 hi)).mem_supp_iff.2 (off σ y)), _, P.isRatSec, (presents_divOfRatSec P.isLB P.isRatSec).unique P, fun σ y => ⟨mem_offSupp.2 (off σ y), ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Real.log _ - Real.log (_ ^ 2) / 2 = 0`.

Rewrite using `[Real.log_pow]`. Use `push_cast`. Conclude with `sub_eq_zero.2 (mul_div_cancel_left₀ _ two_ne_zero).symm`.
-/
theorem exists_can_of_vert : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (p : ℕ), p ≠ 0 →
    ∀ E : CartierDiv X, Vert p E → ∃ M : HermLB q, Can M E := by
  intro k _ X _ q p hp E hE
  have P := presents_toLB E
  have off (σ : k →+* ℂ) (y : CxPts q σ) : under y ∉ E.supp := fun h => h (hE _ (not_ov_under hp y))
  refine ⟨unitMetric P.isLB P.isRatSec fun σ y i hi =>
    not_not.1 (mt (P.isEqn i _ (mem_ptsIn.1 hi)).mem_supp_iff.2 (off σ y)), _, P.isRatSec,
    (presents_divOfRatSec P.isLB P.isRatSec).unique P, fun σ y => ⟨mem_offSupp.2 (off σ y), ?_⟩⟩
  change Real.log _ - Real.log (_ ^ 2) / 2 = 0
  rw [Real.log_pow]
  push_cast
  exact sub_eq_zero.2 (mul_div_cancel_left₀ _ two_ne_zero).symm

end GlobalTheory.LatChain

end
