import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain.CanTens

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem presents_dual {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (-D) (CechPic.dual L) fun i => (r i)⁻¹ := by
  refine ⟨isLB_dual h.isLB, fun i j hij => ?_, fun i x hx => (h.isEqn i x hx).neg⟩
  change (((r i)⁻¹ : X.functionFieldˣ) : X.functionField) =
    fnOf (L.U i ⊓ L.U j) hij ((L.g i j)⁻¹ : Γ(X, L.U i ⊓ L.U j)ˣ) * ((r j)⁻¹ : X.functionFieldˣ)
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, h.isRatSec i j hij, mul_inv]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem ratVal_inv {σ : k →+* ℂ} {y : CxPts q σ} {f : X.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have h1 : UnitAt (under y) (1 : X.functionField) := unitAt_one _
  have e1 : ratVal (1 : X.functionField) y = 1 := by
    have e := ratVal_mul h1.regAt h1.regAt
    rw [mul_one] at e
    exact (mul_eq_left₀ (ratVal_ne_zero h1)).1 e.symm
  have e := ratVal_mul hf.regAt hf.inv.regAt
  rw [mul_inv_cancel₀ hf.ne_zero, e1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem can_tens {M M' : HermLB q} {E E' : CartierDiv X} (h : Can M E) (h' : Can M' E') :
    Can (M.tens M') (E + E') := by
  obtain ⟨r, hr, rfl, H⟩ := h
  obtain ⟨r', hr', rfl, H'⟩ := h'
  have P := (presents_divOfRatSec M.isLB hr).tens (presents_divOfRatSec M'.isLB hr')
  refine ⟨fun c => r c.1 * r' c.2, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P, fun σ y => ?_⟩
  obtain ⟨a, b⟩ := H σ y
  obtain ⟨a', b'⟩ := H' σ y
  refine ⟨mem_offSupp.2 fun hy => ?_, ?_⟩
  · rcases CartierDiv.supp_add_le _ _ hy with hy | hy
    · exact mem_offSupp.1 a hy
    · exact mem_offSupp.1 a' hy
  · have hc := CxPts.mem_ptsIn_inf.1 (CxPts.mem_pick ((M.tens M').φ σ).isLB y)
    rw [logNorm_eq _ hr a hc.1] at b
    rw [logNorm_eq _ hr' a' hc.2] at b'
    have u := hr.unitAt M.isLB a hc.1
    have u' := hr'.unitAt M'.isLB a' hc.2
    have e := Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero u)) (norm_ne_zero_iff.2 (ratVal_ne_zero u'))
    rw [← norm_mul, ← ratVal_mul u.regAt u'.regAt] at e
    refine (congrArg₂ (· - ·) e (add_div _ _ _)).trans ?_
    linarith

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem can_dual {M : HermLB q} {E : CartierDiv X} (h : Can M E) : Can M.dual (-E) := by
  obtain ⟨r, hr, rfl, H⟩ := h
  have P := presents_dual (presents_divOfRatSec M.isLB hr)
  refine ⟨fun i => (r i)⁻¹, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P, fun σ y => ?_⟩
  obtain ⟨a, b⟩ := H σ y
  refine ⟨mem_offSupp.2 fun hy => hy ?_, ?_⟩
  · have := CartierDiv.IsEqn.neg (not_not.1 (mem_offSupp.1 a))
    rwa [inv_one] at this
  · have hc := CxPts.mem_pick (M.dual.φ σ).isLB y
    rw [logNorm_eq _ hr a hc] at b
    have u := hr.unitAt M.isLB a hc
    have e := congrArg (fun z : ℂ => Real.log ‖z‖) (ratVal_inv u)
    simp only [norm_inv, Real.log_inv] at e
    rw [← Units.val_inv_eq_inv_val] at e
    refine (congrArg₂ (· - ·) e (neg_div _ _)).trans ?_
    linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem can_tens_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (M M' : HermLB q), (∀ E E' : CartierDiv X, Can M E → Can M' E' → Can (M.tens M') (E + E') ∧ Can M.dual (-E)) ∧ ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) (r' : M'.B.ι → X.functionFieldˣ) (hr' : IsRatSec M'.B r'), ∃ (s : (M.tens M').B.ι → X.functionFieldˣ) (hs : IsRatSec (M.tens M').B s), (M.tens M').div hs = M.div hr + M'.div hr' := by
  intro k _ X _ q M M'
  refine ⟨fun E E' h h' => ⟨can_tens h h', can_dual h⟩, fun r hr r' hr' => ?_⟩
  have P := (presents_divOfRatSec M.isLB hr).tens (presents_divOfRatSec M'.isLB hr')
  exact ⟨fun c => r c.1 * r' c.2, P.isRatSec, (presents_divOfRatSec _ P.isRatSec).unique P⟩

end GlobalTheory.LatChain.CanTens

end
