import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHIter
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGEB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGE

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Jac

variable {k r : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩`.
-/
theorem skHaar_of_cs {U : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : Formalism.MainNotions.S.IsHaarOn U μ :=
  ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩

def fA (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r) : Mt k r :=
  fun i j => ((Matrix.of a)⁻¹ * g * Matrix.of m * Matrix.of b) i j

def fB (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r) : Mt k r :=
  fun i j => (Matrix.of a * g * Matrix.of m * (Matrix.of b)⁻¹) i j

/- English proof (translation)
Establish `e : (fun p : (Mt k r × Mt k r) × Mt k r => fA g p.1.1 p.1.2 p.2) = fun p => (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => ((Matrix.of p.1.1)⁻¹) i j : Mt k r) * Matrix.of (g : Mt k r)) i j : Mt k r) * Matrix.of p.2) i j : Mt k r) * Matrix.of p.1. …`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `mulMt_meas (mulMt_meas (mulMt_meas (invMt_meas (measurable_fst.comp measurable_fst)) measurable_const) measurable_snd) (measurable_snd.comp measurable_fst)`.
-/
theorem meas_fA (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable fun p : (Mt k r × Mt k r) × Mt k r => fA g p.1.1 p.1.2 p.2 := by
  have e : (fun p : (Mt k r × Mt k r) × Mt k r => fA g p.1.1 p.1.2 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of
        (fun i j => ((Matrix.of p.1.1)⁻¹) i j : Mt k r) * Matrix.of (g : Mt k r)) i j : Mt k r) *
        Matrix.of p.2) i j : Mt k r) * Matrix.of p.1.2) i j : Mt k r) := by
    funext p; rfl
  rw [e]
  exact mulMt_meas (mulMt_meas (mulMt_meas (invMt_meas (measurable_fst.comp measurable_fst)) measurable_const)
    measurable_snd) (measurable_snd.comp measurable_fst)

/- English proof (translation)
Establish `e : (fun p : (Mt k r × Mt k r) × Mt k r => fB g p.1.1 p.1.2 p.2) = fun p => (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of p.1.1 * Matrix.of (g : Mt k r)) i j : Mt k r) * Matrix.of p.2) i j : Mt k r) * Matrix.of (fun i j => ((Matrix.of p.1.2)⁻¹) i j : Mt k r …`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `mulMt_meas (mulMt_meas (mulMt_meas (measurable_fst.comp measurable_fst) measurable_const) measurable_snd) (invMt_meas (measurable_snd.comp measurable_fst))`.
-/
theorem meas_fB (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable fun p : (Mt k r × Mt k r) × Mt k r => fB g p.1.1 p.1.2 p.2 := by
  have e : (fun p : (Mt k r × Mt k r) × Mt k r => fB g p.1.1 p.1.2 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of p.1.1 * Matrix.of (g : Mt k r)) i j : Mt k r) *
        Matrix.of p.2) i j : Mt k r) * Matrix.of (fun i j => ((Matrix.of p.1.2)⁻¹) i j : Mt k r)) i j : Mt k r) := by
    funext p; rfl
  rw [e]
  exact mulMt_meas (mulMt_meas (mulMt_meas (measurable_fst.comp measurable_fst) measurable_const) measurable_snd)
    (invMt_meas (measurable_snd.comp measurable_fst))

/- English proof (translation)
Set `P : Mt k r × Mt k r → Mt k r` to `fun p => ((Matrix.of a0)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`. Establish `hP : Continuous P` using `by show Continuous fun p : Mt k r × Mt k r => ((Matrix.of a0)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) fun_prop`. Conclude with `hf.comp hP.measurable`.
-/
theorem meas_fA_slice (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun p : Mt k r × Mt k r => f (fA g a0 p.1 p.2) := by
  let P : Mt k r × Mt k r → Mt k r := fun p =>
    ((Matrix.of a0)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  have hP : Continuous P := by
    show Continuous fun p : Mt k r × Mt k r =>
      ((Matrix.of a0)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    fun_prop
  exact hf.comp hP.measurable

/- English proof (translation)
The claim follows from `hf.comp (meas_PQinv (fun p : Mt k r × Mt k r => Matrix.of a0 * g * Matrix.of p.2) (fun p => Matrix.of p.1) (by fun_prop) (by fun_prop))`.
-/
theorem meas_fB_slice (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun p : Mt k r × Mt k r => f (fB g a0 p.1 p.2) :=
  hf.comp (meas_PQinv (fun p : Mt k r × Mt k r => Matrix.of a0 * g * Matrix.of p.2) (fun p => Matrix.of p.1)
    (by fun_prop) (by fun_prop))

/- English proof (translation)
Establish `h1 : ((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ = Matrix.of a` using `Matrix.nonsing_inv_nonsing_inv _ ha`. Use `show (fun i j => (((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ * g * Matrix.of m * (Matrix.of b)⁻¹) i j : Mt k r) = fun i j => (Matrix.of a * g * Matrix.of m * (Matrix.of b)⁻¹) i j`. Rewrite using `[h1]`.
-/
theorem fA_inv (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r)
    (ha : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det) :
    fA g (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) m = fB g a b m := by
  have h1 : ((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ = Matrix.of a :=
    Matrix.nonsing_inv_nonsing_inv _ ha
  show (fun i j => (((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ * g * Matrix.of m *
      (Matrix.of b)⁻¹) i j : Mt k r) = fun i j => (Matrix.of a * g * Matrix.of m * (Matrix.of b)⁻¹) i j
  rw [h1]

/- English proof (translation)
Introduce `k r νN νb hN hb g f hf`. Establish `sN` using `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN`. Establish `sb` using `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hb`. Establish `hinv : νN.map Formalism.FourierDecayAlt.B2.invM = νN` using `Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) νN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN`. Establish `hA` using `hf.comp (meas_fA (k := k) (r := r) g)`.

Establish `hB` using `hf.comp (meas_fB (k := k) (r := r) g)`. Establish `e0 : (fun p : (Mt k r × Mt k r) × Mt k r => f ((Matrix.of p.1.1)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1.2)) = fun p => f (fA g p.1.1 p.1.2 p.2)` using `by funext p; rfl`. Rewrite using `[e0, lintegral_prod (fun p : (Mt k r × Mt k r) × Mt k r => f (fA g p.1.1 p.1.2 p.2)) hA.aemeasurable]`. Rewrite using `[lintegral_prod (fun q : Mt k r × Mt k r => ∫⁻ m, f (fA g q.1 q.2 m) ∂νb) (hA.lintegral_prod_right' (ν := νb)).aemeasurable]`. Establish `key : ∀ F : Mt k r → ℝ≥0∞, Measurable F → ∫⁻ a, F a ∂νN = ∫⁻ a, F (Formalism.FourierDecayAlt.B2.invM a) ∂νN`.

Introduce `F hF`. Use `conv_lhs => rw [← hinv]`. Conclude with `lintegral_map hF Formalism.FourierDecayAlt.P.B2x1.invM_meas`. Establish `hF : Measurable fun a : Mt k r => ∫⁻ b, ∫⁻ m, f (fA g a b m) ∂νb ∂νN` using `(hA.lintegral_prod_right' (ν := νb)).lintegral_prod_right' (ν := νN)`. Use `(key _ hF).trans ?_` and prove the remaining obligations.

Use `lintegral_congr_ae ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ a ∂νN, (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r` using `ae_iff.2 hN.conc`. Use `filter_upwards [hae] with a ha`. Establish `hau : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det` using `unit_of_UH ha.1`. Establish `hG : Measurable fun b : Mt k r => ∫⁻ m, f (fA g (Formalism.FourierDecayAlt.B2.invM a) b m) ∂νb`.

Conclude with `(meas_fA_slice g (Formalism.FourierDecayAlt.B2.invM a) hf).lintegral_prod_right'`. Use `(key _ hG).trans ?_` and prove the remaining obligations. Establish `e1 : ∀ b m : Mt k r, f (fA g (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) m) = f (fB g a b m)` using `fun b m => by rw [fA_inv g a b m hau]`. Repeatedly rewrite using `[e1]`. Use `lintegral_lintegral_swap ?_` and prove the remaining obligations.

Conclude with `(meas_fB_slice g a hf).aemeasurable`.
-/
theorem itgSwap : ItgSwap := by
  intro k r νN νb hN hb g f hf
  have sN := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN
  have sb := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hb
  have hinv : νN.map Formalism.FourierDecayAlt.B2.invM = νN :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) νN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
  have hA := hf.comp (meas_fA (k := k) (r := r) g)
  have hB := hf.comp (meas_fB (k := k) (r := r) g)
  have e0 : (fun p : (Mt k r × Mt k r) × Mt k r => f ((Matrix.of p.1.1)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1.2)) =
      fun p => f (fA g p.1.1 p.1.2 p.2) := by funext p; rfl
  rw [e0, lintegral_prod (fun p : (Mt k r × Mt k r) × Mt k r => f (fA g p.1.1 p.1.2 p.2)) hA.aemeasurable]
  rw [lintegral_prod (fun q : Mt k r × Mt k r => ∫⁻ m, f (fA g q.1 q.2 m) ∂νb)
    (hA.lintegral_prod_right' (ν := νb)).aemeasurable]

  have key : ∀ F : Mt k r → ℝ≥0∞, Measurable F → ∫⁻ a, F a ∂νN = ∫⁻ a, F (Formalism.FourierDecayAlt.B2.invM a) ∂νN := by
    intro F hF
    conv_lhs => rw [← hinv]
    exact lintegral_map hF Formalism.FourierDecayAlt.P.B2x1.invM_meas
  have hF : Measurable fun a : Mt k r => ∫⁻ b, ∫⁻ m, f (fA g a b m) ∂νb ∂νN :=
    (hA.lintegral_prod_right' (ν := νb)).lintegral_prod_right' (ν := νN)
  refine (key _ hF).trans ?_
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ a ∂νN, (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r :=
    ae_iff.2 hN.conc
  filter_upwards [hae] with a ha
  have hau : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det := unit_of_UH ha.1
  have hG : Measurable fun b : Mt k r => ∫⁻ m, f (fA g (Formalism.FourierDecayAlt.B2.invM a) b m) ∂νb := by
    exact (meas_fA_slice g (Formalism.FourierDecayAlt.B2.invM a) hf).lintegral_prod_right'
  refine (key _ hG).trans ?_
  have e1 : ∀ b m : Mt k r, f (fA g (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) m) = f (fB g a b m) :=
    fun b m => by rw [fA_inv g a b m hau]
  simp_rw [e1]
  refine lintegral_lintegral_swap ?_
  exact (meas_fB_slice g a hf).aemeasurable

end Formalism.L2.SG.Pf.BH

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

/- English proof (translation)
Introduce `k r μb hμb`. Take `⟨νG, hG⟩` from `Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r`. Take `⟨νN, hN⟩` from `Formalism.FourierDecayAlt.P.unipotent_haar_exists k r`. Take `⟨νb, hb⟩` from `Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r`. Take `⟨C, hC, hI⟩` from `Formalism.FourierDecayAlt.P.iterated_integration_formula k r νG νN νb hG hN hb`.

Take `⟨cb, cb0, cbt, hμB⟩` from `Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) hb hμb.1`. Take `⟨cN, cN0, cNt, hμN⟩` from `Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top)`. Use `set D : ℝ≥0∞ := cN * cb * cN with hD`. Establish `hD0 : D ≠ 0` using `by simp [hD, cN0, cb0]`. Establish `hDt : D ≠ ∞` using `by simp [hD, ENNReal.mul_eq_top, cNt, cbt]`.

Establish `hC0 : (C : ℝ≥0∞) ≠ 0` using `by exact_mod_cast hC.ne'`. Use `set E : ℝ≥0∞ := D / (C : ℝ≥0∞) with hE`. Establish `hEt : E ≠ ∞` using `ENNReal.div_ne_top hDt hC0`. Establish `hE0 : E ≠ 0` using `ENNReal.div_ne_zero.2 ⟨hD0, ENNReal.coe_ne_top⟩`. Use `⟨E.toNNReal • νG, isHaarOn_smul (skHaar_of_cs hG) (ENNReal.toNNReal_pos hE0 hEt), fun φ hφ => ?_⟩` and prove the remaining obligations.

Establish `hR : rhs k r μb φ = D * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) * ∫⁻ n, ∫⁻ m, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j) ∂νN ∂νb ∂νN`. Unfold `rhs`. Rewrite using `[← lintegral_const_mul' _ _ hDt]`. Use `lintegral_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[hμN, hμB]`.

Repeatedly rewrite using `[lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ cNt, lintegral_const_mul' _ _ cbt]`. Repeatedly rewrite using `[lintegral_const_mul' _ _ cNt]`. Rewrite using `[hD]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hR, lintegral_smul_measure, hI φ hφ]`.

Repeatedly rewrite using `[← itgSwap k r νN νb hN hb _ φ hφ]`. Rewrite using `[ENNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal hEt, hE, ← mul_assoc, ENNReal.div_mul_cancel hC0 ENNReal.coe_ne_top]`.
-/
theorem rhsHaar : RhsHaar := by
  intro k r μb hμb
  obtain ⟨νG, hG⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨νN, hN⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  obtain ⟨νb, hb⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  obtain ⟨C, hC, hI⟩ := Formalism.FourierDecayAlt.P.iterated_integration_formula k r νG νN νb hG hN hb
  obtain ⟨cb, cb0, cbt, hμB⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) hb hμb.1
  obtain ⟨cN, cN0, cNt, hμN⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
    (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top)
  set D : ℝ≥0∞ := cN * cb * cN with hD
  have hD0 : D ≠ 0 := by simp [hD, cN0, cb0]
  have hDt : D ≠ ∞ := by simp [hD, ENNReal.mul_eq_top, cNt, cbt]
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  set E : ℝ≥0∞ := D / (C : ℝ≥0∞) with hE
  have hEt : E ≠ ∞ := ENNReal.div_ne_top hDt hC0
  have hE0 : E ≠ 0 := ENNReal.div_ne_zero.2 ⟨hD0, ENNReal.coe_ne_top⟩
  refine ⟨E.toNNReal • νG, isHaarOn_smul (skHaar_of_cs hG) (ENNReal.toNNReal_pos hE0 hEt), fun φ hφ => ?_⟩
  have hR : rhs k r μb φ = D * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
      ∫⁻ n, ∫⁻ m, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j)
        ∂νN ∂νb ∂νN := by
    unfold rhs
    rw [← lintegral_const_mul' _ _ hDt]
    refine lintegral_congr fun c => ?_
    rw [hμN, hμB]
    simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ cNt, lintegral_const_mul' _ _ cbt]
    simp_rw [lintegral_const_mul' _ _ cNt]
    rw [hD]
    ring
  rw [hR, lintegral_smul_measure, hI φ hφ]
  simp_rw [← itgSwap k r νN νb hN hb _ φ hφ]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal hEt, hE, ← mul_assoc, ENNReal.div_mul_cancel hC0 ENNReal.coe_ne_top]

end Formalism.L2.SG.Pf.GE

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨n, hn⟩` from `exists_nat_gt (ρ / (ρ - ‖x‖))`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h1 : 0 < ρ - ‖x‖` using `by linarith`. Establish `h2 : ρ / (ρ - ‖x‖) < (n : ℝ) + 2` using `by linarith`. Establish `h3 : ρ / ((n : ℝ) + 2) < ρ - ‖x‖`. Rewrite using `[div_lt_iff₀ (by positivity)]`.

Rewrite `h2` using `[div_lt_iff₀ h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `⟨n, hn⟩`. Establish `: 0 < ρ / ((n : ℝ) + 2)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ball_eq_iUnion {E : Type*} [NormedAddCommGroup E] (ρ : ℝ) (hρ : 0 < ρ) :
    Metric.ball (0 : E) ρ = ⋃ n : ℕ, Metric.closedBall (0 : E) (ρ - ρ / (n + 2)) := by
  ext x
  simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (ρ / (ρ - ‖x‖))
    refine ⟨n, ?_⟩
    have h1 : 0 < ρ - ‖x‖ := by linarith
    have h2 : ρ / (ρ - ‖x‖) < (n : ℝ) + 2 := by linarith
    have h3 : ρ / ((n : ℝ) + 2) < ρ - ‖x‖ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at h2
      linarith
    linarith
  · rintro ⟨n, hn⟩
    have : 0 < ρ / ((n : ℝ) + 2) := by positivity
    linarith

/- English proof (translation)
Establish `hE` using `Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S`. Unfold `expBall`. Rewrite using `[ball_eq_iUnion ρ hρ, Set.image_iUnion]`. Use `MeasurableSet.iUnion fun n => ?_` and prove the remaining obligations. Conclude with `((isCompact_closedBall _ _).image hE).isClosed.measurableSet`.
-/
theorem measurableSet_expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) (hρ : 0 < ρ) :
    MeasurableSet (expBall (k := k) (r := r) S ρ) := by
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S
  unfold expBall
  rw [ball_eq_iUnion ρ hρ, Set.image_iUnion]
  refine MeasurableSet.iUnion fun n => ?_
  exact ((isCompact_closedBall _ _).image hE).isClosed.measurableSet

/- English proof (translation)
The claim follows from `Formalism.QuantumDeterminants.bigCellMem k r 1 1 (fun a => one_ne_zero) (by simp)`.
-/
theorem long_weyl_element_mem : w0B k r ∈ UH (Hpk k r) :=
  Formalism.QuantumDeterminants.bigCellMem k r 1 1 (fun a => one_ne_zero) (by simp)

/- English proof (translation)
Introduce `k r μ hμ ρ hρ`. Establish `hg : MeasurableSet (gBall k r ρ)` using `measurableSet_expBall (k := k) (r := r) (UH (Hpk k r)) ρ hρ`. Establish `hl : Measurable (lmulM (k` using `k) (r := r) (w0B k r)) := by`. Establish `: Continuous (lmulM (k` using `k) (r := r) (w0B k r)) := by show Continuous fun x : Mt k r => (w0B k r * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`. Conclude with `continuous_const.matrix_mul continuous_id`.

Conclude with `this.measurable`. Establish `e : wBall k r ρ = lmulM (w0B k r) ⁻¹' gBall k r ρ` using `rfl`. Use `⟨e ▸ hl hg, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← Measure.map_apply hl hg, hμ.2.2.2 _ long_weyl_element_mem]`.
-/
theorem gaugeShift : GaugeShift := by
  intro k r μ hμ ρ hρ
  have hg : MeasurableSet (gBall k r ρ) := measurableSet_expBall (k := k) (r := r) (UH (Hpk k r)) ρ hρ
  have hl : Measurable (lmulM (k := k) (r := r) (w0B k r)) := by
    have : Continuous (lmulM (k := k) (r := r) (w0B k r)) := by
      show Continuous fun x : Mt k r =>
        (w0B k r * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have e : wBall k r ρ = lmulM (w0B k r) ⁻¹' gBall k r ρ := rfl
  refine ⟨e ▸ hl hg, ?_⟩
  rw [e, ← Measure.map_apply hl hg, hμ.2.2.2 _ long_weyl_element_mem]

end Formalism.L2.SG.Pf.BH
