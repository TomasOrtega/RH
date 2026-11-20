import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.E0EqSingleNhFst
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.NHeisInt

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def NIntAt (k r : ℕ) : Prop :=
  ∀ μN : Measure (Mt k r), Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN → ∀ b : ℝ, (dimN k r : ℝ) < b →
    ∫⁻ x, ENNReal.ofReal (gN (Matrix.of x) ^ (-b)) ∂μN < ∞

/- English proof (translation)
Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dimN_succ (k r' : ℕ) :
    (dimN k (1 + r') : ℝ) = (dimN k r' : ℝ) + (2 * ((2 * r' + k + 1 : ℕ) : ℝ) + 1) := by
  unfold dimN
  push_cast
  ring

section NIntStepAux

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem ns_gN_cont_mt {k r : ℕ} : Continuous (fun g : Mt k r => gN (Matrix.of g : Mat k r)) := by
  unfold gN; fun_prop

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ns_meas_F {k r : ℕ} (b : ℝ) :
    Measurable (fun x : Mt k r => ENNReal.ofReal (gN (Matrix.of x : Mat k r) ^ (-b))) :=
  ((ns_gN_cont_mt.measurable).pow_const _).ennreal_ofReal

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem ns_cont_mulM {k r : ℕ} : Continuous (mulM (k := k) (r := r)) := by
  unfold mulM
  exact (continuous_fst (X := Mt k r) (Y := Mt k r)).matrix_mul continuous_snd

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem ns_cont_levM (k r' : ℕ) : Continuous (levM k r') := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  show Continuous fun x : Mt k r' => ιLev k 1 r' (Matrix.of x) p q
  unfold ιLev
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ns_meas_heis0 (k r' : ℕ) :
    @Measurable (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := by
  have h : @Continuous (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := continuous_heis0 k r'
  exact h.measurable

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ns_meas_G (k r' : ℕ) (d : ℝ) :
    Measurable (fun x : HPar k r' => ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2)))) := by
  have h : Continuous (fun x : HPar k r' => 1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) :=
    (continuous_const.add (continuous_finsetSum _ fun i _ =>
      Complex.continuous_normSq.comp ((continuous_apply i).comp continuous_fst))).add (continuous_snd.pow 2)
  exact (h.measurable.pow_const _).ennreal_ofReal

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ns_sigmaFinite {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem ns_sq_rpow {t : ℝ} (ht : 0 ≤ t) (z : ℝ) : (t ^ 2) ^ z = t ^ (2 * z) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ns_split {a g S t b d : ℝ} (ha : 1 ≤ a) (hg : 0 ≤ g) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hle : a ^ 2 + S + t ≤ g ^ 2) (hd : 0 ≤ d) (hdb : d ≤ b) :
    g ^ (-b) ≤ (1 + S + t) ^ (-(d / 2)) * a ^ (-(b - d)) := by
  have ha0 : 0 ≤ a := by linarith
  have h1 : 1 + S + t ≤ g ^ 2 := by nlinarith
  have h2 : a ^ 2 ≤ g ^ 2 := by linarith
  have hp : 0 < 1 + S + t := by linarith
  have hp2 : 0 < a ^ 2 := by positivity
  have hg2 : 0 < g ^ 2 := lt_of_lt_of_le hp h1
  have e1 : g ^ (-b) = (g ^ 2) ^ (-(d / 2)) * (g ^ 2) ^ (-((b - d) / 2)) := by
    rw [← Real.rpow_add hg2, ns_sq_rpow hg]
    congr 1; ring
  have e2 : a ^ (-(b - d)) = (a ^ 2) ^ (-((b - d) / 2)) := by
    rw [ns_sq_rpow ha0]; congr 1; ring
  rw [e1, e2]
  have i1 : (g ^ 2) ^ (-(d / 2)) ≤ (1 + S + t) ^ (-(d / 2)) :=
    Real.rpow_le_rpow_of_nonpos hp h1 (by linarith)
  have i2 : (g ^ 2) ^ (-((b - d) / 2)) ≤ (a ^ 2) ^ (-((b - d) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hp2 h2 (by linarith)
  exact mul_le_mul i1 i2 (by positivity) (by positivity)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ns_point (hGL : GNLower) (k r' : ℕ) {b d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ b) (x : HPar k r')
    (n' : Mt k r') (hn : (Matrix.of n' : Mat k r') ∈ Nset k r') :
    ENNReal.ofReal (gN (Matrix.of (mulM ((heis0 k r' x : Mt k (1 + r')), levM k r' n')) : Mat k (1 + r')) ^ (-b)) ≤
      ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2))) *
        ENNReal.ofReal (gN (Matrix.of n' : Mat k r') ^ (-(b - d))) := by
  have hS : 0 ≤ ∑ i, Complex.normSq (x.1 i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hm : (Matrix.of (mulM ((heis0 k r' x : Mt k (1 + r')), levM k r' n')) : Mat k (1 + r')) =
      heis0 k r' x * ιLev k 1 r' (Matrix.of n') := rfl
  rw [hm]
  have key := gN_heis_lev k r' x (Matrix.of n')
  have ha := hGL k r' _ hn.1
  exact ns_split ha (Real.sqrt_nonneg _) hS (sq_nonneg _) (by linarith) hd hdb

end NIntStepAux

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem nIntAt_step (hNR : NRecHaar) (hHU : HaarUnique) (hCN : ClosedN) (hHN : HaarNExists) (hGL : GNLower)
    (k r' : ℕ) (ih : NIntAt k r') : NIntAt k (1 + r') := by
  intro μN hμN b hb
  obtain ⟨μ', hμ'⟩ := hHN k r'
  have hν := hNR k r' μ' hμ'
  obtain ⟨c, hc⟩ := hHU k (1 + r') (Nset k (1 + r')) _ μN (hCN k (1 + r')) hν hμN.conc hμN.left
    hμN.finite_compact
  have hσ : SigmaFinite μ' := ns_sigmaFinite hμ'
  have hdim := dimN_succ k r'
  set m : ℝ := ((2 * r' + k + 1 : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set d : ℝ := ((2 * m + 1) + (b - dimN k r')) / 2 with hd
  have hd1 : 2 * m + 1 < d := by rw [hd]; linarith
  have hd2 : (dimN k r' : ℝ) < b - d := by rw [hd]; linarith
  have hd0 : 0 ≤ d := by linarith
  have hdb : d ≤ b := by
    have : (0 : ℝ) ≤ dimN k r' := Nat.cast_nonneg _
    linarith
  have hae : ∀ᵐ z ∂((volume : Measure (HPar k r')).prod μ'), (Matrix.of z.2 : Mat k r') ∈ Nset k r' := by
    have h0 : ∀ᵐ y ∂μ', (Matrix.of y : Mat k r') ∈ Nset k r' := by rw [ae_iff]; exact hμ'.conc
    exact Measure.quasiMeasurePreserving_snd.ae h0
  have hfin : ∫⁻ x : Mt k (1 + r'), ENNReal.ofReal (gN (Matrix.of x : Mat k (1 + r')) ^ (-b))
      ∂(((μHeis k r').prod (μ'.map (levM k r'))).map mulM) < ∞ := by
    rw [lintegral_map (ns_meas_F b) ns_cont_mulM.measurable, μHeis,
      Measure.map_prod_map (volume : Measure (HPar k r')) μ' (ns_meas_heis0 k r') (ns_cont_levM k r').measurable,
      lintegral_map (f := fun a : Mt k (1 + r') × Mt k (1 + r') => ENNReal.ofReal (gN (Matrix.of (mulM a) : Mat k (1 + r')) ^ (-b)))
        ((ns_meas_F b).comp ns_cont_mulM.measurable)
        ((ns_meas_heis0 k r').prodMap (ns_cont_levM k r').measurable)]
    calc _ ≤ ∫⁻ z : HPar k r' × Mt k r',
          ENNReal.ofReal ((1 + ∑ i, Complex.normSq (z.1.1 i) + z.1.2 ^ 2) ^ (-(d / 2))) *
            ENNReal.ofReal (gN (Matrix.of z.2 : Mat k r') ^ (-(b - d))) ∂((volume : Measure (HPar k r')).prod μ') := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with z hz
          exact ns_point hGL k r' hd0 hdb z.1 z.2 hz
      _ = (∫⁻ x : HPar k r', ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2)))) *
            ∫⁻ y, ENNReal.ofReal (gN (Matrix.of y : Mat k r') ^ (-(b - d))) ∂μ' :=
          lintegral_prod_mul (ns_meas_G k r' d).aemeasurable (ns_meas_F (b - d)).aemeasurable
      _ < ∞ := ENNReal.mul_lt_top (heis_lint_fin (2 * r' + k + 1) (by rw [hm] at hd1; exact_mod_cast hd1))
          (ih μ' hμ' (b - d) hd2)
  rw [hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
