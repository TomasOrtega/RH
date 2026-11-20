import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem cwA_add_k (w : InfinitePlace F) (X Y : Mx F E d.m d.n) : d.cw w (X + Y) = d.cw w X + d.cw w Y := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem cwA_realAd_k (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    d.cw w (realAd F t • X) = (t : ℂ) • d.cw w X := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, GlobalTheory.RealScalar.piInf_realAd_smul]
/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem locA_add_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X Y : Mx F E d.m d.n) :
    R.loc w (X + Y) = R.loc w X + R.loc w Y := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KFP.cwA_add_k, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _
/- English proof (translation)
Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem locA_realAd_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    R.loc w (realAd F t • X) = (t : ℂ) • R.loc w X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KFP.cwA_realAd_k, Matrix.mul_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  rfl
def arcAF_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ :=
  fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem arcA_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X) := rfl
/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.
-/
theorem arc_add'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X Y : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X + _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R Y := by
  have : _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X + _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R Y := by
    funext i
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.locA_add_k, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, this, map_add]
/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.
-/
theorem arc_realAd'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (realAd F t • X) = t • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X := by
  have : _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R (realAd F t • X) = t • _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X := by
    funext i
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.locA_realAd_k, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, this, map_smul]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem crdA_add_k (X Y : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Y) k = d.crd X k + d.crd Y k := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem sndA_crd_of_k (Z : Mx F E d.m d.n) (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have h1 : finOne F • Z k.1 k.2.1 = 0 := by
    have := congrFun (congrFun hZ k.1) k.2.1
    simpa using this
  have h2 : finOne F * (Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2 = 0 := by
    have := congrArg (fun z => (Algebra.TensorProduct.basis (AF F) d.bs).repr z k.2.2) h1
    simpa only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] using this
  have h3 : (1 : FiniteAdeleRing (𝓞 F) F) * ((Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2).2 = 0 :=
    congrArg Prod.snd h2
  rw [one_mul] at h3
  exact h3
/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fin_add_of'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d (X + Z) = _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X := by
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.crdA_add_k]
  show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.sndA_crd_of_k Z hZ k, add_zero]
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem fin_realAd_smul'_k {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (t : ℝ) : finOne F • (realAd F t • Z) = 0 := by
  rw [smul_comm, hZ, smul_zero]
/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.
-/
theorem gau_eq'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k R X = (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) := by
  have hn : ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2 = ∑ w, ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.equiv, if_true, if_false]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k, fP, evX, map_one, one_mul, gs]
  rw [hn, ← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
