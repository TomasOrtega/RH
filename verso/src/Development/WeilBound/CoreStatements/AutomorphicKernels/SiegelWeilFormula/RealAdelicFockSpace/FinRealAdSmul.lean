import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[SD.cw]`.
-/
theorem cwA_add (w : InfinitePlace F) (X Y : Mx F E d.m d.n) : d.cw w (X + Y) = d.cw w X + d.cw w Y := by
  ext i j
  simp [SD.cw]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[SD.cw, GlobalTheory.RealScalar.piInf_realAd_smul]`.
-/
theorem cwA_realAd (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    d.cw w (realAd F t • X) = (t : ℂ) • d.cw w X := by
  ext i j
  simp [SD.cw, GlobalTheory.RealScalar.piInf_realAd_smul]

/- English proof (translation)
Simplify using `only [RD.loc, cwA_add, Matrix.mul_add]`. Conclude with `Matrix.map_add _ (fun a b => star_add a b) _ _`.
-/
theorem locA_add (R : RD d) (w : InfinitePlace F) (X Y : Mx F E d.m d.n) :
    R.loc w (X + Y) = R.loc w X + R.loc w Y := by
  simp only [RD.loc, cwA_add, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _

/- English proof (translation)
Simplify using `only [RD.loc, cwA_realAd, Matrix.mul_smul]`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[star_mul', Complex.star_def, Complex.conj_ofReal]`. Both sides reduce to the same expression.
-/
theorem locA_realAd (R : RD d) (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    R.loc w (realAd F t • X) = (t : ℂ) • R.loc w X := by
  simp only [RD.loc, cwA_realAd, Matrix.mul_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  rfl

def arcAF (R : RD d) (X : Mx F E d.m d.n) : Iw d → ℝ :=
  fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem arcA_eq (R : RD d) (X : Mx F E d.m d.n) : arc R X = (EuclideanSpace.equiv (Iw d) ℝ).symm (arcAF R X) := rfl

/- English proof (translation)
Establish `: arcAF R (X + Y) = arcAF R X + arcAF R Y`. Use function extensionality and compare the values at `i`. Simplify using `only [arcAF, locA_add, Matrix.add_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[arcA_eq, arcA_eq, arcA_eq, this, map_add]`.
-/
theorem arc_add' (R : RD d) (X Y : Mx F E d.m d.n) : arc R (X + Y) = arc R X + arc R Y := by
  have : arcAF R (X + Y) = arcAF R X + arcAF R Y := by
    funext i
    simp only [arcAF, locA_add, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [arcA_eq, arcA_eq, arcA_eq, this, map_add]

/- English proof (translation)
Establish `: arcAF R (realAd F t • X) = t • arcAF R X`. Use function extensionality and compare the values at `i`. Simplify using `only [arcAF, locA_realAd, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[arcA_eq, arcA_eq, this, map_smul]`.
-/
theorem arc_realAd' (R : RD d) (t : ℝ) (X : Mx F E d.m d.n) : arc R (realAd F t • X) = t • arc R X := by
  have : arcAF R (realAd F t • X) = t • arcAF R X := by
    funext i
    simp only [arcAF, locA_realAd, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [arcA_eq, arcA_eq, this, map_smul]

/- English proof (translation)
Simplify using `[SD.crd]`.
-/
theorem crdA_add (X Y : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Y) k = d.crd X k + d.crd Y k := by
  simp [SD.crd]

/- English proof (translation)
Establish `h1 : finOne F • Z k.1 k.2.1 = 0`. Use `congrFun (congrFun hZ k.1) k.2.1` as an intermediate fact. Simplify using `using this`. Establish `h2 : finOne F * (Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2 = 0`. Use `congrArg (fun z => (Algebra.TensorProduct.basis (AF F) d.bs).repr z k.2.2) h1` as an intermediate fact.

Simplify `this` using `only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul]`. Establish `h3 : (1 : FiniteAdeleRing (𝓞 F) F) * ((Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2).2 = 0` using `congrArg Prod.snd h2`. Rewrite `h3` using `[one_mul]`. Conclude with `h3`.
-/
theorem sndA_crd_of (Z : Mx F E d.m d.n) (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
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
Use function extensionality and compare the values at `k`. Use `show (d.crd (X + Z) k).2 = (d.crd X k).2`. Rewrite using `[crdA_add]`. Use `show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2`. Rewrite using `[sndA_crd_of Z hZ k, add_zero]`.
-/
theorem fin_add_of' (R : RD d) {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (X : Mx F E d.m d.n) :
    fin d (X + Z) = fin d X := by
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [crdA_add]
  show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  rw [sndA_crd_of Z hZ k, add_zero]

/- English proof (translation)
Rewrite using `[smul_comm, hZ, smul_zero]`.
-/
theorem fin_realAd_smul' {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (t : ℝ) : finOne F • (realAd F t • Z) = 0 := by
  rw [smul_comm, hZ, smul_zero]

/- English proof (translation)
Establish `hn : ‖arc R X‖ ^ 2 = ∑ w, ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2`. Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Simplify using `only [Fintype.sum_prod_type, Fintype.sum_bool, arc, Real.norm_eq_abs, sq_abs]`. Use `Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [EuclideanSpace.equiv, if_true, if_false]`.

Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[sq]`. Simplify using `only [gau, fP, evX, map_one, one_mul, gs]`. Rewrite using `[hn, ← Complex.exp_sum, Complex.ofReal_exp]`. Use `congr 1`.

Use `push_cast`. Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib]`.
-/
theorem gau_eq' (R : RD d) (X : Mx F E d.m d.n) : gau R X = (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) := by
  have hn : ‖arc R X‖ ^ 2 = ∑ w, ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, arc, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.equiv, if_true, if_false]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  simp only [gau, fP, evX, map_one, one_mul, gs]
  rw [hn, ← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

end PositivityTheory.SiegelWeilFormula.KFP

end
