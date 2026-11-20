import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.VandermondeConjugatePrimes
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.VandermondeConjugatePrimes

namespace GlobalTheory.CurveToStdLog

open MvPowerSeries

variable {l : ℕ} [Fact l.Prime] {κ κ' : Type}

/- English proof (translation)
Rewrite using `[PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hb).const ha]`. Both sides reduce to the same expression.
-/
theorem mvsubst_subst {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a) {b : MvPowerSeries κ ℂ_[l]}
    (hb : constantCoeff b = 0) (f : PowerSeries ℂ_[l]) :
    MvPowerSeries.subst a (f.subst b : MvPowerSeries κ ℂ_[l]) = f.subst (MvPowerSeries.subst a b) := by
  rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hb).const ha]
  rfl

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Rewrite using `[GlobalTheory.ExpLogMv.expMv_eq_subst hf, mvsubst_subst hs hf, GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]`.
-/
theorem subst_expMv [Finite κ] {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : ∀ i, constantCoeff (a i) = 0)
    {f : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, mvsubst_subst hs hf,
    GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]

/- English proof (translation)
Rewrite using `[GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg, GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]`. Conclude with `ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg`.
-/
theorem expMv_add {f g : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    expMv (f + g) = expMv f * expMv g := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
    GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

/- English proof (translation)
Rewrite using `[GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]`. Conclude with `ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero`.
-/
theorem expMv_zero : expMv (0 : MvPowerSeries κ ℂ_[l]) = 1 := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using expMv_zero`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi, expMv_add (hf i) (by simp [map_sum, hf]), ih]`.
-/
theorem expMv_sum {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries κ ℂ_[l]}
    (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expMv_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, expMv_add (hf i) (by simp [map_sum, hf]), ih]

/- English proof (translation)
Establish `h` using `(GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).1`. Use `show constantCoeff (-logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0`. Rewrite using `[map_neg, h, neg_zero]`.
-/
theorem cc_ph (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) :
    PowerSeries.constantCoeff g.ph = 0 := by
  have h := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).1
  show constantCoeff (-logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
  rw [map_neg, h, neg_zero]

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero hy _ (cc_ph g hE)`.
-/
theorem cc_phAt (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) : constantCoeff (g.phAt y) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hy _ (cc_ph g hE)

/- English proof (translation)
Establish `hs : HasSubst (fun _ : Unit => y)` using `hasSubst_of_constantCoeff_zero fun _ => hy`. Establish `h` using `congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).2`. Rewrite `h` using `[subst_mul hs, subst_expMv (f := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) (cc_ph g hE), ← coe_substAlgHom hs (R := ℂ_[l]), map_one, coe_substAlgHom]`. Establish `h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]`.

Conclude with `one_ne_zero`. Rewrite using `[MvPowerSeries.inv_eq_iff_mul_eq_one h1]`. Conclude with `h`.
-/
theorem inv_ePhi1 (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) :
    (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
  have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
  have h := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).2
  rw [subst_mul hs, subst_expMv (f := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) (cc_ph g hE), ← coe_substAlgHom hs (R := ℂ_[l]), map_one,
    coe_substAlgHom] at h
  have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
  exact h

end GlobalTheory.CurveToStdLog
