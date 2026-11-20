import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InParamMap

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_rescale]`. Use `show vp ^ n.degree * MvPowerSeries.coeff n f = _`. Use `congr 1`. Rewrite using `[Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]`.

Both sides reduce to the same expression.
-/
theorem atPi_eq_rescale {σ R : Type} [CommRing R] (vp : R) (f : MvPowerSeries σ R) :
    atPi vp f = MvPowerSeries.rescale (fun _ => vp) f := by
  ext n
  rw [MvPowerSeries.coeff_rescale]
  show vp ^ n.degree * MvPowerSeries.coeff n f = _
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_C_mul]`. Use `show vp ^ n.degree * MvPowerSeries.coeff n _ = _`. Simplify using `only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
private theorem atPi_sum_C_mul_X_eq_C_mul {σ R ι : Type} [CommRing R] (vp : R) (t : Finset ι) (a : ι → R)
    (g : ι → σ) :
    atPi vp (∑ i ∈ t, MvPowerSeries.C (a i) * MvPowerSeries.X (g i)) =
      MvPowerSeries.C vp * ∑ i ∈ t, MvPowerSeries.C (a i) * MvPowerSeries.X (g i) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_C_mul]
  show vp ^ n.degree * MvPowerSeries.coeff n _ = _
  simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs with h
  · subst h
    simp
  · simp

/- English proof (translation)
Apply the tactic sequence `rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp only [Sys.coordZA] <;> exact atPi_sum_C_mul_X_eq_C_mul _ _ _ _`.
-/
theorem atPi_coordZA (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    atPi vp (X.coordZA K' j x) = MvPowerSeries.C vp * X.coordZA K' j x := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp only [Sys.coordZA] <;> exact atPi_sum_C_mul_X_eq_C_mul _ _ _ _

/- English proof (translation)
Apply the tactic sequence `rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>`. Simplify using `only [Sys.coordZA, map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, ← IsScalarTower.algebraMap_apply]`.
-/
theorem map_coordZA (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.map (algebraMap K1 K') (X.coordZA K1 j x) = X.coordZA K' j x := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>
    simp only [Sys.coordZA, map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X,
      ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Establish `hA1 : MvPowerSeries.HasSubst (X.coordZA K1 j)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K1 j)`. Establish `hA' : MvPowerSeries.HasSubst (X.coordZA K' j)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K' j)`. Rewrite using `[Sys.ThZA, MvPowerSeries.map_subst hA1]`. Simplify using `only [map_coordZA X K1 K']`. Rewrite using `[atPi_eq_rescale, MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hA' (MvPowerSeries.HasSubst.smul_X _)]`.

Use `congrArg (fun a => MvPowerSeries.subst a (MvPowerSeries.map (algebraMap K1 K') U)) (funext fun s => ?_)` and prove the remaining obligations. Rewrite using `[← MvPowerSeries.rescale_eq_subst, ← atPi_eq_rescale, atPi_coordZA]`.
-/
theorem atPi_map_ThZA (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K') (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) K1) :
    atPi vp (MvPowerSeries.map (algebraMap K1 K') (X.ThZA K1 j U)) =
      MvPowerSeries.subst (fun x => MvPowerSeries.C vp * X.coordZA K' j x) (MvPowerSeries.map (algebraMap K1 K') U) := by
  have hA1 : MvPowerSeries.HasSubst (X.coordZA K1 j) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K1 j)
  have hA' : MvPowerSeries.HasSubst (X.coordZA K' j) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K' j)
  rw [Sys.ThZA, MvPowerSeries.map_subst hA1]
  simp only [map_coordZA X K1 K']
  rw [atPi_eq_rescale, MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.subst_comp_subst_apply hA' (MvPowerSeries.HasSubst.smul_X _)]
  refine congrArg (fun a => MvPowerSeries.subst a (MvPowerSeries.map (algebraMap K1 K') U)) (funext fun s => ?_)
  rw [← MvPowerSeries.rescale_eq_subst, ← atPi_eq_rescale, atPi_coordZA]

/- English proof (translation)
Introduce `j K1 _ _ R1 U hU K' _ _ _ _ R' vp hvp hRp hR1`. Rewrite using `[atPi_map_ThZA X K1 K' vp j U]`. Use `genInt p K' R' vp hvp hRp _ (inParam_map p K' K1 R1 R' hR1 U hU) (X.coordZA K' j) (coordZA_const X K' j) ?_` and prove the remaining obligations. Introduce `i`. Apply the tactic sequence `rcases i with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp only [Sys.coordZA] <;>`.

Conclude with `IntR_sum _ _ (fun s _ => IntR_mul (IntR_C (hRp (W_mem_Rp (p := p) (K' := K') vp _))) (IntR_X _))`.
-/
theorem restSIntA : RestSIntA X := by
  intro j K1 _ _ R1 U hU K' _ _ _ _ R' vp hvp hRp hR1
  rw [atPi_map_ThZA X K1 K' vp j U]
  refine genInt p K' R' vp hvp hRp _ (inParam_map p K' K1 R1 R' hR1 U hU) (X.coordZA K' j)
    (coordZA_const X K' j) ?_
  intro i
  rcases i with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp only [Sys.coordZA] <;>
    exact IntR_sum _ _ (fun s _ => IntR_mul (IntR_C (hRp (W_mem_Rp (p := p) (K' := K') vp _))) (IntR_X _))

end Formalism.MainNotions.FormalGroupSystem.Pf
