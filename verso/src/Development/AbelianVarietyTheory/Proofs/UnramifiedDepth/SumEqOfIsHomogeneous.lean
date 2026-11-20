import Mathlib
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelliStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DetFrobeniusSubPowSupportStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorialWeightedPairingDetPowProportionalStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DeterminantPairingQuotientValuationLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdIccMulFactorial
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreAndCapelli
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RadiiValuationDifferences
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NewtonBoundPosAndNewtonStep
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockValueOnRowsEqStatement

section
open ReciprocityTheory.PGsh

noncomputable section

namespace GlobalTheory.OddBlock.ExpShift

section General

variable {C : Type} [Field C] {σ : Type}

def form (φ : (σ →₀ ℕ) → C) : MvPolynomial σ C →ₗ[C] C :=
  (MvPolynomial.basisMonomials σ C).constr C φ

/- English proof (translation)
Establish `h : (MvPolynomial.monomial A c : MvPolynomial σ C) = c • MvPolynomial.basisMonomials σ C A`. Simplify using `[MvPolynomial.smul_monomial]`. Rewrite using `[h, map_smul, form, Module.Basis.constr_basis, smul_eq_mul]`.
-/
theorem form_monomial (φ : (σ →₀ ℕ) → C) (A : σ →₀ ℕ) (c : C) :
    form φ (MvPolynomial.monomial A c) = c * φ A := by
  have h : (MvPolynomial.monomial A c : MvPolynomial σ C) = c • MvPolynomial.basisMonomials σ C A := by
    simp [MvPolynomial.smul_monomial]
  rw [h, map_smul, form, Module.Basis.constr_basis, smul_eq_mul]

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Simplify using `only [form_monomial]`.
-/
theorem form_eq_sum (φ : (σ →₀ ℕ) → C) (P : MvPolynomial σ C) :
    form φ P = ∑ A ∈ P.support, MvPolynomial.coeff A P * φ A := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  simp only [form_monomial]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u a => rw [MvPolynomial.X, MvPolynomial.monomial_mul, form_monomial, form_monomial, mul_one]`. Consider the case `add p q hp hq => rw [add_mul, map_add, map_add, hp, hq]`.
-/
theorem form_mul_X (φ : (σ →₀ ℕ) → C) (P : MvPolynomial σ C) (i : σ) :
    form φ (P * MvPolynomial.X i) = form (fun A => φ (A + Finsupp.single i 1)) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a => rw [MvPolynomial.X, MvPolynomial.monomial_mul, form_monomial, form_monomial, mul_one]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq]

/- English proof (translation)
Simplify using `only [form_eq_sum, mul_add, Finset.sum_add_distrib]`.
-/
theorem form_add (φ ψ : (σ →₀ ℕ) → C) (P : MvPolynomial σ C) :
    form (fun A => φ A + ψ A) P = form φ P + form ψ P := by
  simp only [form_eq_sum, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [form_eq_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem form_mul_left (c : C) (φ : (σ →₀ ℕ) → C) (P : MvPolynomial σ C) :
    form (fun A => c * φ A) P = c * form φ P := by
  simp only [form_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u a => rw [MvPolynomial.rename_monomial, form_monomial, form_monomial]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`.
-/
theorem form_rename {τ : Type} (e : σ → τ) (φ : (τ →₀ ℕ) → C) (P : MvPolynomial σ C) :
    form φ (MvPolynomial.rename e P) = form (fun A => φ (A.mapDomain e)) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a => rw [MvPolynomial.rename_monomial, form_monomial, form_monomial]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

def fact (C : Type) [Field C] (A : σ →₀ ℕ) : C := A.prod fun _ e => (e.factorial : C)

/- English proof (translation)
Establish `h : ∀ B : σ →₀ ℕ, fact C B = ((B i).factorial : C) * fact C (B.erase i)` using `fun B => by`. Rewrite using `[fact, fact, Finsupp.mul_prod_erase' B i (fun _ e => (e.factorial : C)) (by simp)]`. Rewrite using `[h, h A, Finsupp.erase_add, Finsupp.erase_single, add_zero]`. Simplify using `[Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fact_add_single (A : σ →₀ ℕ) (i : σ) :
    fact C (A + Finsupp.single i 1) = fact C A * (A i + 1) := by
  classical
  have h : ∀ B : σ →₀ ℕ, fact C B = ((B i).factorial : C) * fact C (B.erase i) := fun B => by
    rw [fact, fact, Finsupp.mul_prod_erase' B i (fun _ e => (e.factorial : C)) (by simp)]
  rw [h, h A, Finsupp.erase_add, Finsupp.erase_single, add_zero]
  simp [Nat.factorial_succ]
  ring

def pair (P : MvPolynomial σ C) (f : MvPowerSeries σ C) : C :=
  form (fun A => fact C A * MvPowerSeries.coeff A f) P

/- English proof (translation)
Rewrite using `[pair, pair, form_mul_X]`. Use `congr 2`. Use function extensionality and compare the values at `A`. Rewrite using `[fact_add_single, MvPowerSeries.coeff_pderiv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_mul_X (P : MvPolynomial σ C) (f : MvPowerSeries σ C) (i : σ) :
    pair (P * MvPolynomial.X i) f = pair P (MvPowerSeries.pderiv C i f) := by
  rw [pair, pair, form_mul_X]
  congr 2
  funext A
  rw [fact_add_single, MvPowerSeries.coeff_pderiv]
  ring

/- English proof (translation)
Simplify using `only [pair, map_add, mul_add, form_add]`.
-/
theorem pair_add_right (P : MvPolynomial σ C) (f g : MvPowerSeries σ C) :
    pair P (f + g) = pair P f + pair P g := by
  simp only [pair, map_add, mul_add, form_add]

/- English proof (translation)
Simplify using `only [pair, ← form_mul_left, map_smul, smul_eq_mul]`. Use `congr 2`. Use function extensionality and compare the values at `A`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_smul_right (P : MvPolynomial σ C) (c : C) (f : MvPowerSeries σ C) :
    pair P (c • f) = c * pair P f := by
  simp only [pair, ← form_mul_left, map_smul, smul_eq_mul]
  congr 2
  funext A
  ring

end General

section Two

variable {C : Type} [Field C] {κ κ' : Type}

def slice (b : κ' →₀ ℕ) (g : MvPowerSeries (κ ⊕ κ') C) : MvPowerSeries κ C :=
  fun A => MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b)) g

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_slice (b : κ' →₀ ℕ) (g : MvPowerSeries (κ ⊕ κ') C) (A : κ →₀ ℕ) :
    MvPowerSeries.coeff A (slice b g) =
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b)) g := rfl

/- English proof (translation)
Use extensionality with `A`. Simplify using `only [coeff_slice, map_add]`.
-/
theorem slice_add (b : κ' →₀ ℕ) (f g : MvPowerSeries (κ ⊕ κ') C) :
    slice b (f + g) = slice b f + slice b g := by
  ext A
  simp only [coeff_slice, map_add]

/- English proof (translation)
Use extensionality with `A`. Simplify using `only [coeff_slice, map_smul]`.
-/
theorem slice_smul (b : κ' →₀ ℕ) (c : C) (g : MvPowerSeries (κ ⊕ κ') C) :
    slice b (c • g) = c • slice b g := by
  ext A
  simp only [coeff_slice, map_smul]

/- English proof (translation)
Use extensionality with `A`. Establish `h : Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b) + Finsupp.single (Sum.inr j) 1 = Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b + Finsupp.single j 1)`. Use extensionality with `x`. Apply the tactic sequence `rcases x with x | x <;> simp [Finsupp.single_apply]`. Rewrite using `[map_smul, coeff_slice, coeff_slice, MvPowerSeries.coeff_pderiv, h, smul_eq_mul, mul_comm]`.

Simplify using the standard rewrite rules.
-/
theorem slice_pderiv (b : κ' →₀ ℕ) (g : MvPowerSeries (κ ⊕ κ') C) (j : κ') :
    slice b (MvPowerSeries.pderiv C (Sum.inr j) g) = ((b j : C) + 1) • slice (b + Finsupp.single j 1) g := by
  classical
  ext A
  have h : Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b) + Finsupp.single (Sum.inr j) 1 =
      Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b + Finsupp.single j 1) := by
    ext x
    rcases x with x | x <;> simp [Finsupp.single_apply]
  rw [map_smul, coeff_slice, coeff_slice, MvPowerSeries.coeff_pderiv, h, smul_eq_mul, mul_comm]
  simp

/- English proof (translation)
Use extensionality with `A`. Establish `h : Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b) - Finsupp.single (Sum.inl i) 1 = Finsupp.sumFinsuppEquivProdFinsupp.symm (A - Finsupp.single i 1, b)`. Use extensionality with `x`. Apply the tactic sequence `rcases x with x | x <;> simp [Finsupp.single_apply]`. Rewrite using `[coeff_slice, MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, h, coeff_slice]`.

Simplify using `[Finsupp.single_le_iff]`.
-/
theorem slice_X_inl_mul (b : κ' →₀ ℕ) (g : MvPowerSeries (κ ⊕ κ') C) (i : κ) :
    slice b (MvPowerSeries.X (Sum.inl i) * g) = MvPowerSeries.X i * slice b g := by
  classical
  ext A
  have h : Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b) - Finsupp.single (Sum.inl i) 1 =
      Finsupp.sumFinsuppEquivProdFinsupp.symm (A - Finsupp.single i 1, b) := by
    ext x
    rcases x with x | x <;> simp [Finsupp.single_apply]
  rw [coeff_slice, MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_monomial_mul, h, coeff_slice]
  simp [Finsupp.single_le_iff]

/- English proof (translation)
Use extensionality with `A`. Rewrite using `[coeff_slice, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]`. Simplify using `[Finsupp.single_le_iff]`.
-/
theorem slice_zero_X_inr_mul (g : MvPowerSeries (κ ⊕ κ') C) (j : κ') :
    slice 0 (MvPowerSeries.X (Sum.inr j) * g) = 0 := by
  classical
  ext A
  rw [coeff_slice, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  simp [Finsupp.single_le_iff]

/- English proof (translation)
Rewrite using `[pair, pair, form_rename]`. Use `congr 2`. Use function extensionality and compare the values at `A`. Establish `h : A.mapDomain Sum.inl = Finsupp.sumFinsuppEquivProdFinsupp.symm (A, (0 : κ' →₀ ℕ))`. Use extensionality with `x`.

Break down `x with x | x` into its components or cases. Rewrite using `[Finsupp.mapDomain_apply Sum.inl_injective]`. Simplify using the standard rewrite rules. Rewrite using `[Finsupp.mapDomain_notin_range _ _ (by simp)]; simp`. Rewrite using `[coeff_slice, ← h, fact, fact, Finsupp.prod_mapDomain_index_inj Sum.inl_injective]`.
-/
theorem pair_rename_inl (F : MvPolynomial κ C) (g : MvPowerSeries (κ ⊕ κ') C) :
    pair (MvPolynomial.rename Sum.inl F) g = pair F (slice 0 g) := by
  rw [pair, pair, form_rename]
  congr 2
  funext A
  have h : A.mapDomain Sum.inl = Finsupp.sumFinsuppEquivProdFinsupp.symm (A, (0 : κ' →₀ ℕ)) := by
    ext x
    rcases x with x | x
    · rw [Finsupp.mapDomain_apply Sum.inl_injective]; simp
    · rw [Finsupp.mapDomain_notin_range _ _ (by simp)]; simp
  rw [coeff_slice, ← h, fact, fact, Finsupp.prod_mapDomain_index_inj Sum.inl_injective]

def mixed (F : MvPolynomial κ C) (H : MvPolynomial (κ ⊕ κ') C) (g : MvPowerSeries (κ ⊕ κ') C) : C :=
  form (fun m => fact C (Finsupp.sumFinsuppEquivProdFinsupp m).2 *
    pair F (MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) *
      slice (Finsupp.sumFinsuppEquivProdFinsupp m).2 g)) H

/- English proof (translation)
Simplify using `only [mixed, slice_add, mul_add, pair_add_right, form_add]`.
-/
theorem mixed_add_right (F : MvPolynomial κ C) (H : MvPolynomial (κ ⊕ κ') C)
    (f g : MvPowerSeries (κ ⊕ κ') C) : mixed F H (f + g) = mixed F H f + mixed F H g := by
  simp only [mixed, slice_add, mul_add, pair_add_right, form_add]

/- English proof (translation)
Simplify using `only [mixed, slice_smul, mul_smul_comm, pair_smul_right, ← form_mul_left]`. Use `congr 2`. Use function extensionality and compare the values at `m`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mixed_smul_right (F : MvPolynomial κ C) (H : MvPolynomial (κ ⊕ κ') C) (c : C)
    (g : MvPowerSeries (κ ⊕ κ') C) : mixed F H (c • g) = c * mixed F H g := by
  simp only [mixed, slice_smul, mul_smul_comm, pair_smul_right, ← form_mul_left]
  congr 2
  funext m
  ring

/- English proof (translation)
Rewrite using `[mixed, mixed, form_mul_X]`. Use `congr 2`. Use function extensionality and compare the values at `m`. Establish `h1 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inr j) 1)).1 = (Finsupp.sumFinsuppEquivProdFinsupp m).1`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Establish `h2 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inr j) 1)).2 = (Finsupp.sumFinsuppEquivProdFinsupp m).2 + Finsupp.single j 1`. Use extensionality with `x`. Simplify using `[Finsupp.single_apply]`. Rewrite using `[h1, h2, slice_pderiv, mul_smul_comm, pair_smul_right, fact_add_single, mul_assoc]`.
-/
theorem mixed_mul_X_inr (F : MvPolynomial κ C) (H : MvPolynomial (κ ⊕ κ') C)
    (g : MvPowerSeries (κ ⊕ κ') C) (j : κ') :
    mixed F (H * MvPolynomial.X (Sum.inr j)) g = mixed F H (MvPowerSeries.pderiv C (Sum.inr j) g) := by
  classical
  rw [mixed, mixed, form_mul_X]
  congr 2
  funext m
  have h1 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inr j) 1)).1 =
      (Finsupp.sumFinsuppEquivProdFinsupp m).1 := by
    ext x; simp
  have h2 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inr j) 1)).2 =
      (Finsupp.sumFinsuppEquivProdFinsupp m).2 + Finsupp.single j 1 := by
    ext x; simp [Finsupp.single_apply]
  rw [h1, h2, slice_pderiv, mul_smul_comm, pair_smul_right, fact_add_single, mul_assoc]

/- English proof (translation)
Rewrite using `[mixed, mixed, form_mul_X]`. Use `congr 2`. Use function extensionality and compare the values at `m`. Establish `h1 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inl i) 1)).1 = (Finsupp.sumFinsuppEquivProdFinsupp m).1 + Finsupp.single i 1`. Use extensionality with `x`.

Simplify using `[Finsupp.single_apply]`. Establish `h2 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inl i) 1)).2 = (Finsupp.sumFinsuppEquivProdFinsupp m).2`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2, slice_X_inl_mul, ← mul_assoc, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]`.
-/
theorem mixed_mul_X_inl (F : MvPolynomial κ C) (H : MvPolynomial (κ ⊕ κ') C)
    (g : MvPowerSeries (κ ⊕ κ') C) (i : κ) :
    mixed F (H * MvPolynomial.X (Sum.inl i)) g = mixed F H (MvPowerSeries.X (Sum.inl i) * g) := by
  classical
  rw [mixed, mixed, form_mul_X]
  congr 2
  funext m
  have h1 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inl i) 1)).1 =
      (Finsupp.sumFinsuppEquivProdFinsupp m).1 + Finsupp.single i 1 := by
    ext x; simp [Finsupp.single_apply]
  have h2 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inl i) 1)).2 =
      (Finsupp.sumFinsuppEquivProdFinsupp m).2 := by
    ext x; simp
  rw [h1, h2, slice_X_inl_mul, ← mul_assoc, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial,
    mul_one]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C c`. Introduce `H g`. Rewrite using `[MvPolynomial.rename_C, MvPolynomial.coe_C, ← MvPowerSeries.smul_eq_C_mul, mixed_smul_right, mul_comm H, MvPolynomial.C_mul', mixed, map_smul, smul_eq_mul, mixed]`. Consider the case `add p q hp hq`.

Introduce `H g`. Rewrite using `[map_add, MvPolynomial.coe_add, add_mul, mixed_add_right, ← hp, ← hq, mul_add, mixed, map_add, mixed, mixed]`. Consider the case `mul_X p i hp`. Introduce `H g`. Rewrite using `[map_mul, MvPolynomial.rename_X, ← mul_assoc, mixed_mul_X_inl, hp, MvPolynomial.coe_mul, MvPolynomial.coe_X, mul_assoc]`.
-/
theorem mixed_mul_rename_inl (F : MvPolynomial κ C) (p : MvPolynomial κ C) :
    ∀ (H : MvPolynomial (κ ⊕ κ') C) (g : MvPowerSeries (κ ⊕ κ') C),
    mixed F (H * MvPolynomial.rename Sum.inl p) g =
      mixed F H (((MvPolynomial.rename Sum.inl p : MvPolynomial (κ ⊕ κ') C) :
        MvPowerSeries (κ ⊕ κ') C) * g) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    intro H g
    rw [MvPolynomial.rename_C, MvPolynomial.coe_C, ← MvPowerSeries.smul_eq_C_mul, mixed_smul_right,
      mul_comm H, MvPolynomial.C_mul', mixed, map_smul, smul_eq_mul, mixed]
  | add p q hp hq =>
    intro H g
    rw [map_add, MvPolynomial.coe_add, add_mul, mixed_add_right, ← hp, ← hq, mul_add, mixed, map_add,
      mixed, mixed]
  | mul_X p i hp =>
    intro H g
    rw [map_mul, MvPolynomial.rename_X, ← mul_assoc, mixed_mul_X_inl, hp, MvPolynomial.coe_mul,
      MvPolynomial.coe_X, mul_assoc]

/- English proof (translation)
Establish `h : Finsupp.sumFinsuppEquivProdFinsupp (0 : κ ⊕ κ' →₀ ℕ) = (0, 0)`. Apply the tactic sequence `ext x <;> simp`. Rewrite using `[mixed, MvPolynomial.one_def, form_monomial, h]`. Simplify using `[fact]`.
-/
theorem mixed_one (F : MvPolynomial κ C) (g : MvPowerSeries (κ ⊕ κ') C) :
    mixed F 1 g = pair F (slice 0 g) := by
  have h : Finsupp.sumFinsuppEquivProdFinsupp (0 : κ ⊕ κ' →₀ ℕ) = (0, 0) := by
    ext x <;> simp
  rw [mixed, MvPolynomial.one_def, form_monomial, h]
  simp [fact]

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on with`. Consider the case `C c`. Introduce `g`. Rewrite using `[MvPolynomial.rename_C, mul_comm, MvPolynomial.C_mul', pair, map_smul, ← pair, pair_rename_inl, h0, MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one, mixed, map_smul, ← mixed, mixed_one]`. Consider the case `add p q hp hq`.

Introduce `g`. Rewrite using `[map_add, mul_add, pair, map_add, ← pair, ← pair, hp, hq, map_add, mixed, mixed, mixed, map_add]`. Consider the case `mul_X p j hp`. Introduce `g`. Rewrite using `[map_mul, MvPolynomial.rename_X, ← mul_assoc, pair_mul_X, Derivation.leibniz, hd, smul_eq_mul, smul_eq_mul, mul_comm g, mul_assoc E, ← mul_add, hp, mixed_add_right, map_mul, MvPolynomial.aeval_X, mul_add, ← mixed_mul_X_inr, ← mixed_mul_rename_inl, add_comm]`.

Simplify using `only [mixed, map_add]`.
-/
theorem pair_eq_mixed (ζ : κ' → MvPolynomial κ C) (F : MvPolynomial κ C)
    (E : MvPowerSeries (κ ⊕ κ') C) (h0 : ∀ g, slice 0 (E * g) = slice 0 g)
    (hd : ∀ j, MvPowerSeries.pderiv C (Sum.inr j) E =
      E * ((MvPolynomial.rename Sum.inl (ζ j) : MvPolynomial (κ ⊕ κ') C) : MvPowerSeries (κ ⊕ κ') C))
    (G : MvPolynomial κ' C) : ∀ g : MvPowerSeries (κ ⊕ κ') C,
    pair (MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G) (E * g) =
      mixed F (MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl (ζ j) +
        MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C)) G) g := by
  induction G using MvPolynomial.induction_on with
  | C c =>
    intro g
    rw [MvPolynomial.rename_C, mul_comm, MvPolynomial.C_mul', pair, map_smul, ← pair, pair_rename_inl, h0,
      MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one, mixed, map_smul, ← mixed, mixed_one]
  | add p q hp hq =>
    intro g
    rw [map_add, mul_add, pair, map_add, ← pair, ← pair, hp, hq, map_add, mixed, mixed, mixed, map_add]
  | mul_X p j hp =>
    intro g
    rw [map_mul, MvPolynomial.rename_X, ← mul_assoc, pair_mul_X, Derivation.leibniz, hd, smul_eq_mul,
      smul_eq_mul, mul_comm g, mul_assoc E, ← mul_add, hp, mixed_add_right, map_mul, MvPolynomial.aeval_X,
      mul_add, ← mixed_mul_X_inr, ← mixed_mul_rename_inl, add_comm]
    simp only [mixed, map_add]

end Two

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : PowerSeries.X ∣ PowerSeries.exp C - 1 := by`. Rewrite using `[PowerSeries.X_dvd_iff]`. Simplify using the standard rewrite rules. Establish `ha : PowerSeries.HasSubst f` using `PowerSeries.HasSubst.of_constantCoeff_zero hf`. Use `⟨PowerSeries.subst f φ, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_add_of_sub_eq' hφ, PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_X ha]`. Use `congr 1`. Rewrite using `[← PowerSeries.coe_substAlgHom ha, map_one]`.
-/
theorem exp_eq_one_add {C : Type} [Field C] [CharZero C] {σ : Type} (f : MvPowerSeries σ C)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    ∃ Y : MvPowerSeries σ C, PowerSeries.subst f (PowerSeries.exp C) = 1 + f * Y := by
  obtain ⟨φ, hφ⟩ : PowerSeries.X ∣ PowerSeries.exp C - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  refine ⟨PowerSeries.subst f φ, ?_⟩
  rw [eq_add_of_sub_eq' hφ, PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_X ha]
  congr 1
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

/- English proof (translation)
Introduce `C _ _ κ κ' _ _ _ _ ζ F G g`. Use `set q : MvPolynomial (κ ⊕ κ') C := ∑ j, MvPolynomial.rename Sum.inl (ζ j) * MvPolynomial.X (Sum.inr j) with hq`. Establish `hq0 : MvPowerSeries.constantCoeff (q : MvPowerSeries (κ ⊕ κ') C) = 0`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe, ← MvPolynomial.constantCoeff_eq, hq]`. Simplify using the standard rewrite rules.

Establish `key` using `pair_eq_mixed ζ F (PowerSeries.subst (q : MvPowerSeries (κ ⊕ κ') C) (PowerSeries.exp C)) (fun g => by`. Take `⟨Y, hY⟩` from `exp_eq_one_add _ hq0`. Establish `hs : ∀ s : Finset κ', slice 0 (((∑ j ∈ s, MvPolynomial.rename Sum.inl (ζ j) * MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C) : MvPowerSeries (κ ⊕ κ') C) * (Y * g)) = 0`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => ext A`. Simplify using `[coeff_slice]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, MvPolynomial.coe_add, add_mul, slice_add, ih, add_zero, mul_comm _ (MvPolynomial.X _), MvPolynomial.coe_mul, MvPolynomial.coe_X, mul_assoc, slice_zero_X_inr_mul]`. Rewrite using `[hY, add_mul, one_mul, slice_add, mul_assoc, hq, hs, add_zero])`.

Use the proof step `(fun j => by`. Rewrite using `[Formalism.G.LogCR.pderiv_psubst hq0, PowerSeries.derivative_exp, MvPowerSeries.pderiv_coe]`. Use `congr 2`. Establish `hz : ∀ i, MvPolynomial.pderiv (Sum.inr j : κ ⊕ κ') (MvPolynomial.rename Sum.inl (ζ i)) = 0` using `fun i => MvPolynomial.pderiv_eq_zero_of_notMem_vars fun h => by`. Take `⟨x, -, hx⟩` from `MvPolynomial.mem_vars_rename _ _ h`.

Conclude with `absurd hx (by simp)`. Simplify using `[hq, hz, MvPolynomial.pderiv_X, Pi.single_apply]) G g`. Simplify using `only [pair, mixed, form_eq_sum, fact] at key`. Simplify using `only [mul_assoc]`. Conclude with `key`.
-/
theorem main :
  (∀ (C : Type) [Field C] [CharZero C] (κ κ' : Type) [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] (ζ : κ' → MvPolynomial κ C) (F : MvPolynomial κ C) (G : MvPolynomial κ' C) (g : MvPowerSeries (κ ⊕ κ') C),
    (∑ A ∈ ((MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G : MvPolynomial (κ ⊕ κ') C)).support, MvPolynomial.coeff A ((MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G : MvPolynomial (κ ⊕ κ') C)) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (PowerSeries.subst (((∑ j, MvPolynomial.rename Sum.inl (ζ j) * MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C) : MvPowerSeries (κ ⊕ κ') C)) (PowerSeries.exp C) * g)) =
    ∑ m ∈ (MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl (ζ j) + MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C)) G).support, MvPolynomial.coeff m (MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl (ζ j) + MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C)) G) * ((Finsupp.sumFinsuppEquivProdFinsupp m).2.prod fun _ e => (e.factorial : C)) *
      (∑ A ∈ (F).support, MvPolynomial.coeff A (F) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) * (show MvPowerSeries κ C from fun A' => MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (A', (Finsupp.sumFinsuppEquivProdFinsupp m).2)) g)))) := by
  intro C _ _ κ κ' _ _ _ _ ζ F G g
  set q : MvPolynomial (κ ⊕ κ') C :=
    ∑ j, MvPolynomial.rename Sum.inl (ζ j) * MvPolynomial.X (Sum.inr j) with hq
  have hq0 : MvPowerSeries.constantCoeff (q : MvPowerSeries (κ ⊕ κ') C) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      ← MvPolynomial.constantCoeff_eq, hq]
    simp
  have key := pair_eq_mixed ζ F (PowerSeries.subst (q : MvPowerSeries (κ ⊕ κ') C) (PowerSeries.exp C))
    (fun g => by
      obtain ⟨Y, hY⟩ := exp_eq_one_add _ hq0
      have hs : ∀ s : Finset κ', slice 0 (((∑ j ∈ s, MvPolynomial.rename Sum.inl (ζ j) *
          MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C) : MvPowerSeries (κ ⊕ κ') C) * (Y * g)) = 0 := by
        intro s
        induction s using Finset.induction_on with
        | empty => ext A; simp [coeff_slice]
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, MvPolynomial.coe_add, add_mul, slice_add, ih, add_zero,
            mul_comm _ (MvPolynomial.X _), MvPolynomial.coe_mul, MvPolynomial.coe_X, mul_assoc,
            slice_zero_X_inr_mul]
      rw [hY, add_mul, one_mul, slice_add, mul_assoc, hq, hs, add_zero])
    (fun j => by
      rw [Formalism.G.LogCR.pderiv_psubst hq0, PowerSeries.derivative_exp, MvPowerSeries.pderiv_coe]
      congr 2
      have hz : ∀ i, MvPolynomial.pderiv (Sum.inr j : κ ⊕ κ') (MvPolynomial.rename Sum.inl (ζ i)) = 0 :=
        fun i => MvPolynomial.pderiv_eq_zero_of_notMem_vars fun h => by
          obtain ⟨x, -, hx⟩ := MvPolynomial.mem_vars_rename _ _ h
          exact absurd hx (by simp)
      simp [hq, hz, MvPolynomial.pderiv_X, Pi.single_apply]) G g
  simp only [pair, mixed, form_eq_sum, fact] at key
  simp only [mul_assoc]
  exact key

end GlobalTheory.OddBlock.ExpShift

end

end

section
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Conclude with `@GlobalTheory.OddBlock.ExpShift.main`.
-/
theorem _root_.GlobalTheory.OddBlock.expShift : (∀ (C : Type) [Field C] [CharZero C] (κ κ' : Type) [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] (ζ : κ' → MvPolynomial κ C) (F : MvPolynomial κ C) (G : MvPolynomial κ' C) (g : MvPowerSeries (κ ⊕ κ') C),
    (∑ A ∈ ((MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G : MvPolynomial (κ ⊕ κ') C)).support, MvPolynomial.coeff A ((MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G : MvPolynomial (κ ⊕ κ') C)) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (PowerSeries.subst (((∑ j, MvPolynomial.rename Sum.inl (ζ j) * MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C) : MvPowerSeries (κ ⊕ κ') C)) (PowerSeries.exp C) * g)) =
    ∑ m ∈ (MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl (ζ j) + MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C)) G).support, MvPolynomial.coeff m (MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl (ζ j) + MvPolynomial.X (Sum.inr j) : MvPolynomial (κ ⊕ κ') C)) G) * ((Finsupp.sumFinsuppEquivProdFinsupp m).2.prod fun _ e => (e.factorial : C)) *
      (∑ A ∈ (F).support, MvPolynomial.coeff A (F) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) * (show MvPowerSeries κ C from fun A' => MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (A', (Finsupp.sumFinsuppEquivProdFinsupp m).2)) g)))) := by
  exact @GlobalTheory.OddBlock.ExpShift.main

end

section
open ReciprocityTheory.PGsh

noncomputable section

namespace GlobalTheory.OddBlock.ExpBinomial

section General

variable {C : Type} [Field C] {κ κ' : Type}

def slice (g : MvPowerSeries (κ ⊕ κ') C) (B : κ' →₀ ℕ) : MvPowerSeries κ C :=
  fun A' => MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (A', B)) g

def actMon (g : MvPowerSeries (κ ⊕ κ') C) (m : κ ⊕ κ' →₀ ℕ) : MvPowerSeries κ C :=
  ((Finsupp.sumFinsuppEquivProdFinsupp m).2.prod fun _ e => (e.factorial : C)) •
    (MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) *
      slice g (Finsupp.sumFinsuppEquivProdFinsupp m).2)

def act (g : MvPowerSeries (κ ⊕ κ') C) : MvPolynomial (κ ⊕ κ') C →ₗ[C] MvPowerSeries κ C :=
  (MvPolynomial.basisMonomials (κ ⊕ κ') C).constr C (actMon g)

/- English proof (translation)
Establish `h : (MvPolynomial.monomial m c : MvPolynomial (κ ⊕ κ') C) = c • MvPolynomial.basisMonomials (κ ⊕ κ') C m`. Simplify using `[MvPolynomial.smul_monomial]`. Rewrite using `[h, map_smul, act, Module.Basis.constr_basis]`.
-/
theorem act_monomial (g : MvPowerSeries (κ ⊕ κ') C) (m : κ ⊕ κ' →₀ ℕ) (c : C) :
    act g (MvPolynomial.monomial m c) = c • actMon g m := by
  have h : (MvPolynomial.monomial m c : MvPolynomial (κ ⊕ κ') C) =
      c • MvPolynomial.basisMonomials (κ ⊕ κ') C m := by
    simp [MvPolynomial.smul_monomial]
  rw [h, map_smul, act, Module.Basis.constr_basis]

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Simplify using `only [map_sum, act_monomial]`.
-/
theorem act_eq (g : MvPowerSeries (κ ⊕ κ') C) (P : MvPolynomial (κ ⊕ κ') C) :
    act g P = ∑ m ∈ P.support, MvPolynomial.coeff m P • actMon g m := by
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, act_monomial]

/- English proof (translation)
Proceed by induction on `R using MvPolynomial.induction_on' with`. Consider the case `add p q hp hq => simp [add_mul, hp, hq]`. Consider the case `monomial a c`. Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [mul_add, map_add, hp, hq]`.

Consider the case `monomial m d`. Establish `h1 : (Finsupp.sumFinsuppEquivProdFinsupp (a.mapDomain Sum.inl + m)).1 = a + (Finsupp.sumFinsuppEquivProdFinsupp m).1`. Use extensionality with `x`. Simplify using `[Finsupp.mapDomain_apply Sum.inl_injective]`. Establish `h2 : (Finsupp.sumFinsuppEquivProdFinsupp (a.mapDomain Sum.inl + m)).2 = (Finsupp.sumFinsuppEquivProdFinsupp m).2`.

Use extensionality with `x`. Simplify using `[Finsupp.mapDomain_notin_range]`. Rewrite using `[MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, act_monomial, act_monomial, actMon, actMon, h1, h2, MvPolynomial.coe_monomial]`. Establish `h3 : (MvPowerSeries.monomial a c : MvPowerSeries κ C) = c • MvPowerSeries.monomial a (1 : C)`. Rewrite using `[← map_smul]`.

Simplify using the standard rewrite rules. Establish `h4 : (MvPowerSeries.monomial (a + (Finsupp.sumFinsuppEquivProdFinsupp m).1) (1 : C)) = MvPowerSeries.monomial a (1 : C) * MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C)`. Rewrite using `[MvPowerSeries.monomial_mul_monomial, one_mul]`. Rewrite using `[h3, h4]`. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem act_mul (g : MvPowerSeries (κ ⊕ κ') C) (R : MvPolynomial κ C)
    (P : MvPolynomial (κ ⊕ κ') C) :
    act g (MvPolynomial.rename Sum.inl R * P) = (R : MvPowerSeries κ C) * act g P := by
  induction R using MvPolynomial.induction_on' with
  | add p q hp hq => simp [add_mul, hp, hq]
  | monomial a c =>
    induction P using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]
    | monomial m d =>
      have h1 : (Finsupp.sumFinsuppEquivProdFinsupp (a.mapDomain Sum.inl + m)).1 =
          a + (Finsupp.sumFinsuppEquivProdFinsupp m).1 := by
        ext x
        simp [Finsupp.mapDomain_apply Sum.inl_injective]
      have h2 : (Finsupp.sumFinsuppEquivProdFinsupp (a.mapDomain Sum.inl + m)).2 =
          (Finsupp.sumFinsuppEquivProdFinsupp m).2 := by
        ext x
        simp [Finsupp.mapDomain_notin_range]
      rw [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, act_monomial, act_monomial,
        actMon, actMon, h1, h2, MvPolynomial.coe_monomial]
      have h3 : (MvPowerSeries.monomial a c : MvPowerSeries κ C) =
          c • MvPowerSeries.monomial a (1 : C) := by
        rw [← map_smul]; simp
      have h4 : (MvPowerSeries.monomial (a + (Finsupp.sumFinsuppEquivProdFinsupp m).1) (1 : C)) =
          MvPowerSeries.monomial a (1 : C) *
            MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) := by
        rw [MvPowerSeries.monomial_mul_monomial, one_mul]
      rw [h3, h4]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      congr 1
      ring

def pair (F : MvPolynomial κ C) : MvPowerSeries κ C →ₗ[C] C :=
  ∑ A ∈ F.support, (MvPolynomial.coeff A F * (A.prod fun _ e => (e.factorial : C))) •
    MvPowerSeries.coeff A

/- English proof (translation)
Simplify using `[pair, LinearMap.sum_apply]`.
-/
theorem pair_apply (F : MvPolynomial κ C) (S : MvPowerSeries κ C) :
    pair F S = ∑ A ∈ F.support, MvPolynomial.coeff A F * (A.prod fun _ e => (e.factorial : C)) *
      MvPowerSeries.coeff A S := by
  simp [pair, LinearMap.sum_apply]

variable [Fintype κ] [DecidableEq κ]

def homPart (N : ℕ) (S : MvPowerSeries κ C) : MvPolynomial κ C :=
  ∑ A ∈ Finset.finsuppAntidiag Finset.univ N, MvPolynomial.monomial A (MvPowerSeries.coeff A S)

/- English proof (translation)
Simplify using `[homPart, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.mem_finsuppAntidiag]`.
-/
theorem coeff_homPart (N : ℕ) (S : MvPowerSeries κ C) (A : κ →₀ ℕ) :
    MvPolynomial.coeff A (homPart N S) =
      if ∑ q, A q = N then MvPowerSeries.coeff A S else 0 := by
  simp [homPart, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.mem_finsuppAntidiag]

omit [DecidableEq κ] in
/- English proof (translation)
Rewrite using `[← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression.
-/
theorem weight_one (A : κ →₀ ℕ) : Finsupp.weight (1 : κ → ℕ) A = ∑ q, A q := by
  rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]; rfl

omit [DecidableEq κ] in
/- English proof (translation)
Use `hF hA` as an intermediate fact. Rewrite using `[← this, weight_one]`.
-/
theorem sum_eq_of_isHomogeneous {F : MvPolynomial κ C} {N : ℕ} (hF : F.IsHomogeneous N)
    {A : κ →₀ ℕ} (hA : MvPolynomial.coeff A F ≠ 0) : ∑ q, A q = N := by
  have := hF hA
  rw [← this, weight_one]

/- English proof (translation)
Introduce `A hA`. Rewrite `hA` using `[coeff_homPart]`. Rewrite using `[weight_one]`. Assume the negation of the conclusion as `h`. Conclude with `hA (if_neg h)`.
-/
theorem homPart_isHomogeneous (N : ℕ) (S : MvPowerSeries κ C) :
    (homPart N S).IsHomogeneous N := by
  intro A hA
  rw [coeff_homPart] at hA
  rw [weight_one]
  by_contra h
  exact hA (if_neg h)

/- English proof (translation)
Rewrite using `[pair_apply]`. Use `Finset.sum_congr rfl fun A hA => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hA'` using `sum_eq_of_isHomogeneous hF (MvPolynomial.mem_support_iff.mp hA)`. Rewrite using `[MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]`.

Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_coe]`. Distinguish the cases in `h : MvPolynomial.coeff x.1 R = 0`. Simplify using `[h]`. Establish `h1` using `sum_eq_of_isHomogeneous hR h`.

Establish `h2 : x.1 + x.2 = A` using `by simpa using hx`. Rewrite `hA'` using `[← h2]`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib] at hA'`. Rewrite using `[coeff_homPart, if_pos (by omega)]`.
-/
theorem pair_mul {F R : MvPolynomial κ C} {d N : ℕ} (hF : F.IsHomogeneous (d + N))
    (hR : R.IsHomogeneous d) (S : MvPowerSeries κ C) :
    pair F ((R : MvPowerSeries κ C) * S) =
      ∑ A ∈ F.support, MvPolynomial.coeff A F * (A.prod fun _ e => (e.factorial : C)) *
        MvPolynomial.coeff A (R * homPart N S) := by
  rw [pair_apply]
  refine Finset.sum_congr rfl fun A hA => ?_
  congr 1
  have hA' := sum_eq_of_isHomogeneous hF (MvPolynomial.mem_support_iff.mp hA)
  rw [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [MvPolynomial.coeff_coe]
  by_cases h : MvPolynomial.coeff x.1 R = 0
  · simp [h]
  · have h1 := sum_eq_of_isHomogeneous hR h
    have h2 : x.1 + x.2 = A := by simpa using hx
    rw [← h2] at hA'
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hA'
    rw [coeff_homPart, if_pos (by omega)]

end General

/- English proof (translation)
Rewrite using `[cayDet, Matrix.det_apply]`. Use `MvPolynomial.IsHomogeneous.sum _ _ _ fun g _ => ?_` and prove the remaining obligations. Establish `h : (∏ i, (MvPolynomial.X (g i, i) : MvPolynomial (Fin n × Fin n) C)).IsHomogeneous n`. Use `MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n)) (fun i => (MvPolynomial.X (g i, i) : MvPolynomial (Fin n × Fin n) C)) (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X _ _)` as an intermediate fact. Simplify using `using this`.

Break down `Int.units_eq_one_or (Equiv.Perm.sign g) with e | e` into its components or cases. Simplify `h` using `[e]`. Simplify `h.neg` using `[e]`.
-/
theorem cayDet_isHomogeneous (n : ℕ) (C : Type) [CommRing C] : (cayDet n C).IsHomogeneous n := by
  rw [cayDet, Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun g _ => ?_
  have h : (∏ i, (MvPolynomial.X (g i, i) : MvPolynomial (Fin n × Fin n) C)).IsHomogeneous n := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
      (fun i => (MvPolynomial.X (g i, i) : MvPolynomial (Fin n × Fin n) C)) (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X _ _)
    simpa using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with e | e
  · simpa [e] using h
  · simpa [e] using h.neg

def psi (l L E n : ℕ) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℤ :=
  (Matrix.of fun b c : Fin n => (MvPolynomial.X (Sum.inl (b, c)) ^ L -
    MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) :
      MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℤ)).det -
      MvPolynomial.rename Sum.inl (cayDet n ℤ) ^ L

/- English proof (translation)
Rewrite using `[psi, map_sub, map_pow (MvPolynomial.map _), MvPolynomial.map_rename, cayDet_map, map_pow (MvPolynomial.rename _), sub_add_cancel, cayDet, AlgHom.map_det, RingHom.map_det, map_pow]`. Use `Matrix.det_smul (R := MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C) ((MvPolynomial.map (Int.castRingHom C)).mapMatrix (Matrix.of fun b c : Fin n => (MvPolynomial.X (Sum.inl (b, c)) ^ L - MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial ((Fin n × …` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Rewrite using `[← this]`. Use `congr 1`.

Use `ext1 b c`. Establish `h : (MvPolynomial.C (((l : C) ^ E)⁻¹) * MvPolynomial.C ((l : C) ^ E) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hl), map_one]`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply, MvPolynomial.aeval_X, map_mul, map_pow, MvPolynomial.rename_C, MvPolynomial.rename_X, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.of_apply, map_sub, MvPolynomial.map_X, MvPolynomial.map_C, smul_eq_ …`. Take the linear combination `(-MvPolynomial.X (Sum.inr (b, c))) * h`.
-/
theorem aeval_cayDet (C : Type) [Field C] (l L E n : ℕ) (hl : (l : C) ≠ 0) :
    MvPolynomial.aeval (fun j => (MvPolynomial.rename Sum.inl
      (MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X j ^ L : MvPolynomial (Fin n × Fin n) C) +
        MvPolynomial.X (Sum.inr j) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C))
      (cayDet n C) =
    MvPolynomial.C ((-((l : C) ^ E)⁻¹) ^ n) *
      (MvPolynomial.map (Int.castRingHom C) (psi l L E n) +
        MvPolynomial.rename Sum.inl (cayDet n C ^ L)) := by
  rw [psi, map_sub, map_pow (MvPolynomial.map _), MvPolynomial.map_rename, cayDet_map,
    map_pow (MvPolynomial.rename _), sub_add_cancel, cayDet, AlgHom.map_det, RingHom.map_det,
    map_pow]
  have := Matrix.det_smul (R := MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C)
    ((MvPolynomial.map (Int.castRingHom C)).mapMatrix
      (Matrix.of fun b c : Fin n => (MvPolynomial.X (Sum.inl (b, c)) ^ L -
    MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) :
      MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℤ))) (MvPolynomial.C (-((l : C) ^ E)⁻¹))
  rw [Fintype.card_fin] at this
  rw [← this]
  congr 1
  ext1 b c
  have h : (MvPolynomial.C (((l : C) ^ E)⁻¹) * MvPolynomial.C ((l : C) ^ E) :
      MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hl), map_one]
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply,
    MvPolynomial.aeval_X, map_mul, map_pow, MvPolynomial.rename_C, MvPolynomial.rename_X,
    Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.of_apply, map_sub, MvPolynomial.map_X,
    MvPolynomial.map_C, smul_eq_mul, map_neg, map_natCast] at h ⊢
  linear_combination (-MvPolynomial.X (Sum.inr (b, c))) * h

open ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps in
/- English proof (translation)
Take `⟨w, rfl⟩` from `h`. Use `push_cast`. Rewrite using `[v.map_mul, v.map_pow, hv, nsmul_one_coe]`. Conclude with `le_add_of_nonneg_right (intCast_nonneg v w)`.
-/
theorem le_v_of_dvd {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {l : ℕ}
    (hv : v (l : C) = 1) {k : ℕ} {z : ℤ} (h : (l : ℤ) ^ k ∣ z) :
    ((k : ℝ) : WithTop ℝ) ≤ v (z : C) := by
  obtain ⟨w, rfl⟩ := h
  push_cast
  rw [v.map_mul, v.map_pow, hv, nsmul_one_coe]
  exact le_add_of_nonneg_right (intCast_nonneg v w)

open ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps in
/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (by simp), ← Nat.cast_prod, natCast_eq_factorization v hl hv (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _), Nat.factorization_def _ hl]`.
-/
theorem v_prod_factorial {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {l : ℕ}
    (hl : l.Prime) (hv : v (l : C) = 1) {κ : Type} [Fintype κ] (B : κ →₀ ℕ) :
    v (B.prod fun _ e => (e.factorial : C)) =
      ((padicValNat l (∏ j, (B j).factorial) : ℝ) : WithTop ℝ) := by
  rw [Finsupp.prod_fintype _ _ (by simp), ← Nat.cast_prod,
    natCast_eq_factorization v hl hv (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _),
    Nat.factorization_def _ hl]

/- English proof (translation)
Establish `hl' : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hL' : (1 : ℝ) ≤ L` using `by exact_mod_cast hL`. Establish `hns : (1 : ℝ) ≤ (n : ℝ) * s` using `by exact_mod_cast Nat.mul_le_mul hn hs`. Establish `hlog : 0 ≤ Real.logb l (n * s)` using `Real.logb_nonneg (by linarith) hns`. Establish `hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2` using `by positivity`.

Establish `hs0 : (0 : ℝ) ≤ s` using `by positivity`. Break down `Nat.eq_zero_or_pos K with rfl | hK1` into its components or cases. Use `mul_nonneg hn2 (show 0 ≤ Real.logb l (n * s) + 1 by linarith)` as an intermediate fact. Simplify using `only [mul_zero, Nat.sub_zero, zero_add, Nat.cast_zero, add_zero, sub_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hp1` using `hp hK1`. Establish `hK' : (1 : ℝ) ≤ K` using `by exact_mod_cast hK1`. Establish `hlog2 : Real.logb l K ≤ Real.logb l (n * s)` using `Real.logb_le_logb_of_le (by linarith) (by linarith) (by exact_mod_cast hK)`. Establish `h3` using `mul_le_mul_of_nonneg_left hlog2 hn2`. Establish `h4 : (s : ℝ) ≤ ((s - K : ℕ) : ℝ) + K` using `by exact_mod_cast (by omega : s ≤ s - K + K)`.

Establish `h5 : (0 : ℝ) ≤ ((s - K : ℕ) : ℝ)` using `by positivity`. Establish `h1 : (l : ℝ) - 1 ≠ 0` using `by linarith`. Establish `h2 : (l : ℝ) + 1 ≠ 0` using `by linarith`. Establish `h6 : (1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (L : ℝ))) * (L * K) + (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (L : ℝ))) * K = E * K + K / (l - 1) - K / 8 - K / (8 * L)`. Rewrite using `[hE, show (l : ℝ) ^ 2 - 1 = (l - 1) * (l + 1) by ring]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h7 : (0 : ℝ) ≤ K / (8 * L)` using `by positivity`. Rewrite using `[h6, Nat.cast_add, Nat.cast_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem real_bound {l : ℕ} (hl : 5 ≤ l) {L E n s K : ℕ} (hL : 1 ≤ L)
    (hE : (E : ℝ) = 1 + ((L : ℝ) - l) / ((l : ℝ) ^ 2 - 1)) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hK : K ≤ n * s) (p : ℝ) (hp0 : 0 ≤ p)
    (hp : 1 ≤ K → (K : ℝ) / (l - 1) - (n : ℝ) ^ 2 * (Real.logb l K + 1) ≤ p) :
    (s : ℝ) / 8 - (n : ℝ) ^ 2 * (Real.logb l (n * s) + 1) ≤
      ((E * K + (s - K) : ℕ) : ℝ) + (p + (0 - ((1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (L : ℝ))) * (L * K) +
        (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (L : ℝ))) * K))) := by
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hns : (1 : ℝ) ≤ (n : ℝ) * s := by exact_mod_cast Nat.mul_le_mul hn hs
  have hlog : 0 ≤ Real.logb l (n * s) := Real.logb_nonneg (by linarith) hns
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hs0 : (0 : ℝ) ≤ s := by positivity
  rcases Nat.eq_zero_or_pos K with rfl | hK1
  · have := mul_nonneg hn2 (show 0 ≤ Real.logb l (n * s) + 1 by linarith)
    simp only [mul_zero, Nat.sub_zero, zero_add, Nat.cast_zero, add_zero, sub_zero]
    linarith
  · have hp1 := hp hK1
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hlog2 : Real.logb l K ≤ Real.logb l (n * s) :=
      Real.logb_le_logb_of_le (by linarith) (by linarith) (by exact_mod_cast hK)
    have h3 := mul_le_mul_of_nonneg_left hlog2 hn2
    have h4 : (s : ℝ) ≤ ((s - K : ℕ) : ℝ) + K := by exact_mod_cast (by omega : s ≤ s - K + K)
    have h5 : (0 : ℝ) ≤ ((s - K : ℕ) : ℝ) := by positivity
    have h1 : (l : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (l : ℝ) + 1 ≠ 0 := by linarith
    have h6 : (1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (L : ℝ))) * (L * K) +
        (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (L : ℝ))) * K =
        E * K + K / (l - 1) - K / 8 - K / (8 * L) := by
      rw [hE, show (l : ℝ) ^ 2 - 1 = (l - 1) * (l + 1) by ring]
      field_simp
      ring
    have h7 : (0 : ℝ) ≤ K / (8 * L) := by positivity
    rw [h6, Nat.cast_add, Nat.cast_mul]
    linarith

/- English proof (translation)
Introduce `C _ _ v l hl hv h5 i E n hi hE h₁ hw hz`. Establish `hi1 : 1 ≤ i` using `hi.pos`. Establish `hlC : (l : C) ≠ 0` using `Nat.cast_ne_zero.mpr hl.ne_zero`. Establish `h0 : MvPowerSeries.constantCoeff h₁ = 0`. Assume the negation of the conclusion as `h`.

Take `⟨q, hq⟩` from `hz 0 (by simpa using h)`. Simplify using `at hq`. Establish `hg` using `GlobalTheory.T.weight_nonneg_exp_of_weight_ge_inv_prime_sub_one C v l hl hv _ _ h₁ h0 hw`. Establish `hg0` using `ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp h0`. Use `set g := PowerSeries.subst h₁ (PowerSeries.exp C) with hgdef`.

Use `set ψ := MvPolynomial.map (Int.castRingHom C) (psi l (l ^ i) E n) with hψ`. Use `⟨fun s => homPart (n * (l ^ i * s)) (act g (ψ ^ s)), ?_, fun s => homPart_isHomogeneous _ _, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `A`. Establish `h1 : (1 : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C) = MvPolynomial.monomial 0 1` using `rfl`. Simplify using `only [pow_zero, mul_zero]`.

Rewrite using `[coeff_homPart, h1, act_monomial, MvPolynomial.coeff_one]`. Distinguish the cases in `hA : A = 0`. Substitute `hA` using the available equality. Establish `e : (Finsupp.sumFinsuppEquivProdFinsupp (0 : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ)) = (0, 0)`. Apply the tactic sequence `ext <;> simp`.

Establish `e' : (Finsupp.sumFinsuppEquivProdFinsupp.symm (0, 0) : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) = 0`. Rewrite using `[← e, Equiv.symm_apply_apply]`. Establish `e2 : MvPowerSeries.coeff 0 (slice g 0) = 1`. Express the relevant statement in the definitionally equal form `MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (0, 0)) g = 1`. Rewrite using `[e']`.

Simplify using `using hg0`. Simplify using `only [actMon, e]`. Simplify using `using e2`. Rewrite using `[if_neg (Ne.symm hA), if_neg]`. Introduce `h`.

Apply `hA` to reduce the goal to its premises. Use extensionality with `q`. Conclude with `(Finset.sum_eq_zero_iff.mp h) q (Finset.mem_univ _)`. Introduce `s hs hn A`. Rewrite using `[coeff_homPart]`.

Use `split_ifs with hA`. Use `swap`. Simplify using the standard rewrite rules. Rewrite using `[act_eq, map_sum]`. Use `v.map_le_sum fun m hm => ?_` and prove the remaining obligations.

Rewrite `hm`, the goal using `[hψ, ← map_pow]`. Take `⟨a1, a2, a3⟩` from `GlobalTheory.T.det_frobenius_sub_pow_support_bounds l i E n s hl hi1 (psi l (l ^ i) E n) rfl m (MvPolynomial.support_map_subset _ _ hm)`. Rewrite using `[actMon, LinearMap.map_smul, LinearMap.map_smul, MvPowerSeries.coeff_monomial_mul, smul_eq_mul, smul_eq_mul]`. Use `split_ifs with hle`. Use `swap`.

Simplify using the standard rewrite rules. Rewrite using `[one_mul, v.map_mul, v.map_mul, MvPolynomial.coeff_map, v_prod_factorial v hl hv]`. Establish `b1` using `le_v_of_dvd v hv a3`. Establish `b2` using `hg (Finsupp.sumFinsuppEquivProdFinsupp.symm (A - (Finsupp.sumFinsuppEquivProdFinsupp m).1, (Finsupp.sumFinsuppEquivProdFinsupp m).2))`. Use `le_trans ?_ (add_le_add b1 (add_le_add le_rfl b2))` and prove the remaining obligations.

Rewrite using `[← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]`. Establish `c1 : ∑ q, (A - (Finsupp.sumFinsuppEquivProdFinsupp m).1) q = l ^ i * ∑ q, m (Sum.inr q)`. Establish `: ∑ q, (A - (Finsupp.sumFinsuppEquivProdFinsupp m).1) q + ∑ q, m (Sum.inl q) = ∑ q, A q`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Use `hle q` as an intermediate fact. Simplify using `only [Finsupp.fst_sumFinsuppEquivProdFinsupp, Finsupp.tsub_apply] at this ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite `a2` using `[mul_assoc]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Finsupp.sumFinsuppEquivProdFinsupp_symm_inl, Finsupp.sumFinsuppEquivProdFinsupp_symm_inr, ← Finset.mul_sum, ← Nat.cast_sum, c1, Finsupp.snd_sumFinsuppEquivProdFinsupp]`. Use `real_bound (L := l ^ i) (E := E) h5 (Nat.one_le_pow _ _ hl.pos) (by push_cast; exact hE) hs hn a1 (padicValNat l (∏ j, (m (Sum.inr j)).factorial)) (by positivity) (fun hK => by` as an intermediate fact. Use `(GlobalTheory.T.legendre_bounds_factorial_multiIndex_capelli l hl).2.1 (Fin n × Fin n) (fun j => m (Sum.inr j)) hK` as an intermediate fact. Simplify `this)` using `[sq]`.

Simplify `this` using `only [Nat.cast_mul, Nat.cast_pow]`. Introduce `y`. Establish `ha : MvPowerSeries.constantCoeff (((∑ q : Fin n × Fin n, MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X (Sum.inl q) ^ (l ^ i) * MvPolynomial.X (Sum.inr q) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C)) : MvPowerSeries ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C) = 0`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe, ← MvPolynomial.constantCoeff_eq]`. Simplify using the standard rewrite rules.

Establish `key` using `GlobalTheory.OddBlock.expShift C (Fin n × Fin n) (Fin n × Fin n) (fun j => MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X j ^ (l ^ i)) (cayDet n C ^ (l ^ i * y)) (cayDet n C ^ y) g`. Rewrite `key` using `[map_pow (MvPolynomial.aeval _), aeval_cayDet C l (l ^ i) E n hlC, ← hψ]`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ha h0, ← hgdef]`. Simplify using `only [map_mul (MvPolynomial.rename Sum.inl), map_pow (MvPolynomial.rename Sum.inl), map_pow (MvPolynomial.rename Sum.inr), MvPolynomial.rename_C, MvPolynomial.rename_X] at key`. Rewrite using `[key, ← map_pow (MvPolynomial.rename Sum.inl)]`.

Generalize the expression as in `hP : (MvPolynomial.C ((-((l : C) ^ E)⁻¹) ^ n) * (ψ + MvPolynomial.rename Sum.inl (cayDet n C ^ l ^ i))) ^ y = P`. Use `Eq.trans (b := pair (cayDet n C ^ (l ^ i * y)) (act g P)) ?_ ?_` and prove the remaining obligations. Rewrite using `[act_eq, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[actMon, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, pair_apply]`.

Both sides reduce to the same expression. Rewrite using `[← hP, mul_pow, ← map_pow, ← pow_mul, MvPolynomial.C_mul', map_smul, map_smul, smul_eq_mul, add_pow, map_sum, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hsy : s ≤ y` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)`.

Rewrite using `[← map_pow (MvPolynomial.rename Sum.inl), ← pow_mul, Nat.mul_sub, mul_comm _ ((y.choose s : ℕ) : MvPolynomial _ C), ← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul, mul_comm (ψ ^ s), act_mul]`. Use `congr 1`. Use `pair_mul (d := n * (l ^ i * y - l ^ i * s)) ?_ ((cayDet_isHomogeneous n C).pow _) _` and prove the remaining obligations. Use `(cayDet_isHomogeneous n C).pow (l ^ i * y)` as an intermediate fact. Rewrite using `[← mul_add, Nat.sub_add_cancel (Nat.mul_le_mul_left _ hsy)]` and apply the resulting hypothesis.
-/
theorem main :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 5 ≤ l → ∀ (i E n₀ : ℕ), Odd i → (E : ℝ) = 1 + ((l : ℝ) ^ i - l) / ((l : ℝ) ^ 2 - 1) → ∀ h₁ : MvPowerSeries ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C,
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h₁))) → (∀ α, MvPowerSeries.coeff α h₁ ≠ 0 → ∃ q, α (Sum.inr q) ≠ 0) →
    ∃ Q : ℕ → MvPolynomial (Fin n₀ × Fin n₀) C, Q 0 = 1 ∧ (∀ s, (Q s).IsHomogeneous (n₀ * (l ^ i * s))) ∧
      (∀ s : ℕ, 1 ≤ s → 1 ≤ n₀ → ∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.coeff A (Q s))) ∧
      ∀ y : ℕ, (∑ A ∈ ((MvPolynomial.rename Sum.inl (cayDet n₀ C) ^ (l ^ i * y) * MvPolynomial.rename Sum.inr (cayDet n₀ C) ^ y : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C)).support, MvPolynomial.coeff A ((MvPolynomial.rename Sum.inl (cayDet n₀ C) ^ (l ^ i * y) * MvPolynomial.rename Sum.inr (cayDet n₀ C) ^ y : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C)) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (PowerSeries.subst (((∑ q : Fin n₀ × Fin n₀, MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X (Sum.inl q) ^ (l ^ i) * MvPolynomial.X (Sum.inr q) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C) : MvPowerSeries ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C) + h₁) (PowerSeries.exp C))) = (-((l : C) ^ E)⁻¹) ^ (n₀ * y) * ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * (∑ A ∈ (cayDet n₀ C ^ (l ^ i * y)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * y)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * y - l ^ i * s) * Q s))) := by
  intro C _ _ v l hl hv h5 i E n hi hE h₁ hw hz
  have hi1 : 1 ≤ i := hi.pos
  have hlC : (l : C) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have h0 : MvPowerSeries.constantCoeff h₁ = 0 := by
    by_contra h
    obtain ⟨q, hq⟩ := hz 0 (by simpa using h)
    simp at hq
  have hg := GlobalTheory.T.weight_nonneg_exp_of_weight_ge_inv_prime_sub_one C v l hl hv _ _ h₁ h0 hw
  have hg0 := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp h0
  set g := PowerSeries.subst h₁ (PowerSeries.exp C) with hgdef
  set ψ := MvPolynomial.map (Int.castRingHom C) (psi l (l ^ i) E n) with hψ
  refine ⟨fun s => homPart (n * (l ^ i * s)) (act g (ψ ^ s)), ?_,
    fun s => homPart_isHomogeneous _ _, ?_, ?_⟩
  · ext A
    have h1 : (1 : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C) =
        MvPolynomial.monomial 0 1 := rfl
    simp only [pow_zero, mul_zero]
    rw [coeff_homPart, h1, act_monomial, MvPolynomial.coeff_one]
    by_cases hA : A = 0
    · subst hA
      have e : (Finsupp.sumFinsuppEquivProdFinsupp
          (0 : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ)) = (0, 0) := by
        ext <;> simp
      have e' : (Finsupp.sumFinsuppEquivProdFinsupp.symm (0, 0) :
          (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) = 0 := by
        rw [← e, Equiv.symm_apply_apply]
      have e2 : MvPowerSeries.coeff 0 (slice g 0) = 1 := by
        change MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (0, 0)) g = 1
        rw [e']; simpa using hg0
      simp only [actMon, e]
      simpa using e2
    · rw [if_neg (Ne.symm hA), if_neg]
      intro h
      apply hA
      ext q
      exact (Finset.sum_eq_zero_iff.mp h) q (Finset.mem_univ _)
  · intro s hs hn A
    rw [coeff_homPart]
    split_ifs with hA
    swap
    · simp
    rw [act_eq, map_sum]
    refine v.map_le_sum fun m hm => ?_
    rw [hψ, ← map_pow] at hm ⊢
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.det_frobenius_sub_pow_support_bounds l i E n s hl hi1 (psi l (l ^ i) E n) rfl m
      (MvPolynomial.support_map_subset _ _ hm)
    rw [actMon, LinearMap.map_smul, LinearMap.map_smul, MvPowerSeries.coeff_monomial_mul, smul_eq_mul, smul_eq_mul]
    split_ifs with hle
    swap
    · simp
    rw [one_mul, v.map_mul, v.map_mul, MvPolynomial.coeff_map, v_prod_factorial v hl hv]
    have b1 := le_v_of_dvd v hv a3
    have b2 := hg (Finsupp.sumFinsuppEquivProdFinsupp.symm
      (A - (Finsupp.sumFinsuppEquivProdFinsupp m).1, (Finsupp.sumFinsuppEquivProdFinsupp m).2))
    refine le_trans ?_ (add_le_add b1 (add_le_add le_rfl b2))
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
    have c1 : ∑ q, (A - (Finsupp.sumFinsuppEquivProdFinsupp m).1) q =
        l ^ i * ∑ q, m (Sum.inr q) := by
      have : ∑ q, (A - (Finsupp.sumFinsuppEquivProdFinsupp m).1) q + ∑ q, m (Sum.inl q) =
          ∑ q, A q := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        have := hle q
        simp only [Finsupp.fst_sumFinsuppEquivProdFinsupp, Finsupp.tsub_apply] at this ⊢
        omega
      rw [mul_assoc] at a2
      omega
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finsupp.sumFinsuppEquivProdFinsupp_symm_inl,
      Finsupp.sumFinsuppEquivProdFinsupp_symm_inr, ← Finset.mul_sum, ← Nat.cast_sum, c1,
      Finsupp.snd_sumFinsuppEquivProdFinsupp]
    have := real_bound (L := l ^ i) (E := E) h5 (Nat.one_le_pow _ _ hl.pos) (by push_cast; exact hE)
      hs hn a1 (padicValNat l (∏ j, (m (Sum.inr j)).factorial)) (by positivity) (fun hK => by
        have := (GlobalTheory.T.legendre_bounds_factorial_multiIndex_capelli l hl).2.1 (Fin n × Fin n) (fun j => m (Sum.inr j)) hK
        simpa [sq] using this)
    simpa only [Nat.cast_mul, Nat.cast_pow] using this
  · intro y
    have ha : MvPowerSeries.constantCoeff (((∑ q : Fin n × Fin n,
        MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X (Sum.inl q) ^ (l ^ i) *
          MvPolynomial.X (Sum.inr q) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C)) :
        MvPowerSeries ((Fin n × Fin n) ⊕ (Fin n × Fin n)) C) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
        ← MvPolynomial.constantCoeff_eq]
      simp
    have key := GlobalTheory.OddBlock.expShift C (Fin n × Fin n) (Fin n × Fin n)
      (fun j => MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X j ^ (l ^ i))
      (cayDet n C ^ (l ^ i * y)) (cayDet n C ^ y) g
    rw [map_pow (MvPolynomial.aeval _), aeval_cayDet C l (l ^ i) E n hlC, ← hψ] at key
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ha h0, ← hgdef]
    simp only [map_mul (MvPolynomial.rename Sum.inl), map_pow (MvPolynomial.rename Sum.inl),
      map_pow (MvPolynomial.rename Sum.inr), MvPolynomial.rename_C, MvPolynomial.rename_X] at key
    rw [key, ← map_pow (MvPolynomial.rename Sum.inl)]
    generalize hP : (MvPolynomial.C ((-((l : C) ^ E)⁻¹) ^ n) *
      (ψ + MvPolynomial.rename Sum.inl (cayDet n C ^ l ^ i))) ^ y = P
    refine Eq.trans (b := pair (cayDet n C ^ (l ^ i * y)) (act g P)) ?_ ?_
    · rw [act_eq, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [actMon, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        pair_apply]
      rfl
    rw [← hP, mul_pow, ← map_pow, ← pow_mul, MvPolynomial.C_mul', map_smul, map_smul, smul_eq_mul,
      add_pow, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsy : s ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [← map_pow (MvPolynomial.rename Sum.inl), ← pow_mul, Nat.mul_sub, mul_comm _ ((y.choose s : ℕ) : MvPolynomial _ C),
      ← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul, mul_comm (ψ ^ s), act_mul]
    congr 1
    refine pair_mul (d := n * (l ^ i * y - l ^ i * s)) ?_ ((cayDet_isHomogeneous n C).pow _) _
    have := (cayDet_isHomogeneous n C).pow (l ^ i * y)
    rwa [← mul_add, Nat.sub_add_cancel (Nat.mul_le_mul_left _ hsy)]

end GlobalTheory.OddBlock.ExpBinomial

end

end

section
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Conclude with `@GlobalTheory.OddBlock.ExpBinomial.main`.
-/
theorem _root_.GlobalTheory.OddBlock.expBinomial : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 5 ≤ l → ∀ (i E n₀ : ℕ), Odd i → (E : ℝ) = 1 + ((l : ℝ) ^ i - l) / ((l : ℝ) ^ 2 - 1) → ∀ h₁ : MvPowerSeries ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C,
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h₁))) → (∀ α, MvPowerSeries.coeff α h₁ ≠ 0 → ∃ q, α (Sum.inr q) ≠ 0) →
    ∃ Q : ℕ → MvPolynomial (Fin n₀ × Fin n₀) C, Q 0 = 1 ∧ (∀ s, (Q s).IsHomogeneous (n₀ * (l ^ i * s))) ∧
      (∀ s : ℕ, 1 ≤ s → 1 ≤ n₀ → ∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.coeff A (Q s))) ∧
      ∀ y : ℕ, (∑ A ∈ ((MvPolynomial.rename Sum.inl (cayDet n₀ C) ^ (l ^ i * y) * MvPolynomial.rename Sum.inr (cayDet n₀ C) ^ y : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C)).support, MvPolynomial.coeff A ((MvPolynomial.rename Sum.inl (cayDet n₀ C) ^ (l ^ i * y) * MvPolynomial.rename Sum.inr (cayDet n₀ C) ^ y : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C)) * (A.prod fun _ e => (e.factorial : C)) * MvPowerSeries.coeff A (PowerSeries.subst (((∑ q : Fin n₀ × Fin n₀, MvPolynomial.C (-((l : C) ^ E)⁻¹) * MvPolynomial.X (Sum.inl q) ^ (l ^ i) * MvPolynomial.X (Sum.inr q) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C) : MvPowerSeries ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) C) + h₁) (PowerSeries.exp C))) = (-((l : C) ^ E)⁻¹) ^ (n₀ * y) * ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * (∑ A ∈ (cayDet n₀ C ^ (l ^ i * y)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * y)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * y - l ^ i * s) * Q s))) := by
  exact @GlobalTheory.OddBlock.ExpBinomial.main

end

section
open Formalism.L2.FormalSeriesBounds

noncomputable section

namespace GlobalTheory.OddBlock.BinomialValue

open Formalism.IncomingBounds ReciprocityTheory.PGsh

variable {C : Type} [Field C]

/- English proof (translation)
Establish `h1 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h3 : (l : ℝ) ^ 2 - 1 ≠ 0` using `by nlinarith`. Take `⟨k, rfl⟩` from `hi`. Establish `hk : (2 * k + 1 - 1) / 2 = k` using `by omega`. Establish `hne : (l : ℝ) ^ 2 ≠ 1` using `fun h => h3 (by rw [h]; ring)`.

Unfold `expE`. Rewrite using `[hk]`. Use `push_cast`. Rewrite using `[geom_sum_eq hne, ← pow_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem expE_cast {l i : ℕ} (hl : 2 ≤ l) (hi : Odd i) :
    (expE l i : ℝ) = 1 + ((l : ℝ) ^ i - l) / ((l : ℝ) ^ 2 - 1) := by
  have h1 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h3 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  obtain ⟨k, rfl⟩ := hi
  have hk : (2 * k + 1 - 1) / 2 = k := by omega
  have hne : (l : ℝ) ^ 2 ≠ 1 := fun h => h3 (by rw [h]; ring)
  unfold expE
  rw [hk]
  push_cast
  rw [geom_sum_eq hne, ← pow_mul]
  field_simp
  ring

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_exp, smul_eq_mul]`. Simplify using `[div_eq_inv_mul]`.

Introduce `k hk`. Assume the negation of the conclusion as `hc`. Apply `hk` to reduce the goal to its premises. Establish `hlt : m.degree < k` using `by simpa using hc`. Establish `: MvPowerSeries.coeff m (f ^ k) = 0`.

Apply `MvPowerSeries.coeff_of_lt_order` to reduce the goal to its premises. Use `lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf)` and prove the remaining obligations. Conclude with `hlt` after adjusting the coercions. Simplify using `[this]`.
-/
theorem subst_exp [CharZero C] {σ : Type} (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst f (PowerSeries.exp C) = mvExp f := by
  ext m
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_inv_mul]
  · intro k hk
    by_contra hc
    apply hk
    have hlt : m.degree < k := by simpa using hc
    have : MvPowerSeries.coeff m (f ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf)
      exact_mod_cast hlt
    simp [this]

/- English proof (translation)
Simplify using `[mfact, Finsupp.prod]`.
-/
theorem mfact_cast {σ : Type} (A : σ →₀ ℕ) : (A.prod fun _ e => (e.factorial : C)) = (mfact A : C) := by
  simp [mfact, Finsupp.prod]

/- English proof (translation)
Rewrite using `[detR, cayDet, AlgHom.map_det]`. Use `congr 1`. Use `ext1 i j`. Simplify using `[Matrix.mvPolynomialX]`.
-/
theorem detR_eq (n : ℕ) : detR C n = MvPolynomial.rename Sum.inr (cayDet n C) := by
  rw [detR, cayDet, AlgHom.map_det]
  congr 1
  ext1 i j
  simp [Matrix.mvPolynomialX]

/- English proof (translation)
Rewrite using `[jetAt0, MvPolynomial.support_rename_of_injective hf, Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective hf h]`. Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_coe, MvPolynomial.coeff_rename_mapDomain f hf, MvPolynomial.coeff_rename_mapDomain f hf, ← mfact_cast, Finsupp.prod_mapDomain_index_inj hf]`.
-/
theorem jetAt0_rename {σ τ : Type} (f : σ → τ) (hf : Function.Injective f) (P Q : MvPolynomial σ C) :
    jetAt0 (MvPolynomial.rename f P) ((MvPolynomial.rename f Q : MvPolynomial τ C) : MvPowerSeries τ C) =
      ∑ A ∈ P.support, MvPolynomial.coeff A P * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A Q := by
  classical
  rw [jetAt0, MvPolynomial.support_rename_of_injective hf,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective hf h]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_rename_mapDomain f hf, MvPolynomial.coeff_rename_mapDomain f hf,
    ← mfact_cast, Finsupp.prod_mapDomain_index_inj hf]

/- English proof (translation)
Take `⟨h1, h2, -, -⟩` from `GlobalTheory.CayleyCapelli.main.2 C n x`. Rewrite `h1` using `[h2, GlobalTheory.CayleyCapelli.detL_eq, ← map_pow, jetAt0_rename _ Sum.inl_injective]`. Conclude with `h1`.
-/
theorem pair_self [CharZero C] (n x : ℕ) :
    ∑ A ∈ (cayDet n C ^ x).support, MvPolynomial.coeff A (cayDet n C ^ x) * (A.prod fun _ e => (e.factorial : C)) *
      MvPolynomial.coeff A (cayDet n C ^ x) = (capNat n x : C) := by
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.CayleyCapelli.main.2 C n x
  rw [h2, GlobalTheory.CayleyCapelli.detL_eq, ← map_pow, jetAt0_rename _ Sum.inl_injective] at h1
  exact h1

/- English proof (translation)
Rewrite using `[hP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum, Fintype.sum_prod_type, Finset.smul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_mul, MvPolynomial.coe_mul, MvPolynomial.coe_pow, MvPolynomial.coe_X, MvPolynomial.coe_X, MvPolynomial.coe_C, mul_assoc, MvPowerSeries.smul_eq_C_mul]`.
-/
theorem hP_eq (l i n : ℕ) (h1 : MvPowerSeries (PVar n) C) :
    hP C l i n h1 = ((∑ q : Fin n × Fin n, MvPolynomial.C (-((l : C) ^ expE l i)⁻¹) *
      MvPolynomial.X (Sum.inl q) ^ (l ^ i) * MvPolynomial.X (Sum.inr q) : MvPolynomial (PVar n) C) :
        MvPowerSeries (PVar n) C) + h1 := by
  rw [hP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum, Fintype.sum_prod_type, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_mul, MvPolynomial.coe_mul,
    MvPolynomial.coe_pow, MvPolynomial.coe_X, MvPolynomial.coe_X, MvPolynomial.coe_C, mul_assoc,
    MvPowerSeries.smul_eq_C_mul]

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff h1 = 0`. Assume the negation of the conclusion as `hc`. Use `h 0 (by simpa using hc)` as an intermediate fact. Simplify using `[degR] at this`. Rewrite using `[hP, map_add, h0, MvPowerSeries.smul_eq_C_mul, map_mul, map_sum]`.

Simplify using `[map_sum]`.
-/
theorem constantCoeff_hP (l i n : ℕ) (h1 : MvPowerSeries (PVar n) C) (h : HM2 h1) :
    MvPowerSeries.constantCoeff (hP C l i n h1) = 0 := by
  have h0 : MvPowerSeries.constantCoeff h1 = 0 := by
    by_contra hc
    have := h 0 (by simpa using hc)
    simp [degR] at this
  rw [hP, map_add, h0, MvPowerSeries.smul_eq_C_mul, map_mul, map_sum]
  simp [map_sum]

/- English proof (translation)
Rewrite using `[Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type, degL, degR]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, Nat.cast_sum, Finset.sum_mul, mul_comm]`. Simplify using `only [Finset.mul_sum]`.
-/
theorem weight_sum (n : ℕ) (α : PVar n →₀ ℕ) (a b : ℝ) :
    α.sum (fun j e => Sum.elim (fun _ => a) (fun _ => b) j * (e : ℝ)) = (degL α : ℝ) * a + (degR α : ℝ) * b := by
  rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type, degL, degR]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, Nat.cast_sum, Finset.sum_mul, mul_comm]
  simp only [Finset.mul_sum]

/- English proof (translation)
Establish `hL : detL C 0 = 1` using `Matrix.det_isEmpty`. Establish `hR : detR C 0 = 1` using `Matrix.det_isEmpty`. Rewrite using `[LamP, hL, hR, one_pow, one_pow, one_mul, jetAt0, MvPolynomial.support_one, Finset.sum_singleton]`. Establish `: MvPowerSeries.coeff 0 (mvExp (hP C l i 0 h1)) = 1` using `by show (∑ k ∈ Finset.range ((0 : PVar 0 →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (hP C l i 0 h1 ^ k) / (k.factorial : C)) = 1`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Simplify using `[mfact]`.
-/
theorem lambdaFactor_zero_eq_one [CharZero C] (l i : ℕ) (h1 : MvPowerSeries (PVar 0) C) (y : ℕ) : LamP C l i 0 h1 y = 1 := by
  have hL : detL C 0 = 1 := Matrix.det_isEmpty
  have hR : detR C 0 = 1 := Matrix.det_isEmpty
  rw [LamP, hL, hR, one_pow, one_pow, one_mul, jetAt0, MvPolynomial.support_one, Finset.sum_singleton]
  have : MvPowerSeries.coeff 0 (mvExp (hP C l i 0 h1)) = 1 := by
    show (∑ k ∈ Finset.range ((0 : PVar 0 →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (hP C l i 0 h1 ^ k) / (k.factorial : C)) = 1
    simp
  rw [this]
  simp [mfact]

/- English proof (translation)
Introduce `C _ _ v l hl h5 hv i hi n0 h1 hm1 hm2`. Break down `Nat.eq_zero_or_pos n0 with rfl | hn` into its components or cases. Use `⟨fun s => if s = 0 then 1 else 0, by simp, fun y => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[lambdaFactor_zero_eq_one]`. Simplify using `[capNat]`.

Establish `: s ≠ 0` using `by omega`. Simplify using `[this]`. Establish `hl0 : (0 : ℝ) < (l : ℝ) ^ i` using `by have := hl.pos; positivity`. Take `⟨Q, hQ0, hQh, hQv, hQ⟩` from `GlobalTheory.OddBlock.expBinomial C v l hl hv h5 i (expE l i) n0 hi (expE_cast hl.two_le hi) h1 (fun α => by`. Establish `h` using `hm1 α`.

Rewrite using `[weight_sum]`. Distinguish the cases in `ht : v (MvPowerSeries.coeff α h1) = ⊤`. Rewrite using `[ht]`. Conclude with `le_top`. Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 ht`.

Rewrite `h`, the goal using `[← hr]`. Rewrite `h` using `[← WithTop.coe_add, WithTop.coe_le_coe]`. Rewrite using `[WithTop.coe_le_coe]`. Establish `e1 : r1 l i - del l i = 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)`. Unfold `r1 del rho`.

Rewrite using `[add_sub_assoc]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : r2 l - del l i = 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)` using `rfl`.

Rewrite `h` using `[e1, e2]`. Use the proof step `linarith)`. Use the proof step `(fun α hα => by`. Establish `h` using `hm2 α hα`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Simplify using `[degR, hc] at h)`. Establish `hcap : ∀ x, (capNat n0 x : C) ≠ 0` using `fun x => Nat.cast_ne_zero.2 (GlobalTheory.CayleyCapelli.main.2 C n0 x).2.2.2`. Use `⟨fun s => (∑ A ∈ (cayDet n0 C ^ (l ^ i * s)).support, MvPolynomial.coeff A (cayDet n0 C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q s)) / (capNat n0 (l ^ i * s) : C), ?_, fun y => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Use `pair_self (C := C) n0 0` as an intermediate fact.

Simplify using `only [mul_zero, hQ0]`. Rewrite `this`, the goal using `[pow_zero]`. Rewrite using `[this, div_self (hcap 0)]`. Establish `hy` using `hQ y`. Rewrite `hy` using `[← hP_eq, subst_exp _ (constantCoeff_hP l i n0 h1 hm2), ← GlobalTheory.CayleyCapelli.detL_eq, ← detR_eq]`.

Rewrite using `[LamP, jetAt0]`. Simplify using `only [← mfact_cast]`. Rewrite using `[hy, mul_assoc, Finset.mul_sum _ _ (capNat n0 (l ^ i * y) : C)]`. Use `congr 1`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations.

Establish `hsy : s ≤ y` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)`. Establish `h4` using `GlobalTheory.T.factorialWeightedPairing_detPow_proportional C n0 (l ^ i * s) (l ^ i * y) (Q s) (Nat.mul_le_mul_left _ hsy) (hQh s)`. Rewrite `h4` using `[pair_self, pair_self]`. Rewrite using `[eq_div_of_mul_eq (hcap _) h4]`. Expand and normalize the polynomial expressions, which then agree.

Use `GlobalTheory.T.determinantPairing_quotient_valuation_lower_bound C v l hl hv i n0 s (Q s) hs hn (hQv s hs hn)` as an intermediate fact. Rewrite `this` using `[pair_self]`. Conclude with `this`.
-/
theorem main : CoefficientExpansionLambda := by
  intro C _ _ v l hl h5 hv i hi n0 h1 hm1 hm2
  rcases Nat.eq_zero_or_pos n0 with rfl | hn
  · refine ⟨fun s => if s = 0 then 1 else 0, by simp, fun y => ?_, fun s hs => ?_⟩
    · rw [lambdaFactor_zero_eq_one]
      simp [capNat]
    · have : s ≠ 0 := by omega
      simp [this]
  have hl0 : (0 : ℝ) < (l : ℝ) ^ i := by have := hl.pos; positivity
  obtain ⟨Q, hQ0, hQh, hQv, hQ⟩ := GlobalTheory.OddBlock.expBinomial C v l hl hv h5 i (expE l i) n0 hi (expE_cast hl.two_le hi) h1
    (fun α => by
      have h := hm1 α
      rw [weight_sum]
      by_cases ht : v (MvPowerSeries.coeff α h1) = ⊤
      · rw [ht]; exact le_top
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
      rw [← hr] at h ⊢
      rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
      rw [WithTop.coe_le_coe]
      have e1 : r1 l i - del l i = 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i) := by
        unfold r1 del rho
        rw [add_sub_assoc]
        congr 1
        field_simp
        ring
      have e2 : r2 l - del l i = 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i) := rfl
      rw [e1, e2] at h
      linarith)
    (fun α hα => by
      have h := hm2 α hα
      by_contra hc
      push Not at hc
      simp [degR, hc] at h)
  have hcap : ∀ x, (capNat n0 x : C) ≠ 0 := fun x =>
    Nat.cast_ne_zero.2 (GlobalTheory.CayleyCapelli.main.2 C n0 x).2.2.2
  refine ⟨fun s => (∑ A ∈ (cayDet n0 C ^ (l ^ i * s)).support, MvPolynomial.coeff A (cayDet n0 C ^ (l ^ i * s)) *
    (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q s)) / (capNat n0 (l ^ i * s) : C), ?_, fun y => ?_,
    fun s hs => ?_⟩
  · have := pair_self (C := C) n0 0
    simp only [mul_zero, hQ0]
    rw [pow_zero] at this ⊢
    rw [this, div_self (hcap 0)]
  · have hy := hQ y
    rw [← hP_eq, subst_exp _ (constantCoeff_hP l i n0 h1 hm2), ← GlobalTheory.CayleyCapelli.detL_eq, ← detR_eq] at hy
    rw [LamP, jetAt0]
    simp only [← mfact_cast]
    rw [hy, mul_assoc, Finset.mul_sum _ _ (capNat n0 (l ^ i * y) : C)]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsy : s ≤ y := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have h4 := GlobalTheory.T.factorialWeightedPairing_detPow_proportional C n0 (l ^ i * s) (l ^ i * y) (Q s) (Nat.mul_le_mul_left _ hsy) (hQh s)
    rw [pair_self, pair_self] at h4
    rw [eq_div_of_mul_eq (hcap _) h4]
    ring
  · have := GlobalTheory.T.determinantPairing_quotient_valuation_lower_bound C v l hl hv i n0 s (Q s) hs hn (hQv s hs hn)
    rw [pair_self] at this
    exact this

end GlobalTheory.OddBlock.BinomialValue

end

end

section
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.OddBlock.WindowValuationBound

open Formalism.IncomingBounds (capNat LamP detL detR jetAt0 mvExp mfact hP expE PVar gam)

/- English proof (translation)
Introduce `h0` and use `by have hq : ∏ c ∈ Finset.range n0, (x + c).factorial ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _ exact hq (by rw [← GlobalTheory.LegendreFacts.capNat_mul, h0, zero_mul])`.
-/
theorem capNat_ne_zero (n0 x : ℕ) : capNat n0 x ≠ 0 := fun h0 => by
  have hq : ∏ c ∈ Finset.range n0, (x + c).factorial ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  exact hq (by rw [← GlobalTheory.LegendreFacts.capNat_mul, h0, zero_mul])

/- English proof (translation)
Establish `hL : detL C 0 = 1` using `by simp [detL]`. Establish `hR : detR C 0 = 1` using `by simp [detR]`. Unfold `LamP jetAt0`. Rewrite using `[hL, hR, one_pow, one_pow, one_mul, MvPolynomial.support_one, Finset.sum_singleton]`. Establish `: MvPowerSeries.coeff (0 : PVar 0 →₀ ℕ) (mvExp (hP C l i 0 h1)) = 1`.

Express the relevant statement in the definitionally equal form `∑ k ∈ Finset.range ((0 : PVar 0 →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (hP C l i 0 h1 ^ k) / (k.factorial : C) = 1`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using `[mfact]`.
-/
theorem value_zero_rows (C : Type) [Field C] (l i : ℕ) (h1 : MvPowerSeries (PVar 0) C) (y : ℕ) :
    LamP C l i 0 h1 y = 1 := by
  have hL : detL C 0 = 1 := by simp [detL]
  have hR : detR C 0 = 1 := by simp [detR]
  unfold LamP jetAt0
  rw [hL, hR, one_pow, one_pow, one_mul, MvPolynomial.support_one, Finset.sum_singleton]
  have : MvPowerSeries.coeff (0 : PVar 0 →₀ ℕ) (mvExp (hP C l i 0 h1)) = 1 := by
    change ∑ k ∈ Finset.range ((0 : PVar 0 →₀ ℕ).degree + 1),
      MvPowerSeries.coeff 0 (hP C l i 0 h1 ^ k) / (k.factorial : C) = 1
    simp
  rw [this]
  simp [mfact]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, v.map_mul, ih, h, ← WithTop.coe_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_pow_real {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {x : C} {r : ℝ}
    (h : v x = (r : WithTop ℝ)) (k : ℕ) : v (x ^ k) = (((k : ℝ) * r : ℝ) : WithTop ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, v.map_mul, ih, h, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

/- English proof (translation)
Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[v.map_zero]`. Conclude with `WithTop.top_ne_coe h`. Rewrite using `[v.map_neg]`.

Take `⟨t, ht⟩` from `ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.exists_real v (inv_ne_zero hx)`. Establish `e : v (x * x⁻¹) = 0` using `by rw [mul_inv_cancel₀ hx, v.map_one]`. Rewrite `e` using `[v.map_mul, h, ht, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj]`. Rewrite using `[ht]`. Use `congr 1`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem val_neg_inv_real {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {x : C} {r : ℝ}
    (h : v x = (r : WithTop ℝ)) : v (-x⁻¹) = ((-r : ℝ) : WithTop ℝ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at h
    exact WithTop.top_ne_coe h
  rw [v.map_neg]
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.exists_real v (inv_ne_zero hx)
  have e : v (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, v.map_one]
  rw [v.map_mul, h, ht, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at e
  rw [ht]
  congr 1
  linarith

/- English proof (translation)
Unfold `S0`. Rewrite using `[Nat.one_le_ceil_iff]`. Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast hl`. Establish `h2 : (1 : ℝ) ≤ n0` using `by exact_mod_cast hn`. Establish `h3 : 0 ≤ Real.logb l ((n0 : ℝ) + 1)` using `Real.logb_nonneg h1 (by linarith)`.

Check the signs of the components of the expression.
-/
theorem one_le_window (l i n0 : ℕ) (hl : 2 ≤ l) (hn : 1 ≤ n0) : 1 ≤ S0 l i n0 := by
  unfold S0
  rw [Nat.one_le_ceil_iff]
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl
  have h2 : (1 : ℝ) ≤ n0 := by exact_mod_cast hn
  have h3 : 0 ≤ Real.logb l ((n0 : ℝ) + 1) := Real.logb_nonneg h1 (by linarith)
  positivity

/- English proof (translation)
Introduce `C _ _ v l hl h5 hv i hi n n0 hn hn0 h1 hM1 hM2`. Use `⟨fun h0 Y0 => ?_, fun h0 y => ?_⟩` and prove the remaining obligations. Use `swap`. Substitute `h0` using the available equality. Conclude with `value_zero_rows C l i h1 y`.

Establish `hi1 : 1 ≤ i` using `hi.pos`. Take `⟨a, ha0, hLam, hbd⟩` from `GlobalTheory.OddBlock.BinomialValue.main C v l hl h5 hv i hi n0 h1 hM1 hM2`. Take `⟨hE, -, hI2, -⟩` from `GlobalTheory.radii_valuation_differences`. Establish `hS` using `one_le_window l i n0 hl.two_le h0`. Take `⟨y, hy1, hy2, hy3⟩` from `GlobalTheory.newtonBound_pos_and_newtonStep.2 C v (S0 l i n0) a hS ha0 (fun s hs => by`.

Establish `hpos` using `GlobalTheory.newtonBound_pos_and_newtonStep.1 l h5 i n0 s hi1 h0 hs`. Conclude with `lt_of_lt_of_le (WithTop.coe_pos.2 hpos) (hbd s (hS.trans hs))) Y0`. Use `⟨y, hy1, hy2, ?_⟩` and prove the remaining obligations. Establish `hv' : v (l : C) = ((1 : ℝ) : WithTop ℝ)` using `hv`. Establish `hcap : v (capNat n0 (l ^ i * y) : C) = ((padicValNat l (capNat n0 (l ^ i * y)) : ℝ) : WithTop ℝ)`.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hv (capNat_ne_zero _ _), Nat.factorization_def _ hl]`. Rewrite using `[hLam y, v.map_mul, v.map_mul, val_pow_real v (val_neg_inv_real v (val_pow_real v hv' (expE l i))) (n0 * y), hcap, ← WithTop.coe_add]`. Use `le_trans (add_le_add le_rfl hy3) ?_` and prove the remaining obligations. Rewrite using `[add_zero, WithTop.coe_le_coe]`. Take `⟨f1, f2⟩` from `GlobalTheory.LegendreFacts.capelli_bound l hl n0 n (l ^ i * y) hn hn0`.

Establish `e1` using `(hE l i hl.two_le hi).2`. Establish `e2` using `(hI2 l i hl.two_le hi1).1`. Unfold `bdP`. Rewrite using `[← e2, ← e1]`. Establish `e3 : (n0 : ℝ) * ((l ^ i * y : ℕ) : ℝ) / ((l : ℝ) - 1) = (n0 : ℝ) * y * ((l : ℝ) ^ i / ((l : ℝ) - 1))`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `f1`, `f2` using `[e3]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main : ThmP := by
  intro C _ _ v l hl h5 hv i hi n n0 hn hn0 h1 hM1 hM2
  refine ⟨fun h0 Y0 => ?_, fun h0 y => ?_⟩
  swap
  · subst h0
    exact value_zero_rows C l i h1 y
  have hi1 : 1 ≤ i := hi.pos
  obtain ⟨a, ha0, hLam, hbd⟩ := GlobalTheory.OddBlock.BinomialValue.main C v l hl h5 hv i hi n0 h1 hM1 hM2
  obtain ⟨hE, -, hI2, -⟩ := GlobalTheory.radii_valuation_differences
  have hS := one_le_window l i n0 hl.two_le h0
  obtain ⟨y, hy1, hy2, hy3⟩ := GlobalTheory.newtonBound_pos_and_newtonStep.2 C v (S0 l i n0) a hS ha0 (fun s hs => by
    have hpos := GlobalTheory.newtonBound_pos_and_newtonStep.1 l h5 i n0 s hi1 h0 hs
    exact lt_of_lt_of_le (WithTop.coe_pos.2 hpos) (hbd s (hS.trans hs))) Y0
  refine ⟨y, hy1, hy2, ?_⟩
  have hv' : v (l : C) = ((1 : ℝ) : WithTop ℝ) := hv
  have hcap : v (capNat n0 (l ^ i * y) : C) =
      ((padicValNat l (capNat n0 (l ^ i * y)) : ℝ) : WithTop ℝ) := by
    rw [ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hv (capNat_ne_zero _ _),
      Nat.factorization_def _ hl]
  rw [hLam y, v.map_mul, v.map_mul,
    val_pow_real v (val_neg_inv_real v (val_pow_real v hv' (expE l i))) (n0 * y), hcap,
    ← WithTop.coe_add]
  refine le_trans (add_le_add le_rfl hy3) ?_
  rw [add_zero, WithTop.coe_le_coe]
  obtain ⟨f1, f2⟩ := GlobalTheory.LegendreFacts.capelli_bound l hl n0 n (l ^ i * y) hn hn0
  have e1 := (hE l i hl.two_le hi).2
  have e2 := (hI2 l i hl.two_le hi1).1
  unfold bdP
  rw [← e2, ← e1]
  have e3 : (n0 : ℝ) * ((l ^ i * y : ℕ) : ℝ) / ((l : ℝ) - 1) =
      (n0 : ℝ) * y * ((l : ℝ) ^ i / ((l : ℝ) - 1)) := by
    push_cast
    ring
  rw [e3] at f1 f2
  push_cast
  nlinarith

end GlobalTheory.OddBlock.WindowValuationBound

end

section
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Conclude with `@GlobalTheory.OddBlock.WindowValuationBound.main`.
-/
theorem _root_.GlobalTheory.OddBlock.windowBound : ThmP := by
  exact @GlobalTheory.OddBlock.WindowValuationBound.main

end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.OddBlock.BlockContent

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Nat.cast_succ]`. Conclude with `v.map_le_add ih (by simp)`.
-/
theorem val_natCast_nonneg (m : ℕ) : 0 ≤ v (m : C) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact v.map_le_add ih (by simp)

/- English proof (translation)
Take `⟨k, rfl | rfl⟩` from `m.eq_nat_or_neg`. Simplify using `using val_natCast_nonneg v k`. Simplify using `using val_natCast_nonneg v k`.
-/
theorem val_intCast_nonneg (m : ℤ) : 0 ≤ v (m : C) := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa using val_natCast_nonneg v k
  · simpa using val_natCast_nonneg v k

/- English proof (translation)
Assume the negation of the conclusion as `hm`. Use `push_neg at hm`. Establish `hb : (1 : ℤ) = l * Nat.gcdA l m + m * Nat.gcdB l m`. Use `Nat.gcd_eq_gcd_ab l m` as an intermediate fact. Rewrite `this` using `[h]`.

Conclude with `this` after adjusting the coercions. Establish `hC : (1 : C) = (l : C) * (Nat.gcdA l m : C) + (m : C) * (Nat.gcdB l m : C)`. Conclude with `congrArg (fun z : ℤ => (z : C)) hb` after adjusting the coercions. Establish `h1 : 0 < v ((l : C) * (Nat.gcdA l m : C))`. Rewrite using `[v.map_mul, hv]`.

Conclude with `lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (val_intCast_nonneg v _))`. Establish `h2 : 0 < v ((m : C) * (Nat.gcdB l m : C))`. Rewrite using `[v.map_mul]`. Conclude with `lt_of_lt_of_le hm (le_add_of_nonneg_right (val_intCast_nonneg v _))`. Establish `h3` using `v.map_lt_add h1 h2`.

Rewrite `h3` using `[← hC, v.map_one]`. Conclude with `lt_irrefl _ h3`.
-/
theorem val_coprime_le {l m : ℕ} (hv : v (l : C) = 1) (h : Nat.Coprime l m) : v (m : C) ≤ 0 := by
  by_contra hm
  push_neg at hm
  have hb : (1 : ℤ) = l * Nat.gcdA l m + m * Nat.gcdB l m := by
    have := Nat.gcd_eq_gcd_ab l m
    rw [h] at this
    exact_mod_cast this
  have hC : (1 : C) = (l : C) * (Nat.gcdA l m : C) + (m : C) * (Nat.gcdB l m : C) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : C)) hb
  have h1 : 0 < v ((l : C) * (Nat.gcdA l m : C)) := by
    rw [v.map_mul, hv]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have h2 : 0 < v ((m : C) * (Nat.gcdB l m : C)) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hm (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have h3 := v.map_lt_add h1 h2
  rw [← hC, v.map_one] at h3
  exact lt_irrefl _ h3

/- English proof (translation)
Take `⟨e, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one`. Use `haveI := Fact.mk hl`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero _)`. Rewrite using `[padicValNat.mul (pow_ne_zero _ hl.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero, Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow, hv]`. Use `val_coprime_le v hv ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_le_padicValNat {l N : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) (hN : N ≠ 0) :
    v (N : C) ≤ ((padicValNat l N : ℝ) : WithTop ℝ) := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one
  haveI := Fact.mk hl
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  rw [padicValNat.mul (pow_ne_zero _ hl.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow, hv]
  have := val_coprime_le v hv ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  calc e • (1 : WithTop ℝ) + v (m : C) ≤ e • (1 : WithTop ℝ) + 0 := by gcongr
    _ = _ := by simp

/- English proof (translation)
Use `(val_le_padicValNat v hl hv N.factorial_ne_zero).trans ?_` and prove the remaining obligations. Use `haveI := Fact.mk hl`. Establish `h` using `sub_one_mul_padicValNat_factorial (p := l) N`. Establish `h2 : (l - 1) * padicValNat l N.factorial ≤ N` using `h ▸ Nat.sub_le _ _`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.two_le`.

Establish `h3 : ((l : ℝ) - 1) * (padicValNat l N.factorial : ℝ) ≤ N`. Establish `: (((l - 1) * padicValNat l N.factorial : ℕ) : ℝ) ≤ N` using `by exact_mod_cast h2`. Rewrite `this` using `[Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_one]`. Then use the resulting hypothesis. Rewrite using `[WithTop.coe_le_coe, le_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem val_factorial_le {l : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) (N : ℕ) :
    v ((N.factorial : ℕ) : C) ≤ (((N : ℝ) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) := by
  refine (val_le_padicValNat v hl hv N.factorial_ne_zero).trans ?_
  haveI := Fact.mk hl
  have h := sub_one_mul_padicValNat_factorial (p := l) N
  have h2 : (l - 1) * padicValNat l N.factorial ≤ N := h ▸ Nat.sub_le _ _
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h3 : ((l : ℝ) - 1) * (padicValNat l N.factorial : ℝ) ≤ N := by
    have : (((l - 1) * padicValNat l N.factorial : ℕ) : ℝ) ≤ N := by exact_mod_cast h2
    rwa [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_one] at this
  rw [WithTop.coe_le_coe, le_div_iff₀ (by linarith)]
  linarith

/- English proof (translation)
Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hp : (l : ℝ) ≤ (l : ℝ) ^ i` using `le_self_pow₀ (by linarith) (by omega)`. Establish `hd : 0 < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hg : gam l = (l : ℝ) / ((l : ℝ) ^ 2 - 1)`. Unfold `gam`.

Both sides reduce to the same expression. Rewrite using `[hg, sub_nonneg, ← mul_div_assoc, le_div_iff₀ hd]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem slope_nonneg {l i : ℕ} (hl : 2 ≤ l) (hi : 1 ≤ i) :
    0 ≤ ((l : ℝ) ^ i + 1) * gam l - 1 := by
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hp : (l : ℝ) ≤ (l : ℝ) ^ i := le_self_pow₀ (by linarith) (by omega)
  have hd : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hg : gam l = (l : ℝ) / ((l : ℝ) ^ 2 - 1) := by
    unfold gam
    rfl
  rw [hg, sub_nonneg, ← mul_div_assoc, le_div_iff₀ hd]
  nlinarith

/- English proof (translation)
Introduce `C _ _ v l hl h5 hv i n n0 y hi hn hn0 Λ hΛ`. Establish `h1` using `val_factorial_le v hl hv (l ^ i * y)`. Establish `h2` using `val_factorial_le v hl hv y`. Establish `hs` using `slope_nonneg (l := l) (i := i) hl.two_le hi.pos`. Rewrite using `[v.map_mul, Nat.cast_pow, v.map_pow, Nat.cast_mul, v.map_mul]`.

Use `(add_le_add (nsmul_le_nsmul_right (add_le_add h1 h2) (n - n0)) hΛ).trans ?_` and prove the remaining obligations. Rewrite using `[← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul, Nat.cast_sub hn0]`. Unfold `bdP`. Establish `hle : (n0 : ℝ) ≤ n` using `by exact_mod_cast hn0`. Establish `h3 : (n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) ≤ (n : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1)` using `by gcongr`.

Establish `h4 : ((n : ℝ) - n0) * ((((l ^ i * y : ℕ) : ℝ)) / ((l : ℝ) - 1) + (y : ℝ) / ((l : ℝ) - 1)) = ((n : ℝ) - n0) * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)` using `by push_cast; ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem biContent : BiContent := by
  intro C _ _ v l hl h5 hv i n n0 y hi hn hn0 Λ hΛ
  have h1 := val_factorial_le v hl hv (l ^ i * y)
  have h2 := val_factorial_le v hl hv y
  have hs := slope_nonneg (l := l) (i := i) hl.two_le hi.pos
  rw [v.map_mul, Nat.cast_pow, v.map_pow, Nat.cast_mul, v.map_mul]
  refine (add_le_add (nsmul_le_nsmul_right (add_le_add h1 h2) (n - n0)) hΛ).trans ?_
  rw [← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
    Nat.cast_sub hn0]
  unfold bdP
  have hle : (n0 : ℝ) ≤ n := by exact_mod_cast hn0
  have h3 : (n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) ≤
      (n : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) := by gcongr
  have h4 : ((n : ℝ) - n0) * ((((l ^ i * y : ℕ) : ℝ)) / ((l : ℝ) - 1) + (y : ℝ) / ((l : ℝ) - 1)) =
      ((n : ℝ) - n0) * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1) := by
    push_cast; ring
  linarith

/- English proof (translation)
Introduce `C _ _ v l hl h5 hv i hi n0 n m hn h1n hm hr t t' h1 hH hM1 hM2 Y0`. Take `⟨y, hy1, hy2, hy⟩` from `(hP C v l hl h5 hv i hi n n0 (h1n.trans hn) hn h1 hM1 hM2).1 h1n Y0`. Use `⟨y, hy1, hy2, ?_⟩` and prove the remaining obligations. Rewrite using `[hV C l i n0 n hn hr t t' h1 hH y]`. Use `(biContent C v l hl h5 hv i n n0 y hi (h1n.trans hn) hn _ hy).trans ?_` and prove the remaining obligations.

Rewrite using `[WithTop.coe_le_coe]`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.two_le`. Establish `hd : (0 : ℝ) ≤ (l : ℝ) - 1` using `by linarith`. Establish `hm' : (n : ℝ) - n0 ≤ ((i : ℝ) + 1) * m`. Establish `: ((n - n0 : ℕ) : ℝ) ≤ (((i + 1) * m : ℕ) : ℝ)` using `by exact_mod_cast hm`.

Rewrite `this` using `[Nat.cast_sub hn]`. Move the coercions through the operations in `at this`. Conclude with `this`. Use `gcongr`.
-/
theorem biWindow_of (hP : Formalism.L2.FormalSeriesBounds.ThmP) (hV : BiValue) : BiWindow := by
  intro C _ _ v l hl h5 hv i hi n0 n m hn h1n hm hr t t' h1 hH hM1 hM2 Y0
  obtain ⟨y, hy1, hy2, hy⟩ := (hP C v l hl h5 hv i hi n n0 (h1n.trans hn) hn h1 hM1 hM2).1 h1n Y0
  refine ⟨y, hy1, hy2, ?_⟩
  rw [hV C l i n0 n hn hr t t' h1 hH y]
  refine (biContent C v l hl h5 hv i n n0 y hi (h1n.trans hn) hn _ hy).trans ?_
  rw [WithTop.coe_le_coe]
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hd : (0 : ℝ) ≤ (l : ℝ) - 1 := by linarith
  have hm' : (n : ℝ) - n0 ≤ ((i : ℝ) + 1) * m := by
    have : ((n - n0 : ℕ) : ℝ) ≤ (((i + 1) * m : ℕ) : ℝ) := by exact_mod_cast hm
    rw [Nat.cast_sub hn] at this
    push_cast at this
    exact this
  gcongr

/- English proof (translation)
Assemble the required witnesses or components as `⟨biContent, biWindow_of GlobalTheory.OddBlock.windowBound GlobalTheory.T.blockValue_on_rows_eq⟩`.
-/
theorem biContent_and_biWindow : BiContent ∧ BiWindow :=
  ⟨biContent, biWindow_of GlobalTheory.OddBlock.windowBound GlobalTheory.T.blockValue_on_rows_eq⟩

end GlobalTheory.OddBlock.BlockContent

end

section
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Conclude with `@GlobalTheory.OddBlock.BlockContent.biContent_and_biWindow`.
-/
theorem _root_.GlobalTheory.OddBlock.content_and_window : BiContent ∧ BiWindow := by
  exact @GlobalTheory.OddBlock.BlockContent.biContent_and_biWindow

end
