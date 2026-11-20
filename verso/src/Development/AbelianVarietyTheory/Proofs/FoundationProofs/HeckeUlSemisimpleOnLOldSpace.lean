import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqSemisimpleCuspFormsGamma1Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamondStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.OldSpace

/- English proof (translation)
Establish `h : (mat γ).det ≠ 0` using `by simp [mat]`. Unfold `toGL`. Rewrite using `[dif_neg h]`. Use extensionality with `i j`. Simplify using `[mat, Matrix.SpecialLinearGroup.mapGL]`.
-/
theorem toGL_mat (γ : SL(2, ℤ)) : toGL (mat γ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have h : (mat γ).det ≠ 0 := by simp [mat]
  unfold toGL
  rw [dif_neg h]
  ext i j
  simp [mat, Matrix.SpecialLinearGroup.mapGL]

/- English proof (translation)
Establish `hAB : (A * B).det ≠ 0` using `by rw [Matrix.det_mul]; exact mul_ne_zero hA hB`. Unfold `toGL`. Rewrite using `[dif_neg hA, dif_neg hB, dif_neg hAB]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem toGL_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGL (A * B) = toGL A * toGL B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  unfold toGL
  rw [dif_neg hA, dif_neg hB, dif_neg hAB]
  ext i j
  simp [Matrix.mul_apply]

/- English proof (translation)
Unfold `toGL`. Rewrite using `[dif_neg hA]`. Simplify using `[Matrix.det_fin_two]`.
-/
theorem det_toGL (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) :
    ((toGL A).det : ℝ) = (A.det : ℝ) := by
  unfold toGL
  rw [dif_neg hA]
  simp [Matrix.det_fin_two]

/- English proof (translation)
Establish `h : (0 : ℝ) < ((toGL A).det : ℝ)`. Rewrite using `[det_toGL A hA.ne']`. Conclude with `hA` after adjusting the coercions. Establish `h' : 0 < (↑(toGL A) : Matrix (Fin 2) (Fin 2) ℝ).det` using `by simpa using h`. Simplify using `[UpperHalfPlane.σ, h']`.
-/
theorem sigma_toGL (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : 0 < A.det) (c : ℂ) : σ (toGL A) c = c := by
  have h : (0 : ℝ) < ((toGL A).det : ℝ) := by
    rw [det_toGL A hA.ne']; exact_mod_cast hA
  have h' : 0 < (↑(toGL A) : Matrix (Fin 2) (Fin 2) ℝ).det := by simpa using h
  simp [UpperHalfPlane.σ, h']

/- English proof (translation)
Rewrite using `[ModularForm.smul_slash, sigma_toGL A hA]`.
-/
theorem slash_smul_toGL (k : ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : 0 < A.det) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] toGL A = c • (f ∣[k] toGL A) := by
  rw [ModularForm.smul_slash, sigma_toGL A hA]

end GlobalTheory.OldSpace

namespace GlobalTheory.OldSpace

/- English proof (translation)
Unfold `toGL`. Rewrite using `[dif_neg hA]`. Simplify using the standard rewrite rules.
-/
theorem toGL_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (i j : Fin 2) :
    (↑(toGL A) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  unfold toGL
  rw [dif_neg hA]
  simp

/- English proof (translation)
Establish `h : 0 < ((toGL A).det : ℝ)` using `by rw [det_toGL A hA.ne']; exact_mod_cast hA`. Rewrite using `[UpperHalfPlane.coe_smul_of_det_pos h]`. Simplify using `[UpperHalfPlane.num, UpperHalfPlane.denom, toGL_apply A hA.ne']`.
-/
theorem toGL_smul_coe (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : 0 < A.det) (τ : ℍ) :
    ((toGL A • τ : ℍ) : ℂ) = ((A 0 0 : ℂ) * τ + A 0 1) / ((A 1 0 : ℂ) * τ + A 1 1) := by
  have h : 0 < ((toGL A).det : ℝ) := by rw [det_toGL A hA.ne']; exact_mod_cast hA
  rw [UpperHalfPlane.coe_smul_of_det_pos h]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, toGL_apply A hA.ne']

/- English proof (translation)
Rewrite using `[ModularForm.slash_apply, sigma_toGL A hA, det_toGL A hA.ne']`. Establish `h0 : (0 : ℝ) ≤ (A.det : ℝ)` using `by exact_mod_cast hA.le`. Rewrite using `[abs_of_nonneg h0]`. Simplify using `[UpperHalfPlane.denom, toGL_apply A hA.ne']`.
-/
theorem slash_toGL_apply (k : ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : 0 < A.det) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toGL A) τ = f (toGL A • τ) * ((A.det : ℝ) : ℂ) ^ (k - 1) * ((A 1 0 : ℂ) * τ + A 1 1) ^ (-k) := by
  rw [ModularForm.slash_apply, sigma_toGL A hA, det_toGL A hA.ne']
  have h0 : (0 : ℝ) ≤ (A.det : ℝ) := by exact_mod_cast hA.le
  rw [abs_of_nonneg h0]
  simp [UpperHalfPlane.denom, toGL_apply A hA.ne']

/- English proof (translation)
Establish `hd : 0 < (!![(l : ℤ), 0; 0, (l : ℤ)]).det`. Rewrite using `[Matrix.det_fin_two_of]`. Establish `: (0 : ℤ) < l` using `by exact_mod_cast hl`. Use the polynomial consequences of the given equalities and inequalities. Establish `hl' : (l : ℂ) ≠ 0` using `by exact_mod_cast hl.ne'`.

Use function extensionality and compare the values at `τ`. Rewrite using `[slash_toGL_apply k _ hd]`. Establish `hτ : toGL !![(l : ℤ), 0; 0, (l : ℤ)] • τ = τ` using `by ext1`. Rewrite using `[toGL_smul_coe _ hd]`. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hτ, Matrix.det_fin_two_of]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Simplify using `only [zero_mul, zero_add, sub_zero]`.

Establish `e2 : (l : ℂ) ^ (2 * (k - 1)) * (l : ℂ) ^ (-k) = (l : ℂ) ^ (k - 2)`. Rewrite using `[← zpow_add₀ hl']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[show ((l : ℂ) * l) = (l : ℂ) ^ (2 : ℤ) by rw [zpow_two], ← zpow_mul, mul_assoc, e2, mul_comm]`.
-/
theorem slash_scalar (k : ℤ) (l : ℕ) (hl : 0 < l) (f : ℍ → ℂ) :
    f ∣[k] toGL !![(l : ℤ), 0; 0, (l : ℤ)] = ((l : ℂ) ^ (k - 2)) • f := by
  have hd : 0 < (!![(l : ℤ), 0; 0, (l : ℤ)]).det := by
    rw [Matrix.det_fin_two_of]
    have : (0 : ℤ) < l := by exact_mod_cast hl
    nlinarith
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  funext τ
  rw [slash_toGL_apply k _ hd]
  have hτ : toGL !![(l : ℤ), 0; 0, (l : ℤ)] • τ = τ := by
    ext1
    rw [toGL_smul_coe _ hd]
    simp
    field_simp
  rw [hτ, Matrix.det_fin_two_of]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [zero_mul, zero_add, sub_zero]
  have e2 : (l : ℂ) ^ (2 * (k - 1)) * (l : ℂ) ^ (-k) = (l : ℂ) ^ (k - 2) := by
    rw [← zpow_add₀ hl']; congr 1; ring
  rw [show ((l : ℂ) * l) = (l : ℂ) ^ (2 : ℤ) by rw [zpow_two], ← zpow_mul, mul_assoc, e2, mul_comm]

/- English proof (translation)
Establish `hm : ModularGroup.T ^ j ∈ CongruenceSubgroup.Gamma1 N`. Rewrite using `[CongruenceSubgroup.Gamma1_mem, ModularGroup.coe_T_zpow]`. Simplify using the standard rewrite rules. Establish `e : toGL !![1, j; 0, 1] = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ j)`. Rewrite using `[← toGL_mat, mat, ModularGroup.coe_T_zpow]`.

Rewrite using `[e]`. Conclude with `SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hm)`.
-/
theorem slash_T_cusp (N : ℕ) (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) (j : ℤ) :
    ⇑f ∣[k] toGL !![1, j; 0, 1] = ⇑f := by
  have hm : ModularGroup.T ^ j ∈ CongruenceSubgroup.Gamma1 N := by
    rw [CongruenceSubgroup.Gamma1_mem, ModularGroup.coe_T_zpow]
    simp
  have e : toGL !![1, j; 0, 1] = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ j) := by
    rw [← toGL_mat, mat, ModularGroup.coe_T_zpow]
  rw [e]
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hm)

end GlobalTheory.OldSpace

namespace GlobalTheory.OldSpace

/- English proof (translation)
Simplify using `[dg, Matrix.det_fin_two_of]`.
-/
theorem det_dg (l : ℕ) : (dg (l : ℤ) 1).det = l := by simp [dg, Matrix.det_fin_two_of]

/- English proof (translation)
Simplify using `[ulFam, Matrix.det_fin_two_of]`.
-/
theorem det_ulFam (l : ℕ) (j : Fin l) : (ulFam l j).det = l := by simp [ulFam, Matrix.det_fin_two_of]

/- English proof (translation)
Establish `hl0 : (0 : ℤ) < l` using `by exact_mod_cast hl`. Establish `hl' : (l : ℂ) ≠ 0` using `by exact_mod_cast hl.ne'`. Unfold `UlF hkF`. Establish `key : ∀ j : Fin l, (⇑f ∣[k] toGL (dg l 1)) ∣[k] toGL (ulFam l j) = ((l : ℂ) ^ (k - 2)) • ⇑f`. Introduce `j`.

Establish `hD : (dg (l : ℤ) 1).det ≠ 0` using `by rw [det_dg]; omega`. Establish `hU : (ulFam l j).det ≠ 0` using `by rw [det_ulFam]; omega`. Establish `hS : (!![(l : ℤ), 0; 0, (l : ℤ)]).det ≠ 0`. Rewrite using `[Matrix.det_fin_two_of]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hT : (!![1, (j : ℤ); 0, 1]).det ≠ 0` using `by rw [Matrix.det_fin_two_of]; norm_num`. Rewrite using `[← SlashAction.slash_mul, ← toGL_mul _ _ hD hU]`. Establish `e : dg (l : ℤ) 1 * ulFam l j = !![(l : ℤ), 0; 0, (l : ℤ)] * !![1, (j : ℤ); 0, 1]`. Apply the tactic sequence `ext a b; fin_cases a <;> fin_cases b <;> simp [dg, ulFam, Matrix.mul_apply, Fin.sum_univ_two]`. Rewrite using `[e, toGL_mul _ _ hS hT, SlashAction.slash_mul, slash_scalar k l hl, slash_smul_toGL k _ (by rw [Matrix.det_fin_two_of]; norm_num), slash_T_cusp]`.

Rewrite using `[Finset.sum_congr rfl (fun j _ => key j), Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Use `congr 1`. Rewrite using `[show k - 1 = (k - 2) + 1 by ring, zpow_add_one₀ hl', mul_comm]`.
-/
theorem ul_slash_dg (N : ℕ) (k : ℤ) (l : ℕ) (hl : 0 < l) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) :
    UlF k l (⇑f ∣[k] toGL (dg l 1)) = ((l : ℂ) ^ (k - 1)) • ⇑f := by
  have hl0 : (0 : ℤ) < l := by exact_mod_cast hl
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold UlF hkF
  have key : ∀ j : Fin l, (⇑f ∣[k] toGL (dg l 1)) ∣[k] toGL (ulFam l j) = ((l : ℂ) ^ (k - 2)) • ⇑f := by
    intro j
    have hD : (dg (l : ℤ) 1).det ≠ 0 := by rw [det_dg]; omega
    have hU : (ulFam l j).det ≠ 0 := by rw [det_ulFam]; omega
    have hS : (!![(l : ℤ), 0; 0, (l : ℤ)]).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]; nlinarith
    have hT : (!![1, (j : ℤ); 0, 1]).det ≠ 0 := by rw [Matrix.det_fin_two_of]; norm_num
    rw [← SlashAction.slash_mul, ← toGL_mul _ _ hD hU]
    have e : dg (l : ℤ) 1 * ulFam l j = !![(l : ℤ), 0; 0, (l : ℤ)] * !![1, (j : ℤ); 0, 1] := by
      ext a b; fin_cases a <;> fin_cases b <;> simp [dg, ulFam, Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, toGL_mul _ _ hS hT, SlashAction.slash_mul, slash_scalar k l hl,
      slash_smul_toGL k _ (by rw [Matrix.det_fin_two_of]; norm_num), slash_T_cusp]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  rw [show k - 1 = (k - 2) + 1 by ring, zpow_add_one₀ hl', mul_comm]

/- English proof (translation)
Simplify using `[tqFam, ulFam]`.
-/
theorem tqFam_castSucc (l : ℕ) (s : SL(2, ℤ)) (i : Fin l) : tqFam l s (Fin.castSucc i) = ulFam l i := by
  simp [tqFam, ulFam]

/- English proof (translation)
Simplify using `[tqFam]`.
-/
theorem tqFam_last (l : ℕ) (s : SL(2, ℤ)) : tqFam l s (Fin.last l) = mat s * dg (l : ℤ) 1 := by
  simp [tqFam]

/- English proof (translation)
Establish `hl0 : (0 : ℤ) < l` using `by exact_mod_cast hl`. Use `show (∑ i, f ∣[k] toGL (tqFam l s i)) = (∑ j, f ∣[k] toGL (ulFam l j)) + _`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [tqFam_castSucc]`. Use `congr 1`.

Establish `e` using `tqFam_last l s`. Establish `hs1 : s ∈ CongruenceSubgroup.Gamma0 N` using `by simpa using hs.1`. Establish `hsd : (mat s).det ≠ 0` using `by simp [mat]`. Establish `hD : (dg (l : ℤ) 1).det ≠ 0` using `by rw [det_dg]; omega`. Rewrite using `[e, toGL_mul _ _ hsd hD, SlashAction.slash_mul, toGL_mat]`.

Establish `h2 : f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ s) = χ (l : ZMod N) • f`. Use `hf s hs1` as an intermediate fact. Rewrite `this` using `[hs.2]`. Conclude with `this`. Rewrite using `[h2, slash_smul_toGL k _ (by rw [det_dg]; exact hl0)]`.
-/
theorem tq_eq (N : ℕ) (k : ℤ) (l : ℕ) (hl : 0 < l) (s : SL(2, ℤ)) (χ : DirichletCharacter ℂ N)
    (hs : IsDiam N 1 (l : ZMod N) s) (f : ℍ → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → f ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • f) :
    TqF k l s f = UlF k l f + χ (l : ZMod N) • (f ∣[k] toGL (dg l 1)) := by
  have hl0 : (0 : ℤ) < l := by exact_mod_cast hl
  show (∑ i, f ∣[k] toGL (tqFam l s i)) = (∑ j, f ∣[k] toGL (ulFam l j)) + _
  rw [Fin.sum_univ_castSucc]
  simp only [tqFam_castSucc]
  congr 1
  · have e := tqFam_last l s
    have hs1 : s ∈ CongruenceSubgroup.Gamma0 N := by simpa using hs.1
    have hsd : (mat s).det ≠ 0 := by simp [mat]
    have hD : (dg (l : ℤ) 1).det ≠ 0 := by rw [det_dg]; omega
    rw [e, toGL_mul _ _ hsd hD, SlashAction.slash_mul, toGL_mat]
    have h2 : f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ s) = χ (l : ZMod N) • f := by
      have := hf s hs1
      rw [hs.2] at this
      exact this
    rw [h2, slash_smul_toGL k _ (by rw [det_dg]; exact hl0)]

/- English proof (translation)
Establish `hb` using `Nat.gcd_eq_gcd_ab l N`. Rewrite `hb` using `[h]`. Establish `hdet : (!![Nat.gcdA l N, -Nat.gcdB l N; (N : ℤ), (l : ℤ)]).det = 1`. Rewrite using `[Matrix.det_fin_two_of]`. Move the coercions through the operations in `at hb`.

Combine the linear equalities and inequalities to obtain the conclusion. Set `s : SL(2, ℤ)` to `⟨!![Nat.gcdA l N, -Nat.gcdB l N; (N : ℤ), (l : ℤ)], hdet⟩`. Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_one, CongruenceSubgroup.Gamma0_mem]`. Simplify using `[s]`.

Simplify using `[mat, s]`.
-/
theorem exists_diam (N l : ℕ) (h : Nat.Coprime l N) : ∃ s : SL(2, ℤ), IsDiam N 1 (l : ZMod N) s := by
  have hb := Nat.gcd_eq_gcd_ab l N
  rw [h] at hb
  have hdet : (!![Nat.gcdA l N, -Nat.gcdB l N; (N : ℤ), (l : ℤ)]).det = 1 := by
    rw [Matrix.det_fin_two_of]; push_cast at hb; linarith
  let s : SL(2, ℤ) := ⟨!![Nat.gcdA l N, -Nat.gcdB l N; (N : ℤ), (l : ℤ)], hdet⟩
  refine ⟨s, ?_, ?_⟩
  · rw [mul_one, CongruenceSubgroup.Gamma0_mem]; simp [s]
  · simp [mat, s]

noncomputable def uL (k : ℤ) (l : ℕ) : Module.End ℂ (ℍ → ℂ) where
  toFun := UlF k l
  map_add' f g := by
    unfold UlF hkF
    simp [SlashAction.add_slash, Finset.sum_add_distrib]
  map_smul' c f := by
    unfold UlF hkF
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hl : l = 0
    · subst hl; exact j.elim0
    exact slash_smul_toGL k _ (by rw [det_ulFam]; exact_mod_cast Nat.pos_of_ne_zero hl) c f

noncomputable def vL (k : ℤ) (l : ℕ) (hl : 0 < l) : Module.End ℂ (ℍ → ℂ) where
  toFun f := f ∣[k] toGL (dg l 1)
  map_add' f g := SlashAction.add_slash _ _ _ _
  map_smul' c f := slash_smul_toGL k _ (by rw [det_dg]; exact_mod_cast hl) c f

end GlobalTheory.OldSpace

namespace GlobalTheory.OldSpace

def HasChi (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → f ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • f

/- English proof (translation)
Introduce `γ _`. Simplify using the standard rewrite rules.
-/
theorem hasChi_zero (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) : HasChi N k χ 0 := by
  intro γ _; simp

/- English proof (translation)
Introduce `γ hγ`. Rewrite using `[SlashAction.add_slash, hf γ hγ, hg γ hγ, smul_add]`.
-/
theorem hasChi_add {N : ℕ} {k : ℤ} {χ : DirichletCharacter ℂ N} {f g : ℍ → ℂ} (hf : HasChi N k χ f)
    (hg : HasChi N k χ g) : HasChi N k χ (f + g) := by
  intro γ hγ; rw [SlashAction.add_slash, hf γ hγ, hg γ hγ, smul_add]

/- English proof (translation)
Introduce `γ hγ`. Rewrite using `[ModularForm.SL_smul_slash, hf γ hγ, smul_comm]`.
-/
theorem hasChi_smul {N : ℕ} {k : ℤ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ} (c : ℂ) (hf : HasChi N k χ f) :
    HasChi N k χ (c • f) := by
  intro γ hγ; rw [ModularForm.SL_smul_slash, hf γ hγ, smul_comm]

noncomputable def coeL (N : ℕ) (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma1 N) k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ⇑f
  map_add' f g := rfl
  map_smul' c f := rfl

def chiSpace (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (ℍ → ℂ) where
  carrier := {G | ∃ f : CuspForm (CongruenceSubgroup.Gamma1 N) k, ⇑f = G ∧ HasChi N k χ G}
  add_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f + g, rfl, hasChi_add hf hg⟩
  zero_mem' := ⟨0, rfl, hasChi_zero N k χ⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl, hf⟩
    exact ⟨c • f, rfl, hasChi_smul c hf⟩

/- English proof (translation)
Use `haveI := (UpperTheory.V.Sd.finDim N k).1`. Establish `hle : chiSpace N k χ ≤ LinearMap.range (coeL N k)`. Introduce and unpack `_ ⟨f, rfl, _⟩`. Conclude with `⟨f, rfl⟩`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem finiteDimensional_chiSpace (N : ℕ) [NeZero N] (k : ℕ) (χ : DirichletCharacter ℂ N) :
    FiniteDimensional ℂ (chiSpace N k χ) := by
  haveI := (UpperTheory.V.Sd.finDim N k).1
  have hle : chiSpace N k χ ≤ LinearMap.range (coeL N k) := by
    rintro _ ⟨f, rfl, _⟩
    exact ⟨f, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

def Good (u : Module.End ℂ (ℍ → ℂ)) (α : ℂ) (G : ℍ → ℂ) : Prop :=
  ∃ g : ℂ[X], g.eval α ≠ 0 ∧ aeval u ((X - C α) * g) G = 0

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by simp, by simp⟩`.
-/
theorem good_zero (u : Module.End ℂ (ℍ → ℂ)) (α : ℂ) : Good u α 0 := ⟨1, by simp, by simp⟩

/- English proof (translation)
Take `⟨g, hg, hG⟩` from `hG`. Take `⟨h, hh, hH⟩` from `hH`. Use `⟨g * h, by simp [hg, hh], ?_⟩` and prove the remaining obligations. Establish `e1 : (X - C α) * (g * h) = h * ((X - C α) * g)` using `by ring`. Establish `e2 : (X - C α) * (g * h) = g * ((X - C α) * h)` using `by ring`.

Establish `hG' : aeval u ((X - C α) * (g * h)) G = 0`. Rewrite using `[e1, map_mul, Module.End.mul_apply, hG, map_zero]`. Establish `hH' : aeval u ((X - C α) * (g * h)) H = 0`. Rewrite using `[e2, map_mul, Module.End.mul_apply, hH, map_zero]`. Rewrite using `[map_add, hG', hH', add_zero]`.
-/
theorem good_add {u : Module.End ℂ (ℍ → ℂ)} {α : ℂ} {G H : ℍ → ℂ} (hG : Good u α G) (hH : Good u α H) :
    Good u α (G + H) := by
  obtain ⟨g, hg, hG⟩ := hG
  obtain ⟨h, hh, hH⟩ := hH
  refine ⟨g * h, by simp [hg, hh], ?_⟩
  have e1 : (X - C α) * (g * h) = h * ((X - C α) * g) := by ring
  have e2 : (X - C α) * (g * h) = g * ((X - C α) * h) := by ring
  have hG' : aeval u ((X - C α) * (g * h)) G = 0 := by
    rw [e1, map_mul, Module.End.mul_apply, hG, map_zero]
  have hH' : aeval u ((X - C α) * (g * h)) H = 0 := by
    rw [e2, map_mul, Module.End.mul_apply, hH, map_zero]
  rw [map_add, hG', hH', add_zero]

/- English proof (translation)
Distinguish the cases in `hq : α ^ 2 - μ * α + c = 0`. Establish `hα : α ≠ 0`. Introduce and unpack `rfl`. Apply `hαc` to reduce the goal to its premises. Take the linear combination `(-1 : ℂ) * hq`.

Use `⟨X - C (c / α), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [eval_sub, eval_X, eval_C]`. Introduce `h0`. Apply `hαc` to reduce the goal to its premises. Clear denominators, using `at h0` for the nonvanishing conditions.

Take the linear combination `h0`. Establish `hμ : μ = α + c / α` using `by field_simp; linear_combination (-1 : ℂ) * hq`. Establish `e : (X - C α) * (X - C (c / α)) = X ^ 2 - C μ * X + C c`. Rewrite using `[hμ, C_add]`. Establish `: C c = C α * C (c / α)` using `by rw [← C_mul]; congr 1; field_simp`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h`. Use `⟨X ^ 2 - C μ * X + C c, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]`. Introduce `h0`. Apply `hq` to reduce the goal to its premises. Take the linear combination `h0`. Rewrite using `[map_mul, Module.End.mul_apply, h, map_zero]`.
-/
theorem good_of_quad (u : Module.End ℂ (ℍ → ℂ)) (α μ c : ℂ) (hαc : α ^ 2 ≠ c) (G : ℍ → ℂ)
    (h : aeval u (X ^ 2 - C μ * X + C c) G = 0) : Good u α G := by
  by_cases hq : α ^ 2 - μ * α + c = 0
  · have hα : α ≠ 0 := by
      rintro rfl; apply hαc; linear_combination (-1 : ℂ) * hq
    refine ⟨X - C (c / α), ?_, ?_⟩
    · simp only [eval_sub, eval_X, eval_C]
      intro h0
      apply hαc
      field_simp at h0
      linear_combination h0
    · have hμ : μ = α + c / α := by field_simp; linear_combination (-1 : ℂ) * hq
      have e : (X - C α) * (X - C (c / α)) = X ^ 2 - C μ * X + C c := by
        rw [hμ, C_add]
        have : C c = C α * C (c / α) := by rw [← C_mul]; congr 1; field_simp
        rw [this]; ring
      rw [e]; exact h
  · refine ⟨X ^ 2 - C μ * X + C c, ?_, ?_⟩
    · simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
      intro h0; apply hq; linear_combination h0
    · rw [map_mul, Module.End.mul_apply, h, map_zero]

/- English proof (translation)
Take `⟨g, hg, hk⟩` from `hG`. Establish `hcop : IsCoprime (X - C α) g`. Rewrite using `[(Polynomial.irreducible_X_sub_C α).coprime_iff_not_dvd, Polynomial.dvd_iff_isRoot]`. Conclude with `hg`. Take `⟨s, t, hst⟩` from `hcop.pow_left (m := n)`.

Establish `hlin : aeval u (X - C α) = u - α • 1`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Establish `hit : aeval u ((X - C α) ^ n) G = 0`. Rewrite using `[map_pow, hlin, Module.End.pow_apply]`. Use `h using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `F`. Simplify using the standard rewrite rules. Establish `key : X - C α = s * ((X - C α) * (X - C α) ^ n) + t * ((X - C α) * g)`. Take the linear combination `(-(X - C α)) * hst`. Establish `h1 : aeval u (X - C α) G = 0`.

Rewrite using `[key, map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, map_mul, Module.End.mul_apply, hit, map_zero, map_zero, hk, map_zero, add_zero]`. Rewrite `h1` using `[hlin]`. Simplify `h1` using `[sub_eq_zero]`.
-/
theorem eigen_of_good (u : Module.End ℂ (ℍ → ℂ)) (α : ℂ) (G : ℍ → ℂ) (hG : Good u α G) (n : ℕ)
    (h : (fun F => u F - α • F)^[n] G = 0) : u G = α • G := by
  obtain ⟨g, hg, hk⟩ := hG
  have hcop : IsCoprime (X - C α) g := by
    rw [(Polynomial.irreducible_X_sub_C α).coprime_iff_not_dvd, Polynomial.dvd_iff_isRoot]
    exact hg
  obtain ⟨s, t, hst⟩ := hcop.pow_left (m := n)
  have hlin : aeval u (X - C α) = u - α • 1 := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hit : aeval u ((X - C α) ^ n) G = 0 := by
    rw [map_pow, hlin, Module.End.pow_apply]
    convert h using 2
    funext F; simp
  have key : X - C α = s * ((X - C α) * (X - C α) ^ n) + t * ((X - C α) * g) := by
    linear_combination (-(X - C α)) * hst
  have h1 : aeval u (X - C α) G = 0 := by
    rw [key, map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply,
      map_mul, Module.End.mul_apply, hit, map_zero, map_zero, hk, map_zero, add_zero]
  rw [hlin] at h1
  simpa [sub_eq_zero] using h1

end GlobalTheory.OldSpace

namespace GlobalTheory.OldSpace

/- English proof (translation)
Unfold `GlobalTheory.Hk.lev`. Use `inf_eq_left.2 fun γ _ => ?_` and prove the remaining obligations. Rewrite using `[CongruenceSubgroup.Gamma0_mem]`. Conclude with `Subsingleton.elim _ _`.
-/
theorem lev_one (N : ℕ) : GlobalTheory.Hk.lev N 1 = CongruenceSubgroup.Gamma1 N := by
  unfold GlobalTheory.Hk.lev
  refine inf_eq_left.2 fun γ _ => ?_
  rw [CongruenceSubgroup.Gamma0_mem]
  exact Subsingleton.elim _ _

/- English proof (translation)
Introduce `N l k s hN hl hlN _ hs χ f hf`. Take `⟨-, -, hT, hD, -⟩` from `GlobalTheory.SlashUpperTriangularMatrices.bridge`. Establish `hN0 : 0 < N` using `by omega`. Establish `hlN' : ¬ l ∣ N * 1` using `by rwa [mul_one]`. Establish `hs' : GlobalTheory.Hk.IsDia N 1 l s` using `(hD N 1 l s).1 (by simpa using hs)`.

Establish `h1` using `GlobalTheory.T.heckeTOperatorExplicit_cuspForm N 1 l k s hN0 hl hlN' hs'`. Establish `h2` using `fun (d : ℤ) (ρ : SL(2, ℤ)) (hρ : GlobalTheory.Hk.IsDia N 1 d ρ) => GlobalTheory.T.hecke_operator_commutes_diamond N 1 l k d s ρ hN0 hl hlN' hs' hρ`. Rewrite `h1`, `h2` using `[lev_one]`. Take `⟨g, hg⟩` from `h1 f`. Rewrite `hg` using `[← hT _ _ _ _ hl.pos]`.

Use `⟨g, fun γ hγ => ?_, hg⟩` and prove the remaining obligations. Establish `hγ' : GlobalTheory.Hk.IsDia N 1 (mat γ 1 1) γ` using `(hD N 1 _ γ).1 ⟨by rwa [mul_one], rfl⟩`. Establish `h3 : GlobalTheory.Hk.heckeT k l s (⇑f ∣[(k : ℤ)] γ) = GlobalTheory.Hk.heckeT k l s ⇑f ∣[(k : ℤ)] γ` using `h2 _ γ hγ' (ModularFormClass.modularForm f)`. Rewrite `h3` using `[← hT _ _ _ _ hl.pos, ← hT _ _ _ _ hl.pos, hf γ hγ]`. Rewrite using `[hg, ← h3, tq_eq N k l hl.pos s χ hs _ (hasChi_smul _ hf), tq_eq N k l hl.pos s χ hs _ hf]`.

Express the relevant statement in the definitionally equal form `uL k l (_ • ⇑f) + χ (l : ZMod N) • vL k l hl.pos (_ • ⇑f) = _ • (uL k l ⇑f + χ (l : ZMod N) • vL k l hl.pos ⇑f)`. Rewrite using `[map_smul, map_smul]`. Use `module`.
-/
theorem hecke_stab : ∀ (N l k : ℕ) (s : SL(2, ℤ)), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → IsDiam N 1 (l : ZMod N) s →
  ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑g ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑g) ∧
      ⇑g = TqF (k : ℤ) l s ⇑f := by
  intro N l k s hN hl hlN _ hs χ f hf
  obtain ⟨-, -, hT, hD, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  have hN0 : 0 < N := by omega
  have hlN' : ¬ l ∣ N * 1 := by rwa [mul_one]
  have hs' : GlobalTheory.Hk.IsDia N 1 l s := (hD N 1 l s).1 (by simpa using hs)
  have h1 := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N 1 l k s hN0 hl hlN' hs'
  have h2 := fun (d : ℤ) (ρ : SL(2, ℤ)) (hρ : GlobalTheory.Hk.IsDia N 1 d ρ) =>
    GlobalTheory.T.hecke_operator_commutes_diamond N 1 l k d s ρ hN0 hl hlN' hs' hρ
  rw [lev_one] at h1 h2
  obtain ⟨g, hg⟩ := h1 f
  rw [← hT _ _ _ _ hl.pos] at hg
  refine ⟨g, fun γ hγ => ?_, hg⟩
  have hγ' : GlobalTheory.Hk.IsDia N 1 (mat γ 1 1) γ := (hD N 1 _ γ).1 ⟨by rwa [mul_one], rfl⟩
  have h3 : GlobalTheory.Hk.heckeT k l s (⇑f ∣[(k : ℤ)] γ) = GlobalTheory.Hk.heckeT k l s ⇑f ∣[(k : ℤ)] γ :=
    h2 _ γ hγ' (ModularFormClass.modularForm f)
  rw [← hT _ _ _ _ hl.pos, ← hT _ _ _ _ hl.pos, hf γ hγ] at h3
  rw [hg, ← h3, tq_eq N k l hl.pos s χ hs _ (hasChi_smul _ hf), tq_eq N k l hl.pos s χ hs _ hf]
  change uL k l (_ • ⇑f) + χ (l : ZMod N) • vL k l hl.pos (_ • ⇑f) =
    _ • (uL k l ⇑f + χ (l : ZMod N) • vL k l hl.pos ⇑f)
  rw [map_smul, map_smul]
  module

end GlobalTheory.OldSpace

namespace GlobalTheory.OldSpace

/- English proof (translation)
Simplify using `[pow_two, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply]`.
-/
theorem quad_apply (u : Module.End ℂ (ℍ → ℂ)) (μ c : ℂ) (G : ℍ → ℂ) :
    aeval u (X ^ 2 - C μ * X + C c) G = u (u G) - μ • u G + c • G := by
  simp [pow_two, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply]

/- English proof (translation)
Introduce `N l k hN hl hlN hk χ α hαc f₁ f₂ hf₁ hf₂`. Use `haveI : NeZero N := ⟨by omega⟩`. Establish `hl0 : 0 < l` using `hl.pos`. Take `⟨s, hs⟩` from `exists_diam N l ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)`. Establish `stab` using `hecke_stab N l k s hN hl hlN hk hs χ`.

Use `set W := chiSpace N (k : ℤ) χ with hWdef`. Use `set u := uL (k : ℤ) l with hudef`. Use `set v := vL (k : ℤ) l hl0 with hvdef`. Use `set T' : Module.End ℂ (ℍ → ℂ) := u + χ (l : ZMod N) • v with hT'def`. Establish `hT'eq : ∀ G ∈ W, T' G = TqF (k : ℤ) l s G`.

Introduce and unpack `_ ⟨f, rfl, hf⟩`. Rewrite using `[tq_eq N (k : ℤ) l hl0 s χ hs _ hf]`. Both sides reduce to the same expression. Establish `hTW : ∀ G ∈ W, T' G ∈ W`. Introduce and unpack `_ ⟨f, rfl, hf⟩`.

Take `⟨g, hg, hgeq⟩` from `stab f hf`. Rewrite using `[hT'eq _ ⟨f, rfl, hf⟩, ← hgeq]`. Conclude with `⟨g, rfl, hg⟩`. Set `T0 : Module.End ℂ W` to `T'.restrict hTW`. Establish `hT0 : ∀ x : W, ((T0 x : W) : ℍ → ℂ) = TqF (k : ℤ) l s (x : ℍ → ℂ)`.

Introduce `x`. Rewrite using `[← hT'eq _ x.2]`. Both sides reduce to the same expression. Use `haveI : FiniteDimensional ℂ W := finiteDimensional_chiSpace N k χ`. Establish `hiter : ∀ (μ : ℂ) (n : ℕ) (x : W), ((((T0 - μ • 1) ^ n) x : W) : ℍ → ℂ) = (fun F => TqF (k : ℤ) l s F - μ • F)^[n] (x : ℍ → ℂ)`.

Introduce `μ n`. Proceed by induction on `n with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `x`. Rewrite using `[pow_succ', Module.End.mul_apply, Function.iterate_succ_apply', ← ih]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub, Submodule.coe_smul, hT0]`. Establish `hss : ∀ μ, T0.maxGenEigenspace μ ≤ T0.eigenspace μ`. Introduce `μ x hx`.

Rewrite `hx` using `[Module.End.mem_maxGenEigenspace]`. Take `⟨n, hn⟩` from `hx`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Take `⟨f, hfx, hf⟩` from `x.2`. Establish `h1 : (fun F => TqF (k : ℤ) l s F - μ • F)^[n] ⇑f = 0`.

Rewrite using `[hfx, ← hiter, hn]`. Both sides reduce to the same expression. Establish `h2` using `GlobalTheory.T.heckeTq_semisimple_cuspForms_gamma1 N k l s hN hk hl hlN hs f μ n h1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hT0, Submodule.coe_smul, ← hfx, h2]`.

Establish `htop : ⨆ μ, T0.eigenspace μ = ⊤` using `eq_top_iff.2 ((Module.End.iSup_maxGenEigenspace_eq_top T0).ge.trans (iSup_mono hss))`. Use `set Lc : ℂ := (l : ℂ) ^ ((k : ℤ) - 1) with hLc`. Establish `hcL : χ (l : ZMod N) * (l : ℂ) ^ (k - 1) = χ (l : ZMod N) * Lc`. Rewrite using `[hLc, show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]`. Establish `hαc' : α ^ 2 ≠ χ (l : ZMod N) * Lc` using `by rw [← hcL]; exact hαc`.

Establish `huv : ∀ G ∈ W, u (v G) = Lc • G`. Introduce and unpack `_ ⟨f, rfl, _⟩`. Conclude with `ul_slash_dg N (k : ℤ) l hl0 f`. Establish `hgoodW : ∀ x : W, Good u α (x : ℍ → ℂ) ∧ Good u α (v x)`. Introduce `x`.

Establish `hx : x ∈ ⨆ μ, T0.eigenspace μ` using `by rw [htop]; trivial`. Use `Submodule.iSup_induction (fun μ => T0.eigenspace μ) (motive := fun y : W => Good u α (y : ℍ → ℂ) ∧ Good u α (v y)) hx ?_ ?_ ?_` and prove the remaining obligations. Introduce `μ y hy`. Rewrite `hy` using `[Module.End.mem_eigenspace_iff]`. Establish `hy' : u y + χ (l : ZMod N) • v y = μ • (y : ℍ → ℂ)`.

Use `congrArg Subtype.val hy` as an intermediate fact. Conclude with `this`. Establish `hvy` using `huv _ y.2`. Establish `hu1 : u y = μ • (y : ℍ → ℂ) - χ (l : ZMod N) • v y` using `by rw [← hy']; abel`. Prove the components needed by the constructor for the conclusion.

Apply `good_of_quad u α μ _ hαc'` to reduce the goal to its premises. Rewrite using `[quad_apply, hu1, map_sub, map_smul, map_smul, hvy, hu1]`. Use `module`. Apply `good_of_quad u α μ _ hαc'` to reduce the goal to its premises. Rewrite using `[quad_apply, hvy, map_smul, hu1]`.

Use `module`. Simplify using `only [ZeroMemClass.coe_zero, map_zero]`. Conclude with `⟨good_zero u α, good_zero u α⟩`. Introduce `a b ha hb`. Simplify using `only [Submodule.coe_add, map_add]`.

Conclude with `⟨good_add ha.1 hb.1, good_add ha.2 hb.2⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨g, hg, hgeq⟩` from `stab f₁ hf₁`. Use `⟨g + Lc • f₂, (-(χ (l : ZMod N))) • f₁, hasChi_add hg (hasChi_smul Lc hf₂), hasChi_smul _ hf₁, ?_⟩` and prove the remaining obligations. Establish `ht` using `tq_eq N (k : ℤ) l hl0 s χ hs _ hf₁`.

Rewrite `ht` using `[← hgeq]`. Express the relevant statement in the definitionally equal form `u (⇑f₁ + v ⇑f₂) = ⇑g + Lc • ⇑f₂ + v ((-(χ (l : ZMod N))) • ⇑f₁)`. Rewrite using `[map_add, huv _ ⟨f₂, rfl, hf₂⟩, map_smul, ht]`. Express the relevant statement in the definitionally equal form `u ⇑f₁ + Lc • ⇑f₂ = u ⇑f₁ + χ (l : ZMod N) • v ⇑f₁ + Lc • ⇑f₂ + -χ (l : ZMod N) • v ⇑f₁`. Use `module`.

Introduce `n hn`. Establish `hG : Good u α (⇑f₁ + v ⇑f₂)` using `good_add (hgoodW ⟨_, f₁, rfl, hf₁⟩).1 (hgoodW ⟨_, f₂, rfl, hf₂⟩).2`. Conclude with `eigen_of_good u α _ hG n hn`.
-/
theorem ul_oldSpace : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (α : ℂ), α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 1) →
  ∀ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) →
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) →
    (∃ g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑g₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑g₁) ∧
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑g₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑g₂) ∧
      UlF (k : ℤ) l (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = ⇑g₁ + ⇑g₂ ∣[(k : ℤ)] toGL (dg l 1)) ∧
    ∀ n : ℕ, (fun F => UlF (k : ℤ) l F - α • F)^[n] (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = 0 →
      UlF (k : ℤ) l (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = α • (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) := by
  intro N l k hN hl hlN hk χ α hαc f₁ f₂ hf₁ hf₂
  haveI : NeZero N := ⟨by omega⟩
  have hl0 : 0 < l := hl.pos
  obtain ⟨s, hs⟩ := exists_diam N l ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  have stab := hecke_stab N l k s hN hl hlN hk hs χ
  set W := chiSpace N (k : ℤ) χ with hWdef
  set u := uL (k : ℤ) l with hudef
  set v := vL (k : ℤ) l hl0 with hvdef
  set T' : Module.End ℂ (ℍ → ℂ) := u + χ (l : ZMod N) • v with hT'def
  have hT'eq : ∀ G ∈ W, T' G = TqF (k : ℤ) l s G := by
    rintro _ ⟨f, rfl, hf⟩
    rw [tq_eq N (k : ℤ) l hl0 s χ hs _ hf]
    rfl
  have hTW : ∀ G ∈ W, T' G ∈ W := by
    rintro _ ⟨f, rfl, hf⟩
    obtain ⟨g, hg, hgeq⟩ := stab f hf
    rw [hT'eq _ ⟨f, rfl, hf⟩, ← hgeq]
    exact ⟨g, rfl, hg⟩
  let T0 : Module.End ℂ W := T'.restrict hTW
  have hT0 : ∀ x : W, ((T0 x : W) : ℍ → ℂ) = TqF (k : ℤ) l s (x : ℍ → ℂ) := by
    intro x
    rw [← hT'eq _ x.2]
    rfl
  haveI : FiniteDimensional ℂ W := finiteDimensional_chiSpace N k χ
  have hiter : ∀ (μ : ℂ) (n : ℕ) (x : W),
      ((((T0 - μ • 1) ^ n) x : W) : ℍ → ℂ) = (fun F => TqF (k : ℤ) l s F - μ • F)^[n] (x : ℍ → ℂ) := by
    intro μ n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply', ← ih]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub,
        Submodule.coe_smul, hT0]
  have hss : ∀ μ, T0.maxGenEigenspace μ ≤ T0.eigenspace μ := by
    intro μ x hx
    rw [Module.End.mem_maxGenEigenspace] at hx
    obtain ⟨n, hn⟩ := hx
    rw [Module.End.mem_eigenspace_iff]
    obtain ⟨f, hfx, hf⟩ := x.2
    have h1 : (fun F => TqF (k : ℤ) l s F - μ • F)^[n] ⇑f = 0 := by
      rw [hfx, ← hiter, hn]; rfl
    have h2 := GlobalTheory.T.heckeTq_semisimple_cuspForms_gamma1 N k l s hN hk hl hlN hs f μ n h1
    apply Subtype.ext
    rw [hT0, Submodule.coe_smul, ← hfx, h2]
  have htop : ⨆ μ, T0.eigenspace μ = ⊤ :=
    eq_top_iff.2 ((Module.End.iSup_maxGenEigenspace_eq_top T0).ge.trans (iSup_mono hss))
  set Lc : ℂ := (l : ℂ) ^ ((k : ℤ) - 1) with hLc
  have hcL : χ (l : ZMod N) * (l : ℂ) ^ (k - 1) = χ (l : ZMod N) * Lc := by
    rw [hLc, show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have hαc' : α ^ 2 ≠ χ (l : ZMod N) * Lc := by rw [← hcL]; exact hαc
  have huv : ∀ G ∈ W, u (v G) = Lc • G := by
    rintro _ ⟨f, rfl, _⟩
    exact ul_slash_dg N (k : ℤ) l hl0 f
  have hgoodW : ∀ x : W, Good u α (x : ℍ → ℂ) ∧ Good u α (v x) := by
    intro x
    have hx : x ∈ ⨆ μ, T0.eigenspace μ := by rw [htop]; trivial
    refine Submodule.iSup_induction (fun μ => T0.eigenspace μ)
      (motive := fun y : W => Good u α (y : ℍ → ℂ) ∧ Good u α (v y)) hx ?_ ?_ ?_
    · intro μ y hy
      rw [Module.End.mem_eigenspace_iff] at hy
      have hy' : u y + χ (l : ZMod N) • v y = μ • (y : ℍ → ℂ) := by
        have := congrArg Subtype.val hy
        exact this
      have hvy := huv _ y.2
      have hu1 : u y = μ • (y : ℍ → ℂ) - χ (l : ZMod N) • v y := by rw [← hy']; abel
      constructor
      · apply good_of_quad u α μ _ hαc'
        rw [quad_apply, hu1, map_sub, map_smul, map_smul, hvy, hu1]
        module
      · apply good_of_quad u α μ _ hαc'
        rw [quad_apply, hvy, map_smul, hu1]
        module
    · simp only [ZeroMemClass.coe_zero, map_zero]
      exact ⟨good_zero u α, good_zero u α⟩
    · intro a b ha hb
      simp only [Submodule.coe_add, map_add]
      exact ⟨good_add ha.1 hb.1, good_add ha.2 hb.2⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg, hgeq⟩ := stab f₁ hf₁
    refine ⟨g + Lc • f₂, (-(χ (l : ZMod N))) • f₁, hasChi_add hg (hasChi_smul Lc hf₂),
      hasChi_smul _ hf₁, ?_⟩
    have ht := tq_eq N (k : ℤ) l hl0 s χ hs _ hf₁
    rw [← hgeq] at ht
    change u (⇑f₁ + v ⇑f₂) = ⇑g + Lc • ⇑f₂ + v ((-(χ (l : ZMod N))) • ⇑f₁)
    rw [map_add, huv _ ⟨f₂, rfl, hf₂⟩, map_smul, ht]
    change u ⇑f₁ + Lc • ⇑f₂ = u ⇑f₁ + χ (l : ZMod N) • v ⇑f₁ + Lc • ⇑f₂ + -χ (l : ZMod N) • v ⇑f₁
    module
  · intro n hn
    have hG : Good u α (⇑f₁ + v ⇑f₂) :=
      good_add (hgoodW ⟨_, f₁, rfl, hf₁⟩).1 (hgoodW ⟨_, f₂, rfl, hf₂⟩).2
    exact eigen_of_good u α _ hG n hn

end GlobalTheory.OldSpace
