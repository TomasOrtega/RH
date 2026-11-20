import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section
namespace GlobalTheory.SlashUpperTriangularMatrices

/- English proof (translation)
Unfold `toGL`. Rewrite using `[dif_neg h]`. Both sides reduce to the same expression.
-/
theorem toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL; rw [dif_neg h]; rfl

/- English proof (translation)
Establish `hdet : (!![a, b; 0, d]).det ≠ 0`. Rewrite using `[Matrix.det_fin_two_of]`. Simplify using `[ha.ne', hd.ne']`. Establish `hv` using `toGL_val _ hdet`. Use `set G := toGL !![a, b; 0, d]`.

Establish `e00 : G 0 0 = a` using `by simp [G, hv]`. Establish `e01 : G 0 1 = b` using `by simp [G, hv]`. Establish `e10 : G 1 0 = 0` using `by simp [G, hv]`. Establish `e11 : G 1 1 = d` using `by simp [G, hv]`. Establish `hG : G.det.val = (a : ℝ) * d`.

Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e00, e01, e10, e11]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < G.det.val` using `by rw [hG]; positivity`. Establish `hsm : G • τ = ofComplex (((a : ℂ) * τ + b) / d)`. Rewrite using `[← ofComplex_apply (G • τ), coe_smul_of_det_pos hpos]`.

Simplify using `[num, denom, e00, e01, e10, e11]`. Rewrite using `[ModularForm.slash_apply, hsm, σ, if_pos hpos, hG]`. Establish `hden : denom G τ = d` using `by simp [denom, e10, e11]`. Rewrite using `[hden, abs_of_pos (by positivity)]`. Simplify using the standard rewrite rules.
-/
theorem slash_upper (k : ℤ) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toGL !![a, b; 0, d]) τ =
      f (ofComplex (((a : ℂ) * τ + b) / d)) * ((a : ℂ) * d) ^ (k - 1) * (d : ℂ) ^ (-k) := by
  have hdet : (!![a, b; 0, d]).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [ha.ne', hd.ne']
  have hv := toGL_val _ hdet
  set G := toGL !![a, b; 0, d]
  have e00 : G 0 0 = a := by simp [G, hv]
  have e01 : G 0 1 = b := by simp [G, hv]
  have e10 : G 1 0 = 0 := by simp [G, hv]
  have e11 : G 1 1 = d := by simp [G, hv]
  have hG : G.det.val = (a : ℝ) * d := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e00, e01, e10, e11]; ring
  have hpos : 0 < G.det.val := by rw [hG]; positivity
  have hsm : G • τ = ofComplex (((a : ℂ) * τ + b) / d) := by
    rw [← ofComplex_apply (G • τ), coe_smul_of_det_pos hpos]
    simp [num, denom, e00, e01, e10, e11]
  rw [ModularForm.slash_apply, hsm, σ, if_pos hpos, hG]
  have hden : denom G τ = d := by simp [denom, e10, e11]
  rw [hden, abs_of_pos (by positivity)]
  simp

/- English proof (translation)
Rewrite using `[← zpow_add₀ hx]`. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules.
-/
theorem pow_pair (x : ℂ) (hx : x ≠ 0) (k : ℤ) : x ^ (k - 1) * x ^ (-k) = x⁻¹ := by
  rw [← zpow_add₀ hx]; ring_nf; simp

/- English proof (translation)
Establish `h : (mat σ).det ≠ 0` using `by simp [mat]`. Use extensionality with `i j`. Rewrite using `[toGL_val _ h]`. Simplify using `[mat]`.
-/
theorem toGL_SL (σ : SL(2, ℤ)) : toGL (mat σ) = (σ : GL (Fin 2) ℝ) := by
  have h : (mat σ).det ≠ 0 := by simp [mat]
  ext i j
  rw [toGL_val _ h]
  simp [mat]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `only [UlF, hkF, Finset.sum_apply, ulFam]`. Establish `hl' : (0 : ℤ) < l` using `by exact_mod_cast hl`. Simplify using `only [fun j : Fin l => slash_upper k 1 (j : ℤ) l one_pos hl' f τ]`. Rewrite using `[GlobalTheory.Hk.uOp, Finset.mul_sum]`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => f (ofComplex (((((1 : ℤ)) : ℂ) * τ + ((j : ℤ) : ℂ)) / ((l : ℤ) : ℂ))) * (((1 : ℤ) : ℂ) * ((l : ℤ) : ℂ)) ^ (k - 1) * ((l : ℤ) : ℂ) ^ (-k)) l]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hx : ((l : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hl.ne'`. Use `push_cast`. Rewrite using `[one_mul, one_mul, mul_assoc, pow_pair _ hx, mul_comm]`.
-/
theorem ul_eq (k : ℤ) (l : ℕ) (f : ℍ → ℂ) (hl : 0 < l) : UlF k l f = GlobalTheory.Hk.uOp l f := by
  funext τ
  simp only [UlF, hkF, Finset.sum_apply, ulFam]
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  simp only [fun j : Fin l => slash_upper k 1 (j : ℤ) l one_pos hl' f τ]
  rw [GlobalTheory.Hk.uOp, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => f (ofComplex (((((1 : ℤ)) : ℂ) * τ + ((j : ℤ) : ℂ)) / ((l : ℤ) : ℂ))) *
      (((1 : ℤ) : ℂ) * ((l : ℤ) : ℂ)) ^ (k - 1) * ((l : ℤ) : ℂ) ^ (-k)) l]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : ((l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  rw [one_mul, one_mul, mul_assoc, pow_pair _ hx, mul_comm]

/- English proof (translation)
Simplify using `[DdF, hkF, GlobalTheory.Hk.dia, toGL_SL, ModularForm.SL_slash]`.
-/
theorem dd_eq (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : DdF k σ f = GlobalTheory.Hk.dia k σ f := by
  simp [DdF, hkF, GlobalTheory.Hk.dia, toGL_SL, ModularForm.SL_slash]

/- English proof (translation)
Establish `hgh : (g * h).det ≠ 0` using `by rw [Matrix.det_mul]; exact mul_ne_zero hg hh`. Use extensionality with `i j`. Rewrite using `[Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh, RingHom.map_mul]`.
-/
theorem toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hg hh
  ext i j
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh, RingHom.map_mul]

/- English proof (translation)
Establish `hsplit : TqF k q σ f = UlF k q f + f ∣[k] toGL (mat σ * dg q 1)`. Establish `e : ∀ i : Fin q, tqFam q σ i.castSucc = ulFam q i` using `fun i => by`. Rewrite using `[tqFam, if_pos (by simp)]; rfl`. Establish `e2 : tqFam q σ (Fin.last q) = mat σ * dg q 1`. Rewrite using `[tqFam, if_neg (by simp)]`.

Simplify using `only [TqF, UlF, hkF]`. Rewrite using `[Fin.sum_univ_castSucc, e2]`. Simplify using `only [e]`. Establish `hq' : (0 : ℤ) < q` using `by exact_mod_cast hq`. Establish `hdg : (dg q 1).det ≠ 0` using `by simp [dg, Matrix.det_fin_two_of, hq.ne']`.

Establish `hσ : (mat σ).det ≠ 0` using `by simp [mat]`. Rewrite using `[hsplit, ul_eq k q f hq, toGL_mul _ _ hσ hdg, SlashAction.slash_mul, toGL_SL, ← ModularForm.SL_slash, GlobalTheory.Hk.heckeT]`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `congr 1`.

Rewrite using `[dg, slash_upper k q 0 1 hq' one_pos, GlobalTheory.Hk.vOp]`. Use `push_cast`. Simplify using `[mul_comm]`.
-/
theorem tq_eq (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) (hq : 0 < q) :
    TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f := by
  have hsplit : TqF k q σ f = UlF k q f + f ∣[k] toGL (mat σ * dg q 1) := by
    have e : ∀ i : Fin q, tqFam q σ i.castSucc = ulFam q i := fun i => by
      rw [tqFam, if_pos (by simp)]; rfl
    have e2 : tqFam q σ (Fin.last q) = mat σ * dg q 1 := by
      rw [tqFam, if_neg (by simp)]
    simp only [TqF, UlF, hkF]
    rw [Fin.sum_univ_castSucc, e2]
    simp only [e]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hdg : (dg q 1).det ≠ 0 := by simp [dg, Matrix.det_fin_two_of, hq.ne']
  have hσ : (mat σ).det ≠ 0 := by simp [mat]
  rw [hsplit, ul_eq k q f hq, toGL_mul _ _ hσ hdg, SlashAction.slash_mul, toGL_SL, ← ModularForm.SL_slash,
    GlobalTheory.Hk.heckeT]
  funext τ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [dg, slash_upper k q 0 1 hq' one_pos, GlobalTheory.Hk.vOp]
  push_cast
  simp [mul_comm]

/- English proof (translation)
Simplify using `[IsDiam, GlobalTheory.Hk.IsDia, CongruenceSubgroup.Gamma0_mem, mat]`.
-/
theorem dia_iff (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ := by
  simp [IsDiam, GlobalTheory.Hk.IsDia, CongruenceSubgroup.Gamma0_mem, mat]

end GlobalTheory.SlashUpperTriangularMatrices

namespace GlobalTheory.SlashUpperTriangularMatrices

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k l f hl => ul_eq k l f hl, dd_eq, fun k q σ f hq => tq_eq k q σ f hq, dia_iff, fun _ _ => rfl⟩`.
-/
theorem bridge : (∀ (k : ℤ) (l : ℕ) (f : ℍ → ℂ), 0 < l → UlF k l f = GlobalTheory.Hk.uOp l f) ∧
  (∀ (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), DdF k σ f = GlobalTheory.Hk.dia k σ f) ∧
  (∀ (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f) ∧
  (∀ (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)), IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ) ∧
  ∀ N l : ℕ, Lev N l = GlobalTheory.Hk.lev N l :=
  ⟨fun k l f hl => ul_eq k l f hl, dd_eq, fun k q σ f hq => tq_eq k q σ f hq, dia_iff, fun _ _ => rfl⟩

end GlobalTheory.SlashUpperTriangularMatrices
