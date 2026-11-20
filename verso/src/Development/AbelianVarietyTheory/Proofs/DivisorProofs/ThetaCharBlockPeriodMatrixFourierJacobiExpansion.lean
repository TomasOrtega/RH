import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMulDotProductLeOfIsCompactThetaDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FJ

/- English proof (translation)
Simplify using `only [dotProduct, zP, tP]`. Rewrite using `[← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]`.
-/
theorem dot_split {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) (u v : Fin g → ℂ) :
    u ⬝ᵥ v = zP σ u ⬝ᵥ zP σ v + tP σ u ⬝ᵥ tP σ v := by
  simp only [dotProduct, zP, tP]
  rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]

/- English proof (translation)
Rewrite using `[dot_split σ]`. Establish `h1 : zP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = A *ᵥ zP σ v + B *ᵥ tP σ v`. Use function extensionality and compare the values at `i`. Simplify using `only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]`. Rewrite using `[← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]`.

Simplify using the standard rewrite rules. Establish `h2 : tP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = Bᵀ *ᵥ zP σ v + D *ᵥ tP σ v`. Use function extensionality and compare the values at `i`. Simplify using `only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]`. Rewrite using `[← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, h2, dotProduct_add, dotProduct_add, mulVec_transpose, dotProduct_comm (tP σ v) (vecMul _ _), ← dotProduct_mulVec]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_full {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) (A : Matrix (Fin g') (Fin g') ℂ)
    (B : Matrix (Fin g') (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ) (v : Fin g → ℂ) :
    v ⬝ᵥ (Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v =
      zP σ v ⬝ᵥ A *ᵥ zP σ v + 2 * (zP σ v ⬝ᵥ B *ᵥ tP σ v) + tP σ v ⬝ᵥ D *ᵥ tP σ v := by
  rw [dot_split σ]
  have h1 : zP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = A *ᵥ zP σ v + B *ᵥ tP σ v := by
    funext i
    simp only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]
    rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
    simp
  have h2 : tP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = Bᵀ *ᵥ zP σ v + D *ᵥ tP σ v := by
    funext i
    simp only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]
    rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
    simp
  rw [h1, h2, dotProduct_add, dotProduct_add, mulVec_transpose, dotProduct_comm (tP σ v) (vecMul _ _),
    ← dotProduct_mulVec]
  ring

def thT {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b z : Fin k → ℂ) (n : Fin k → ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
    2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (z + b)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem thetaChar_eq_tsum {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b z : Fin k → ℂ) :
    thetaChar τ a b z = ∑' n, thT τ a b z n := rfl

/- English proof (translation)
Establish `hd : τ ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin k)` using `hτ.add hτ.transpose`. Use `(GlobalTheory.thetaSummable_holds (Fin k) (fun i => (a i).re) 0 (z + b) τ hd).congr fun n => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hs : ReciprocityTheory.PTheta.shiftVec (fun i => (a i).re) n = (fun i => (n i : ℂ)) + a`. Use function extensionality and compare the values at `fun i => by simp [ReciprocityTheory.PTheta.shiftVec, ha i]`.

Establish `h0 : ReciprocityTheory.PTheta.ofRealVec (0 : Fin k → ℝ) = 0` using `funext fun i => by simp [ReciprocityTheory.PTheta.ofRealVec]`. Simplify using `only [ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC, thT]`. Rewrite using `[hs, h0, add_zero]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem summable_thT {k : ℕ} {τ : Matrix (Fin k) (Fin k) ℂ} (hτ : (τ.map Complex.im).PosDef) {a : Fin k → ℂ}
    (ha : ∀ i, ((a i).re : ℂ) = a i) (b z : Fin k → ℂ) : Summable fun n => ‖thT τ a b z n‖ := by
  have hd : τ ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin k) := hτ.add hτ.transpose
  refine (GlobalTheory.thetaSummable_holds (Fin k) (fun i => (a i).re) 0 (z + b) τ hd).congr fun n => ?_
  congr 1
  have hs : ReciprocityTheory.PTheta.shiftVec (fun i => (a i).re) n = (fun i => (n i : ℂ)) + a :=
    funext fun i => by simp [ReciprocityTheory.PTheta.shiftVec, ha i]
  have h0 : ReciprocityTheory.PTheta.ofRealVec (0 : Fin k → ℝ) = 0 := funext fun i => by simp [ReciprocityTheory.PTheta.ofRealVec]
  simp only [ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC, thT]
  rw [hs, h0, add_zero]
  congr 1
  ring

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

/- English proof (translation)
Establish `hz : zP σ ((fun i => (n i : ℂ)) + d.aF σ) = (fun i => ((zP σ n i : ℤ) : ℂ)) + d.a`. Use function extensionality and compare the values at `i`. Simplify using `[zP, CD.aF]`. Establish `ht : tP σ ((fun i => (n i : ℂ)) + d.aF σ) = cv (tP σ n)`. Use function extensionality and compare the values at `i`.

Simplify using `[tP, CD.aF, cv]`. Establish `hz' : zP σ (Z + d.bF σ) = zP σ Z + d.b`. Use function extensionality and compare the values at `i`. Simplify using `[zP, CD.bF]`. Establish `ht' : tP σ (Z + d.bF σ) = tP σ Z + d.b2`.

Use function extensionality and compare the values at `i`. Simplify using `[tP, CD.bF]`. Unfold `thT CD.full`. Rewrite using `[quad_full, dot_split σ _ (Z + d.bF σ), hz, ht, hz', ht', ← Complex.exp_add]`. Use `congr 1`.

Simplify using `only [dotProduct_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thT_full (S : Matrix (Fin r) (Fin r) ℂ) (Z : Fin g → ℂ) (n : Fin g → ℤ) :
    thT (d.full σ S) (d.aF σ) (d.bF σ) Z n =
      Complex.exp (Real.pi * Complex.I * (cv (tP σ n) ⬝ᵥ (d.t22 + S) *ᵥ cv (tP σ n)) +
        2 * Real.pi * Complex.I * (cv (tP σ n) ⬝ᵥ (tP σ Z + d.b2))) *
      thT d.τ d.a d.b (zP σ Z + d.t12 *ᵥ cv (tP σ n)) (zP σ n) := by
  have hz : zP σ ((fun i => (n i : ℂ)) + d.aF σ) = (fun i => ((zP σ n i : ℤ) : ℂ)) + d.a := by
    funext i; simp [zP, CD.aF]
  have ht : tP σ ((fun i => (n i : ℂ)) + d.aF σ) = cv (tP σ n) := by
    funext i; simp [tP, CD.aF, cv]
  have hz' : zP σ (Z + d.bF σ) = zP σ Z + d.b := by
    funext i; simp [zP, CD.bF]
  have ht' : tP σ (Z + d.bF σ) = tP σ Z + d.b2 := by
    funext i; simp [tP, CD.bF]
  unfold thT CD.full
  rw [quad_full, dot_split σ _ (Z + d.bF σ), hz, ht, hz', ht', ← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

end GlobalTheory.MBLow.Cl.FJ

open GlobalTheory.MBLow.Cl.FJ in

/- English proof (translation)
Introduce `N g' r g bX d σ S _ hpos Z`. Set `e : (Fin g → ℤ) ≃ (Fin r → ℤ) × (Fin g' → ℤ)` to `{ toFun := fun n => (tP σ n, zP σ n) invFun := fun p j => Sum.elim p.2 p.1 (σ j) left_inv := fun n => by`. Use function extensionality and compare the values at `j`. Break down `h : σ j with i | l` into its components or cases. Simplify using `only [h, Sum.elim_inl, zP]`.

Rewrite using `[σ.symm_apply_eq.mpr h.symm]`. Simplify using `only [h, Sum.elim_inr, tP]`. Rewrite using `[σ.symm_apply_eq.mpr h.symm]`. Apply the tactic sequence `right_inv := fun p => by ext <;> simp [zP, tP] }`. Establish `haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j`.

Introduce `j`. Simplify using `only [CD.aF]`. Break down `σ j with i | l` into its components or cases. Apply the tactic sequence `rcases d.ha i with h | h <;> simp [h]`. Simplify using the standard rewrite rules.

Set `F : (Fin r → ℤ) × (Fin g' → ℤ) → ℂ` to `fun p => thT (d.full σ S) (d.aF σ) (d.bF σ) Z (e.symm p)`. Establish `hF : Summable fun p => ‖F p‖` using `(e.symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) Z n‖)).mpr (summable_thT hpos haF (d.bF σ) Z)`. Establish `hFc : Summable F` using `hF.of_norm`. Establish `hkey : ∀ χ, d.fj σ S χ Z = ∑' m, F (bX.equivFun χ, m)`. Introduce `χ`.

Establish `hcv : cv (bX.equivFun χ) = co bX χ`. Use function extensionality and compare the values at `l`. Simplify using `[cv, co, Module.Basis.equivFun_apply]`. Establish `hsymm : ∀ p, e (e.symm p) = p` using `e.apply_symm_apply`. Simplify using `only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left, F]`.

Use `congr 1`. Use function extensionality and compare the values at `m`. Establish `h1 : tP σ (e.symm (bX.equivFun χ, m)) = bX.equivFun χ` using `congrArg Prod.fst (hsymm (bX.equivFun χ, m))`. Establish `h2 : zP σ (e.symm (bX.equivFun χ, m)) = m` using `congrArg Prod.snd (hsymm (bX.equivFun χ, m))`. Rewrite using `[thT_full, h1, h2, hcv]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `((hF.prod).comp_injective bX.equivFun.injective).of_nonneg_of_le (fun _ => norm_nonneg _) fun χ => ?_` and prove the remaining obligations. Rewrite using `[hkey χ]`. Conclude with `norm_tsum_le_tsum_norm (hF.prod_factor _)`. Establish `hre` using `bX.equivFun.toEquiv.tsum_eq (fun k => ∑' m, F (k, m))`.

Simplify using `only [LinearEquiv.coe_toEquiv] at hre`. Rewrite using `[tsum_congr hkey, hre, ← hFc.tsum_prod, thetaChar_eq_tsum, ← e.symm.tsum_eq]`.
-/
theorem GlobalTheory.MBLow.Cl.fj_expansion : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm →
    ((d.full σ S).map Complex.im).PosDef → ∀ Z, (Summable fun χ => ‖d.fj σ S χ Z‖) ∧
      ∑' χ, d.fj σ S χ Z = thetaChar (d.full σ S) (d.aF σ) (d.bF σ) Z := by
  intro N g' r g bX d σ S _ hpos Z
  let e : (Fin g → ℤ) ≃ (Fin r → ℤ) × (Fin g' → ℤ) :=
    { toFun := fun n => (tP σ n, zP σ n)
      invFun := fun p j => Sum.elim p.2 p.1 (σ j)
      left_inv := fun n => by
        funext j
        rcases h : σ j with i | l
        · simp only [h, Sum.elim_inl, zP]; rw [σ.symm_apply_eq.mpr h.symm]
        · simp only [h, Sum.elim_inr, tP]; rw [σ.symm_apply_eq.mpr h.symm]
      right_inv := fun p => by ext <;> simp [zP, tP] }
  have haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j := by
    intro j
    simp only [CD.aF]
    rcases σ j with i | l
    · rcases d.ha i with h | h <;> simp [h]
    · simp
  let F : (Fin r → ℤ) × (Fin g' → ℤ) → ℂ := fun p => thT (d.full σ S) (d.aF σ) (d.bF σ) Z (e.symm p)
  have hF : Summable fun p => ‖F p‖ :=
    (e.symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) Z n‖)).mpr
      (summable_thT hpos haF (d.bF σ) Z)
  have hFc : Summable F := hF.of_norm
  have hkey : ∀ χ, d.fj σ S χ Z = ∑' m, F (bX.equivFun χ, m) := by
    intro χ
    have hcv : cv (bX.equivFun χ) = co bX χ := by
      funext l; simp [cv, co, Module.Basis.equivFun_apply]
    have hsymm : ∀ p, e (e.symm p) = p := e.apply_symm_apply
    simp only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left, F]
    congr 1
    funext m
    have h1 : tP σ (e.symm (bX.equivFun χ, m)) = bX.equivFun χ := congrArg Prod.fst (hsymm (bX.equivFun χ, m))
    have h2 : zP σ (e.symm (bX.equivFun χ, m)) = m := congrArg Prod.snd (hsymm (bX.equivFun χ, m))
    rw [thT_full, h1, h2, hcv]
  refine ⟨?_, ?_⟩
  · refine ((hF.prod).comp_injective bX.equivFun.injective).of_nonneg_of_le (fun _ => norm_nonneg _) fun χ => ?_
    rw [hkey χ]
    exact norm_tsum_le_tsum_norm (hF.prod_factor _)
  · have hre := bX.equivFun.toEquiv.tsum_eq (fun k => ∑' m, F (k, m))
    simp only [LinearEquiv.coe_toEquiv] at hre
    rw [tsum_congr hkey, hre, ← hFc.tsum_prod, thetaChar_eq_tsum, ← e.symm.tsum_eq]
