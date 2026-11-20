import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

open GlobalTheory.HolRead GlobalTheory.HolRead.AdExt GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

/- English proof (translation)
Establish `hxi : x * x⁻¹ = 1` using `Matrix.mul_nonsing_inv x hx`. Establish `hix : x⁻¹ * x = 1` using `Matrix.nonsing_inv_mul x hx`. Establish `hxh : ∀ M : Matrix (Fin n) (Fin n) ℂ, xᴴ * (x⁻¹ᴴ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ← conjTranspose_mul, hix, conjTranspose_one, Matrix.one_mul]`. Establish `hGi : G⁻¹ = x * S * xᴴ`.

Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hxi, Matrix.mul_one]`. Use `_ = 1 := by rw [h, Matrix.mul_assoc x S S, hS, Matrix.mul_one, hxi]`. Establish `hG : G = x⁻¹ᴴ * S * x⁻¹`.

Rewrite using `[← h]`. Simplify using `only [Matrix.mul_assoc, hxi, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, ← conjTranspose_mul, hxi, conjTranspose_one, Matrix.one_mul]`. Rewrite using `[hGi, hG]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, hxh]`.
-/
theorem conj_frame_eq {n : ℕ} {G S x : Matrix (Fin n) (Fin n) ℂ} (hd : IsUnit G.det) (hx : IsUnit x.det)
    (h : xᴴ * G * x = S) (hS : S * S = 1) (A : Matrix (Fin n) (Fin n) ℂ) :
    G⁻¹ * (x * A * x⁻¹)ᴴ * G = x * (S * Aᴴ * S) * x⁻¹ := by
  have hxi : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x hx
  have hix : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul x hx
  have hxh : ∀ M : Matrix (Fin n) (Fin n) ℂ, xᴴ * (x⁻¹ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hix, conjTranspose_one, Matrix.one_mul]
  have hGi : G⁻¹ = x * S * xᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    calc x * S * xᴴ * G = x * S * (xᴴ * G * x) * x⁻¹ := by
          simp only [Matrix.mul_assoc, hxi, Matrix.mul_one]
      _ = 1 := by rw [h, Matrix.mul_assoc x S S, hS, Matrix.mul_one, hxi]
  have hG : G = x⁻¹ᴴ * S * x⁻¹ := by
    rw [← h]
    simp only [Matrix.mul_assoc, hxi, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hxi, conjTranspose_one, Matrix.one_mul]
  rw [hGi, hG]
  simp only [conjTranspose_mul, Matrix.mul_assoc, hxh]

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sgn_mul_self (p a : ℕ) : (sgn p a : ℝ) * sgn p a = 1 := by
  unfold sgn
  split_ifs <;> norm_num

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.smul_apply]`. Apply the tactic sequence `by_cases hi : d = i <;> by_cases hj : c = j <;> subst_vars <;> simp [*]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diag_single_diag {n : ℕ} (s : Fin n → ℝ) (c d : Fin n) :
    (diagonal fun a => ((s a : ℝ) : ℂ)) * (Matrix.single c d (1 : ℂ))ᴴ * (diagonal fun a => ((s a : ℝ) : ℂ)) =
      (s c * s d) • Matrix.single d c (1 : ℂ) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.single_apply,
    Matrix.smul_apply]
  by_cases hi : d = i <;> by_cases hj : c = j <;> subst_vars <;> simp [*]
  ring

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Unfold `Ctx.IsB sgnM at hB`. Establish `hx : IsUnit (B ρ).det` using `isUnit_det_B C hB ρ`. Establish `hS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = 1`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Rewrite using `[← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]`. Establish `hsd` using `diag_single_diag (fun a : Fin T.rank => sgn C.X.p0 (a : ℕ)) c d`. Simplify using `only [conjAt]`. Rewrite using `[conj_frame_eq (R.1 ρ).2 hx (hB ρ) hS, hsd, Matrix.mul_smul, Matrix.smul_mul, neg_smul]`.
-/
theorem conjAt_single (C : Ctx S T) (R : RealPoints C.θ T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau)
    (c d : Fin T.rank) : conjAt T ρ (B ρ * Matrix.single c d 1 * (B ρ)⁻¹) =
      (-(sgn C.X.p0 c * sgn C.X.p0 d) : ℝ) • (B ρ * Matrix.single d c 1 * (B ρ)⁻¹) := by
  unfold Ctx.IsB sgnM at hB
  have hx : IsUnit (B ρ).det := isUnit_det_B C hB ρ
  have hS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]
  have hsd := diag_single_diag (fun a : Fin T.rank => sgn C.X.p0 (a : ℕ)) c d
  simp only [conjAt]
  rw [conj_frame_eq (R.1 ρ).2 hx (hB ρ) hS, hsd, Matrix.mul_smul, Matrix.smul_mul, neg_smul]

/- English proof (translation)
Use function extensionality and compare the values at `τ a b`. Express the relevant statement in the definitionally equal form `conj (I * Z τ a b) = -(I * conj (Z τ a b))`. Rewrite using `[map_mul, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conjL_I_smul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) :
    conjL (I • Z) = -(I • conjL Z) := by
  funext τ a b
  change conj (I * Z τ a b) = -(I * conj (Z τ a b))
  rw [map_mul, Complex.conj_I]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `τ' a b`. Express the relevant statement in the definitionally equal form `conj (unitFr τ c d τ' a b) = unitFr τ c d τ' a b`. Simplify using `only [unitFr]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem conjL_unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) :
    conjL (unitFr τ c d) = unitFr τ c d := by
  funext τ' a b
  change conj (unitFr τ c d τ' a b) = unitFr τ c d τ' a b
  simp only [unitFr]
  split_ifs <;> simp

/- English proof (translation)
Unfold `Ctx.IsB sgnM at hB`. Use function extensionality and compare the values at `ρ`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[toLie_I]`. Establish `hx : IsUnit (B ρ).det` using `isUnit_det_B C hB ρ`.

Establish `hS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = 1`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]`.

Establish `key : (mat (conjL Z) (C.m.e ρ))ᴴ * (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) + (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * mat (conjL Z) (C.m.e ρ) = 0`. Establish `hZe` using `hZ (C.m.e ρ)`. Rewrite using `[mat_conjL]`. Use extensionality with `i j`. Establish `h1` using `congrArg (fun M : Matrix (Fin T.rank) (Fin T.rank) ℂ => (starRingEnd ℂ) (M i j)) hZe`.

Simplify using `only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.zero_apply, ← starRingEnd_apply, map_add, map_mul, map_zero, Complex.conj_conj, Complex.conj_ofReal] at h1 ⊢`. Take the linear combination `h1`. Establish `hMS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * (mat (conjL Z) (C.m.e ρ))ᴴ * (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = -mat (conjL Z) (C.m.e ρ)`. Rewrite using `[Matrix.mul_assoc, eq_neg_of_add_eq_zero_left key, Matrix.mul_neg, ← Matrix.mul_assoc, hS, Matrix.one_mul]`. Simplify using `only [conjAt]`.

Rewrite using `[conj_frame_eq (R.1 ρ).2 hx (hB ρ) hS, hMS, Matrix.mul_neg, Matrix.neg_mul, neg_neg, sub_self, smul_zero]`. Both sides reduce to the same expression.
-/
theorem toLie_I_conjL (C : Ctx S T) (R : RealPoints C.θ T) {B : C.Bas} (hB : C.IsB B) {Z : Frame C.X.Ψ T.rank}
    (hZ : Z ∈ unitLie C.X) : toLie R B (fun ρ => C.m.e ρ) (I • conjL Z) = 0 := by
  unfold Ctx.IsB sgnM at hB
  funext ρ
  apply Subtype.ext
  rw [toLie_I]
  have hx : IsUnit (B ρ).det := isUnit_det_B C hB ρ
  have hS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]
  have key : (mat (conjL Z) (C.m.e ρ))ᴴ * (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) +
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * mat (conjL Z) (C.m.e ρ) = 0 := by
    have hZe := hZ (C.m.e ρ)
    rw [mat_conjL]
    ext i j
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin T.rank) ℂ => (starRingEnd ℂ) (M i j)) hZe
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.map_apply, Matrix.zero_apply, ← starRingEnd_apply, map_add, map_mul, map_zero,
      Complex.conj_conj, Complex.conj_ofReal] at h1 ⊢
    linear_combination h1
  have hMS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * (mat (conjL Z) (C.m.e ρ))ᴴ *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = -mat (conjL Z) (C.m.e ρ) := by
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left key, Matrix.mul_neg, ← Matrix.mul_assoc, hS,
      Matrix.one_mul]
  simp only [conjAt]
  rw [conj_frame_eq (R.1 ρ).2 hx (hB ρ) hS, hMS, Matrix.mul_neg, Matrix.neg_mul, neg_neg, sub_self, smul_zero]
  rfl

/- English proof (translation)
Introduce `D S T C R B hB φ hφ g ρ c d hcd Z Z' hZ hZ' hsum`. Take `⟨-, hk⟩` from `hφ`. Distinguish the cases in `hf : DifferentiableAt ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0`. Use `swap`. Rewrite using `[fderiv_zero_of_not_differentiableAt hf]`.

Simplify using the standard rewrite rules. Establish `hZ1 : toLieC C R B Z = toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)`. Establish `e : Z = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d - I • Z'` using `by rw [← hsum, add_sub_cancel_right]`. Rewrite using `[e]`. Simplify using `only [toLieC, LinearMap.comp_apply, map_sub, conjL_unitFr, conjL_I_smul, map_neg, toLie_I_conjL C R hB hZ', neg_zero, sub_zero]`.

Establish `hZ2 : toLieC C R B Z' = toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)`. Establish `e : Z' = I • Z - I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d`. Rewrite using `[← hsum, smul_add, smul_smul, I_mul_I, neg_one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Simplify using `only [toLieC, LinearMap.comp_apply, map_sub, conjL_I_smul, conjL_unitFr, map_neg, toLie_I_conjL C R hB hZ, neg_zero, zero_sub, neg_neg]`. Rewrite using `[hZ1, hZ2]`. Establish `hs : ∀ a : ℕ, sgn C.X.p0 a = 1 ∨ sgn C.X.p0 a = -1`. Introduce `a`. Unfold `sgn`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hε : (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) * (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) = (1 : ℝ)`. Establish `h1` using `sgn_mul_self C.X.p0 c`. Establish `h2` using `sgn_mul_self C.X.p0 d`. Take the linear combination `(sgn C.X.p0 (d : ℕ) * sgn C.X.p0 (d : ℕ)) * h1 + h2`.

Establish `hI : (1 / (2 * I) : ℂ) = -(I / 2)`. Rewrite using `[one_div, mul_inv, Complex.inv_I]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : (1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) = (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ).1`. Rewrite using `[toLie_val]`.

Simplify using `only [mat_unitFr, if_true]`. Rewrite using `[conjAt_single C R hB ρ c d, conjAt_single C R hB ρ d c]`. Apply the tactic sequence `rcases hs c with h1 | h1 <;> rcases hs d with h2 | h2 <;> rw [h1, h2] <;> module`. Establish `hBm : (1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) = (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ).1`. Rewrite using `[toLie_I]`.

Simplify using `only [mat_unitFr, if_true]`. Rewrite using `[conjAt_single C R hB ρ c d, conjAt_single C R hB ρ d c, hI]`. Apply the tactic sequence `rcases hs c with h1 | h1 <;> rcases hs d with h2 | h2 <;> rw [h1, h2] <;> module`. Establish `memA : (1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) ∈ lieU (gramAt D T ρ)`. Rewrite using `[hA]`.

Conclude with `(((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) ρ).2`. Establish `memB : (1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) ∈ lieU (gramAt D T ρ)`. Rewrite using `[hBm]`. Conclude with `(((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) ρ).2`. Establish `hN1 : toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) = HSMul.hSMul (α` using `ℝ) (β := GlobalTheory.SmoothForms.LieN T) (γ := GlobalTheory.SmoothForms.LieN T) (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) (atPlace T ρ ⟨_, memA⟩) := by`.

Use function extensionality and compare the values at `ρ'`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ').1 = (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • ((atPlace T ρ ⟨_, memA⟩ : GlobalTheory.SmoothForms.LieN T) ρ').1`. Distinguish the cases in `hρ : ρ' = ρ`. Substitute `hρ` using the available equality.

Simplify using `only [atPlace, Pi.single_eq_same]`. Rewrite using `[hA, smul_smul, hε, one_smul]`. Simplify using `only [atPlace, Pi.single_eq_of_ne hρ]`. Rewrite using `[toLie_val]`. Simplify using `[mat_unitFr, hρ, conjAt]`.

Establish `hN2 : toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) = HSMul.hSMul (α` using `ℝ) (β := GlobalTheory.SmoothForms.LieN T) (γ := GlobalTheory.SmoothForms.LieN T) (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) (atPlace T ρ ⟨_, memB⟩) := by`. Use function extensionality and compare the values at `ρ'`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ').1 = (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • ((atPlace T ρ ⟨_, memB⟩ : GlobalTheory.SmoothForms.LieN T) ρ').1`. Distinguish the cases in `hρ : ρ' = ρ`.

Substitute `hρ` using the available equality. Simplify using `only [atPlace, Pi.single_eq_same]`. Rewrite using `[hBm, smul_smul, hε, one_smul]`. Simplify using `only [atPlace, Pi.single_eq_of_ne hρ]`. Rewrite using `[toLie_I]`.

Simplify using `[mat_unitFr, hρ, conjAt]`. Establish `hk1` using `congrFun (hk ρ d c hcd) g`. Simplify using `only [RderC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk1`. Establish `e1 : (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0) (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) = (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • Rder C.θ T ρ ((1 / 2 : ℂ) • (B ρ * single …`. Rewrite using `[hN1]`.

Conclude with `(map_smul _ _ _).trans (congrArg (fun z : ℂ => (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • z) (fderiv_atPlace R g hf ρ ⟨_, memA⟩))`. Establish `e2 : (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0) (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) = (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • Rder C.θ T ρ ((1 / (2 * I) : ℂ) • (B …`. Rewrite using `[hN2]`. Conclude with `(map_smul _ _ _).trans (congrArg (fun z : ℂ => (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • z) (fderiv_atPlace R g hf ρ ⟨_, memB⟩))`. Rewrite using `[e1, e2]`.

Simplify using `only [Complex.real_smul]`. Take the linear combination `(((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) : ℂ)) * hk1`.
-/
theorem fderiv_toLieC_eq_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (φ : GA D T → ℂ), LowKilled C.θ T B φ → ∀ (g : GA D T) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  intro D S T C R B hB φ hφ g ρ c d hcd Z Z' hZ hZ' hsum
  obtain ⟨-, hk⟩ := hφ
  by_cases hf : DifferentiableAt ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0
  swap
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp

  have hZ1 : toLieC C R B Z = toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) := by
    have e : Z = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d - I • Z' := by rw [← hsum, add_sub_cancel_right]
    rw [e]
    simp only [toLieC, LinearMap.comp_apply, map_sub, conjL_unitFr, conjL_I_smul, map_neg,
      toLie_I_conjL C R hB hZ', neg_zero, sub_zero]
  have hZ2 : toLieC C R B Z' = toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) := by
    have e : Z' = I • Z - I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d := by
      rw [← hsum, smul_add, smul_smul, I_mul_I, neg_one_smul]
      abel
    rw [e]
    simp only [toLieC, LinearMap.comp_apply, map_sub, conjL_I_smul, conjL_unitFr, map_neg,
      toLie_I_conjL C R hB hZ, neg_zero, zero_sub, neg_neg]
  rw [hZ1, hZ2]

  have hs : ∀ a : ℕ, sgn C.X.p0 a = 1 ∨ sgn C.X.p0 a = -1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  have hε : (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) * (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) =
      (1 : ℝ) := by
    have h1 := sgn_mul_self C.X.p0 c
    have h2 := sgn_mul_self C.X.p0 d
    linear_combination (sgn C.X.p0 (d : ℕ) * sgn C.X.p0 (d : ℕ)) * h1 + h2
  have hI : (1 / (2 * I) : ℂ) = -(I / 2) := by
    rw [one_div, mul_inv, Complex.inv_I]
    ring

  have hA : (1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ).1 := by
    rw [toLie_val]
    simp only [mat_unitFr, if_true]
    rw [conjAt_single C R hB ρ c d, conjAt_single C R hB ρ d c]
    rcases hs c with h1 | h1 <;> rcases hs d with h2 | h2 <;> rw [h1, h2] <;> module
  have hBm : (1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ).1 := by
    rw [toLie_I]
    simp only [mat_unitFr, if_true]
    rw [conjAt_single C R hB ρ c d, conjAt_single C R hB ρ d c, hI]
    rcases hs c with h1 | h1 <;> rcases hs d with h2 | h2 <;> rw [h1, h2] <;> module
  have memA : (1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) ∈
      lieU (gramAt D T ρ) := by
    rw [hA]
    exact (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
      toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) ρ).2
  have memB : (1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) ∈
      lieU (gramAt D T ρ) := by
    rw [hBm]
    exact (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
      toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) ρ).2

  have hN1 : toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) =
      HSMul.hSMul (α := ℝ) (β := GlobalTheory.SmoothForms.LieN T) (γ := GlobalTheory.SmoothForms.LieN T)
        (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) (atPlace T ρ ⟨_, memA⟩) := by
    funext ρ'
    apply Subtype.ext
    change (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ').1 =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • ((atPlace T ρ ⟨_, memA⟩ : GlobalTheory.SmoothForms.LieN T) ρ').1
    by_cases hρ : ρ' = ρ
    · subst hρ
      simp only [atPlace, Pi.single_eq_same]
      rw [hA, smul_smul, hε, one_smul]
    · simp only [atPlace, Pi.single_eq_of_ne hρ]
      rw [toLie_val]
      simp [mat_unitFr, hρ, conjAt]
  have hN2 : toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) =
      HSMul.hSMul (α := ℝ) (β := GlobalTheory.SmoothForms.LieN T) (γ := GlobalTheory.SmoothForms.LieN T)
        (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) (atPlace T ρ ⟨_, memB⟩) := by
    funext ρ'
    apply Subtype.ext
    change (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ').1 =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • ((atPlace T ρ ⟨_, memB⟩ : GlobalTheory.SmoothForms.LieN T) ρ').1
    by_cases hρ : ρ' = ρ
    · subst hρ
      simp only [atPlace, Pi.single_eq_same]
      rw [hBm, smul_smul, hε, one_smul]
    · simp only [atPlace, Pi.single_eq_of_ne hρ]
      rw [toLie_I]
      simp [mat_unitFr, hρ, conjAt]
  have hk1 := congrFun (hk ρ d c hcd) g
  simp only [RderC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk1
  have e1 : (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0)
      (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        Rder C.θ T ρ ((1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹))) φ g := by
    rw [hN1]
    exact (map_smul _ _ _).trans (congrArg (fun z : ℂ => (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • z)
      (fderiv_atPlace R g hf ρ ⟨_, memA⟩))
  have e2 : (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0)
      (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        Rder C.θ T ρ ((1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹))) φ g := by
    rw [hN2]
    exact (map_smul _ _ _).trans (congrArg (fun z : ℂ => (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • z)
      (fderiv_atPlace R g hf ρ ⟨_, memB⟩))
  rw [e1, e2]
  simp only [Complex.real_smul]
  linear_combination (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) : ℂ)) * hk1

end GlobalTheory.AdSpan.ConjHol
