import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma p0auxiliary_rdV_neg {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) (g : Matrix (Fin n) (Fin n) ℂ) :
    RdV (-X) f g = -RdV X f g := by
  have key := deriv_comp_neg (f := fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (x := (0 : ℝ))
  simp only [neg_zero, Complex.ofReal_neg, neg_smul] at key
  simp only [RdV, smul_neg]
  exact key

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma p0auxiliary_theta_single {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = (sgn ε a b : ℂ) • Matrix.single b a 1 := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.smul_apply, Matrix.single_apply, sgn, smul_eq_mul]
  push_cast
  split_ifs <;> simp_all

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
private lemma Jm_mul_selfRealPlaceTaylor {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
private lemma conjTranspose_Jm {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private lemma Jm_mul_conjTranspose_smul_mul_Jm {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (c • Z)ᴴ * Jm ε = star c • (Jm ε * Zᴴ * Jm ε) := by
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
private lemma inG_cpart1_real_place_taylor {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart1 ε Z) := by
  have hAH : (Jm ε * Zᴴ * Jm ε)ᴴ = Jm ε * Z * Jm ε := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      conjTranspose_Jm, Matrix.mul_assoc]
  have h1 : Jm ε * Z * Jm ε * Jm ε = Jm ε * Z := by
    rw [Matrix.mul_assoc, Jm_mul_selfRealPlaceTaylor, Matrix.mul_one]
  have h2 : Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_selfRealPlaceTaylor, Matrix.one_mul]
  rw [inG, cpart1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hAH, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
  simp <;> module

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Normalize the expressions using the abelian group laws.
-/
lemma p0auxiliary_cpart1_add {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (Z + W) = cpart1 ε Z + cpart1 ε W := by
  rw [cpart1, cpart1, cpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Normalize the expressions using the abelian group laws.
-/
lemma p0auxiliary_cpart2_add {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Z + W) = cpart2 ε Z + cpart2 ε W := by
  rw [cpart2, cpart2, cpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
lemma p0auxiliary_cpart1_real {n : ℕ} (ε : Fin n → Bool) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε ((x : ℂ) • Z) = (x : ℂ) • cpart1 ε Z := by
  have hx : star (x : ℂ) = x := Complex.conj_ofReal x
  rw [cpart1, cpart1, Jm_mul_conjTranspose_smul_mul_Jm, hx, ← smul_sub, smul_comm]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
lemma p0auxiliary_cpart2_real {n : ℕ} (ε : Fin n → Bool) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε ((x : ℂ) • Z) = (x : ℂ) • cpart2 ε Z := by
  have hx : star (x : ℂ) = x := Complex.conj_ofReal x
  rw [cpart2, cpart2, Jm_mul_conjTranspose_smul_mul_Jm, hx, ← smul_add, smul_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
lemma p0auxiliary_half_I : (1 / (2 * Complex.I) : ℂ) = -(1 / 2) * Complex.I := by
  rw [one_div, mul_inv, Complex.inv_I]
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma p0auxiliary_cpart1_I {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (Complex.I • Z) = -cpart2 ε Z := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rw [cpart1, cpart2, Jm_mul_conjTranspose_smul_mul_Jm, hI, p0auxiliary_half_I]
  module

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private lemma inG_cpart2_real_place_taylor {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart2 ε Z) := by
  have h := inG_cpart1_real_place_taylor ε (Complex.I • Z)
  rw [p0auxiliary_cpart1_I] at h
  rw [inG] at h ⊢
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add] at h
  exact neg_eq_zero.mp h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma p0auxiliary_cpart2_I {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Complex.I • Z) = cpart1 ε Z := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have k1 : (-(1 / 2) * Complex.I) * Complex.I = 1 / 2 := by
    linear_combination (-(1 / 2) : ℂ) * Complex.I_sq
  have k2 : (-(1 / 2) * Complex.I) * -Complex.I = -(1 / 2) := by
    linear_combination ((1 / 2) : ℂ) * Complex.I_sq
  rw [cpart2, cpart1, Jm_mul_conjTranspose_smul_mul_Jm, hI, p0auxiliary_half_I, smul_add, smul_smul, smul_smul, k1, k2]
  module

section EcV
variable (hl : RdLinV) {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
include hl

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
lemma p0auxiliary_ecV_add (hf : SmoothOnGV ε f) (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (Z + W) f g = EcV ε Z f g + EcV ε W f g := by
  have H := hl
  unfold RdLinV at H
  simp only [EcV]
  rw [p0auxiliary_cpart1_add, p0auxiliary_cpart2_add,
    (H n ε E f f _ _ 0 0 g hf hf (inG_cpart1_real_place_taylor ε Z) (inG_cpart1_real_place_taylor ε W) hg).1,
    (H n ε E f f _ _ 0 0 g hf hf (inG_cpart2_real_place_taylor ε Z) (inG_cpart2_real_place_taylor ε W) hg).1, smul_add]
  abel

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
lemma p0auxiliary_ecV_real (hf : SmoothOnGV ε f) (hg : inUJ ε g) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε ((x : ℂ) • Z) f g = (x : ℂ) • EcV ε Z f g := by
  have H := hl
  unfold RdLinV at H
  simp only [EcV]
  rw [p0auxiliary_cpart1_real, p0auxiliary_cpart2_real,
    (H n ε E f f _ _ x 0 g hf hf (inG_cpart1_real_place_taylor ε Z) (inG_cpart1_real_place_taylor ε Z) hg).2.1,
    (H n ε E f f _ _ x 0 g hf hf (inG_cpart2_real_place_taylor ε Z) (inG_cpart2_real_place_taylor ε Z) hg).2.1, smul_add,
    smul_comm Complex.I (x : ℂ)]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
lemma p0auxiliary_ecV_I (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (Complex.I • Z) f g = Complex.I • EcV ε Z f g := by
  simp only [EcV]
  rw [p0auxiliary_cpart1_I, p0auxiliary_cpart2_I, p0auxiliary_rdV_neg, smul_add, smul_smul, Complex.I_mul_I,
    neg_one_smul]
  abel

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
lemma p0auxiliary_ecV_smul (hf : SmoothOnGV ε f) (hg : inUJ ε g) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (c • Z) f g = c • EcV ε Z f g := by
  have hc : c • Z = (c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [hc, p0auxiliary_ecV_add hl hf hg, p0auxiliary_ecV_real hl hf hg, p0auxiliary_ecV_real hl hf hg,
    p0auxiliary_ecV_I hl, smul_smul, ← add_smul, Complex.re_add_im]

end EcV

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ecSumV_of (h : RdLinV) : EcSumV := by
  unfold EcSumV
  intro n ε E _ _ f Z g hf hg
  let L : Matrix (Fin n) (Fin n) ℂ →+ E :=
    AddMonoidHom.mk' (fun Y => EcV ε Y f g) (fun Y W => p0auxiliary_ecV_add h hf hg Y W)
  have hL : ∀ Y, L Y = EcV ε Y f g := fun Y => rfl
  calc EcV ε Z f g = L (∑ a, ∑ b, Matrix.single a b (Z a b)) := by
        rw [hL, ← Matrix.matrix_eq_sum_single Z]
    _ = ∑ a, ∑ b, L (Matrix.single a b (Z a b)) := by simp only [map_sum]
    _ = ∑ a, ∑ b, Z a b • EabV ε a b f g := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have hs : Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := by
          ext i j
          simp [Matrix.single_apply]
        rw [hL, hs, p0auxiliary_ecV_smul h hf hg, EabV]

end Formalism.REAL
