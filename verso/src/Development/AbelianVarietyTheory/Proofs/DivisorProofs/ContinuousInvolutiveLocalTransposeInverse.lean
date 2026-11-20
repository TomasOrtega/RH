import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.LocTwist

variable {R : Type} [CommRing R]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_Phi (a : ℕ) (c : R →+* R) : c.mapMatrix (GlobalTheory.Tw.Phi a R) = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.mul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single i.rev]`. Establish `h1 : (i : ℕ) + (i.rev : ℕ) + 1 = a` using `by rw [Fin.val_rev]; omega`. Rewrite using `[if_pos h1]`.

Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Rewrite using `[if_pos (by rw [Fin.val_rev]; omega), Matrix.one_apply_eq, mul_one, ← pow_add]`. Use `congr 1`. Rewrite using `[Fin.val_rev]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg (fun h2 => h (Fin.ext (by rw [Fin.val_rev] at h2; omega))), Matrix.one_apply_ne (Ne.symm h), mul_zero, mul_zero]`. Introduce `j _ hj`. Rewrite using `[if_neg (fun h => hj (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem Phi_mul_self (a : ℕ) : GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) := by
  ext i k
  simp only [Matrix.mul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i.rev]
  · have h1 : (i : ℕ) + (i.rev : ℕ) + 1 = a := by rw [Fin.val_rev]; omega
    rw [if_pos h1]
    by_cases h : k = i
    · subst h
      rw [if_pos (by rw [Fin.val_rev]; omega), Matrix.one_apply_eq, mul_one, ← pow_add]
      congr 1
      rw [Fin.val_rev]; omega
    · rw [if_neg (fun h2 => h (Fin.ext (by rw [Fin.val_rev] at h2; omega))), Matrix.one_apply_ne (Ne.symm h), mul_zero, mul_zero]
  · intro j _ hj
    rw [if_neg (fun h => hj (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]
  · simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem thetaGL_val (a : ℕ) (c : R →+* R) (g : GL (Fin a) R) :
    (thetaGL a c g).val = GlobalTheory.Tw.Phi a R * (c.mapMatrix (g⁻¹).val)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `hT : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix Mᵀ = (c.mapMatrix M)ᵀ` using `fun M => rfl`. Establish `hcc : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix (c.mapMatrix M) = M` using `fun M => by`. Use extensionality with `i j`. Conclude with `hc _`.

Rewrite using `[thetaGL_val, ← map_inv, thetaGL_val, inv_inv, map_mul, map_mul, map_Phi, hT, hT, map_Phi, hcc]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose]`. Establish `hP` using `Phi_mul_self (R := R) a`. Establish `hPt : (GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R)`. Rewrite using `[← Matrix.transpose_mul, hP, Matrix.transpose_smul, Matrix.transpose_one]`.

Establish `e : ∀ X : Matrix (Fin a) (Fin a) R, GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R * (X * (GlobalTheory.Tw.Phi a R)ᵀ)) * (GlobalTheory.Tw.Phi a R)ᵀ = (GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R) * X * ((GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ)`. Introduce `X`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, hP, hPt, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem thetaGL_thetaGL (a : ℕ) (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin a) R) :
    thetaGL a c (thetaGL a c g) = g := by
  apply Units.ext
  have hT : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix Mᵀ = (c.mapMatrix M)ᵀ := fun M => rfl
  have hcc : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix (c.mapMatrix M) = M := fun M => by
    ext i j; exact hc _
  rw [thetaGL_val, ← map_inv, thetaGL_val, inv_inv, map_mul, map_mul, map_Phi, hT, hT, map_Phi, hcc]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hP := Phi_mul_self (R := R) a
  have hPt : (GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) := by
    rw [← Matrix.transpose_mul, hP, Matrix.transpose_smul, Matrix.transpose_one]
  have e : ∀ X : Matrix (Fin a) (Fin a) R, GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R * (X * (GlobalTheory.Tw.Phi a R)ᵀ)) * (GlobalTheory.Tw.Phi a R)ᵀ
      = (GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R) * X * ((GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ) := by
    intro X; simp only [Matrix.mul_assoc]
  rw [e, hP, hPt, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow]
  simp

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun g : GL (Fin a) R => GlobalTheory.Tw.Phi a R * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ`. Conclude with `(continuous_const.matrix_mul ((Units.continuous_coe_inv.matrix_map hc).matrix_transpose)).matrix_mul continuous_const`. Establish `: (fun g : GL (Fin a) R => ((thetaGL a c g)⁻¹).val) = fun g => GlobalTheory.Tw.Phi a R * (g.val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ`.

Use function extensionality and compare the values at `g`. Rewrite using `[← map_inv, thetaGL_val, inv_inv]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(continuous_const.matrix_mul ((Units.continuous_val.matrix_map hc).matrix_transpose)).matrix_mul continuous_const`.
-/
theorem continuous_thetaGL [TopologicalSpace R] [IsTopologicalRing R] (a : ℕ) (c : R →+* R) (hc : Continuous c) :
    Continuous (thetaGL a c) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin a) R => GlobalTheory.Tw.Phi a R * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ
    exact (continuous_const.matrix_mul ((Units.continuous_coe_inv.matrix_map hc).matrix_transpose)).matrix_mul
      continuous_const
  · have : (fun g : GL (Fin a) R => ((thetaGL a c g)⁻¹).val) =
        fun g => GlobalTheory.Tw.Phi a R * (g.val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ := by
      funext g
      rw [← map_inv, thetaGL_val, inv_inv]
      rfl
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.matrix_map hc).matrix_transpose)).matrix_mul
      continuous_const

end GlobalTheory.LocTwist

/- English proof (translation)
Introduce `E _ _ _ hU n w`. Take `⟨hcont, hinv, -⟩` from `GlobalTheory.ConjAtPlace.main E hU w`. Unfold `thL`. Use `split_ifs`. Conclude with `⟨continuous_id, fun g => rfl⟩`.

Conclude with `⟨GlobalTheory.LocTwist.continuous_thetaGL n (cj w) hcont, GlobalTheory.LocTwist.thetaGL_thetaGL n (cj w) hinv⟩`.
-/
theorem GlobalTheory.BCT.thL_continuous_involutive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  intro E _ _ _ hU n w
  obtain ⟨hcont, hinv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  unfold thL
  split_ifs
  · exact ⟨continuous_id, fun g => rfl⟩
  · exact ⟨GlobalTheory.LocTwist.continuous_thetaGL n (cj w) hcont, GlobalTheory.LocTwist.thetaGL_thetaGL n (cj w) hinv⟩
