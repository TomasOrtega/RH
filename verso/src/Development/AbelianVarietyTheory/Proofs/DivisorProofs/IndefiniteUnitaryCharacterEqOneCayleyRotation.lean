import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open Formalism.BasicNotions.TH

noncomputable section

namespace GlobalTheory.UnitaryCharRot

open Complex

def signatureOneOneForm : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def boost : Matrix (Fin 2) (Fin 2) ℂ := !![5/4, 3/4; 3/4, 5/4]

def boostInv : Matrix (Fin 2) (Fin 2) ℂ := !![5/4, -3/4; -3/4, 5/4]

def upperUnip (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1 + t * I, -(t * I); t * I, 1 - t * I]

def lowerUnip (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1 + t * I, t * I; -(t * I), 1 - t * I]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [upperUnip, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem upperUnip_mem (t : ℝ) : (upperUnip t)ᴴ * signatureOneOneForm * upperUnip t = signatureOneOneForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperUnip, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [lowerUnip, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem lowerUnip_mem (t : ℝ) : (lowerUnip t)ᴴ * signatureOneOneForm * lowerUnip t = signatureOneOneForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerUnip, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [boost, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem boost_mem : (boost)ᴴ * signatureOneOneForm * boost = signatureOneOneForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [boostInv, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem boostInv_mem : (boostInv)ᴴ * signatureOneOneForm * boostInv = signatureOneOneForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boostInv, signatureOneOneForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [boost, boostInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem boost_boostInv : boost * boostInv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, boostInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [boost, boostInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem boostInv_boost : boostInv * boost = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, boostInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [upperUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem upperUnip_neg (u : ℝ) : upperUnip u * upperUnip (-u) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem lowerUnip_neg (u : ℝ) : lowerUnip u * lowerUnip (-u) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [boost, boostInv, upperUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem upperUnip_comm (u : ℝ) : boost * upperUnip u * boostInv * upperUnip (-u) = upperUnip (3 * u) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, boostInv, upperUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [boost, boostInv, lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>`. Apply the tactic sequence `(try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))`.
-/
theorem lowerUnip_comm (u : ℝ) : boostInv * lowerUnip u * boost * lowerUnip (-u) = lowerUnip (3 * u) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, boostInv, lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, map_div₀, map_ofNat] <;>
    (try constructor) <;> (first | trivial | (ring_nf; done) | (norm_num; done))

/- English proof (translation)
Establish `h1 : (1 - 2 * I * x) ≠ 0`. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Establish `h3 : (1 + 4 * x ^ 2) ≠ 0` using `by positivity`.

Rewrite using `[div_eq_iff h1, Complex.ext_iff]`. Generalize the expression as in `hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c`. Generalize the expression as in `hs : (4 * x) / (1 + 4 * x ^ 2) = s`. Simplify using the standard rewrite rules. Substitute `hc hs` using the available equality.

Apply the tactic sequence `constructor <;> field_simp <;> ring`.
-/
theorem zeta_eq (x : ℝ) : (1 + 2 * I * x) / (1 - 2 * I * x) =
    (((1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) : ℝ) : ℂ) + (((4 * x) / (1 + 4 * x ^ 2) : ℝ) : ℂ) * I := by
  have h1 : (1 - 2 * I * x) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h3 : (1 + 4 * x ^ 2) ≠ 0 := by positivity
  rw [div_eq_iff h1, Complex.ext_iff]
  generalize hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c
  generalize hs : (4 * x) / (1 + 4 * x ^ 2) = s
  simp
  subst hc hs
  constructor <;> field_simp <;> ring
/- English proof (translation)
Establish `h1 : (1 + 2 * I * x) ≠ 0`. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Establish `h3 : (1 + 4 * x ^ 2) ≠ 0` using `by positivity`.

Rewrite using `[div_eq_iff h1, Complex.ext_iff]`. Generalize the expression as in `hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c`. Generalize the expression as in `hs : (4 * x) / (1 + 4 * x ^ 2) = s`. Simplify using the standard rewrite rules. Substitute `hc hs` using the available equality.

Apply the tactic sequence `constructor <;> field_simp <;> ring`.
-/
theorem zeta_eq' (x : ℝ) : (1 - 2 * I * x) / (1 + 2 * I * x) =
    (((1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) : ℝ) : ℂ) - (((4 * x) / (1 + 4 * x ^ 2) : ℝ) : ℂ) * I := by
  have h1 : (1 + 2 * I * x) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h3 : (1 + 4 * x ^ 2) ≠ 0 := by positivity
  rw [div_eq_iff h1, Complex.ext_iff]
  generalize hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c
  generalize hs : (4 * x) / (1 + 4 * x ^ 2) = s
  simp
  subst hc hs
  constructor <;> field_simp <;> ring

/- English proof (translation)
Establish `h3 : (1 + 4 * x ^ 2) ≠ 0` using `by positivity`. Rewrite using `[zeta_eq, zeta_eq']`. Generalize the expression as in `hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c`. Generalize the expression as in `hs : (4 * x) / (1 + 4 * x ^ 2) = s`. Generalize the expression as in `hy : 2 * x / (1 + 4 * x ^ 2) = y`.

Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [upperUnip, lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>`. Apply the tactic sequence `subst hc hs hy <;> (try constructor) <;> field_simp <;> ring`.
-/
theorem rot_eq (x : ℝ) : upperUnip x * lowerUnip (2 * x / (1 + 4 * x ^ 2)) * upperUnip x =
    !![(1 + 2 * I * x) / (1 - 2 * I * x), 0; 0, (1 - 2 * I * x) / (1 + 2 * I * x)] := by
  have h3 : (1 + 4 * x ^ 2) ≠ 0 := by positivity
  rw [zeta_eq, zeta_eq']
  generalize hc : (1 - 4 * x ^ 2) / (1 + 4 * x ^ 2) = c
  generalize hs : (4 * x) / (1 + 4 * x ^ 2) = s
  generalize hy : 2 * x / (1 + 4 * x ^ 2) = y
  ext i j; fin_cases i <;> fin_cases j <;> simp [upperUnip, lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    subst hc hs hy <;> (try constructor) <;> field_simp <;> ring

variable {R S : ℕ}

def pl (i0 : Fin R) (j0 : Fin S) : Fin 2 → Fin R ⊕ Fin S := ![Sum.inl i0, Sum.inr j0]

def emb (i0 : Fin R) (j0 : Fin S) : Matrix (Fin R ⊕ Fin S) (Fin 2) ℂ :=
  Matrix.of fun k p => if k = pl i0 j0 p then 1 else 0

def inPlane (i0 : Fin R) (j0 : Fin S) (M : Matrix (Fin 2) (Fin 2) ℂ) : Mat R S :=
  1 + emb i0 j0 * (M - 1) * (emb i0 j0)ᵀ

variable (i0 : Fin R) (j0 : Fin S)
/- English proof (translation)
Apply the tactic sequence `ext p q; fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, emb, pl, Fintype.sum_sum_type, Matrix.one_apply]`.
-/
theorem embT_emb : (emb i0 j0)ᵀ * emb i0 j0 = 1 := by
  ext p q; fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, emb, pl, Fintype.sum_sum_type, Matrix.one_apply]
/- English proof (translation)
Apply the tactic sequence `ext p k; simp only [emb, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]; split_ifs <;> simp`.
-/
theorem emb_ct : (emb i0 j0)ᴴ = (emb i0 j0)ᵀ := by
  ext p k; simp only [emb, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]; split_ifs <;> simp
/- English proof (translation)
Apply the tactic sequence `ext k p; simp only [emb, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]; split_ifs <;> simp`.
-/
theorem embT_ct : ((emb i0 j0)ᵀ)ᴴ = emb i0 j0 := by
  ext k p; simp only [emb, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]; split_ifs <;> simp
/- English proof (translation)
Apply the tactic sequence `ext k l; rcases k with k | k <;> rcases l with l | l <;>`. Apply the tactic sequence `simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp`.
-/
theorem Jm_diag : Jm R S = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
  ext k l; rcases k with k | k <;> rcases l with l | l <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
/- English proof (translation)
Apply the tactic sequence `ext p q; fin_cases p <;> fin_cases q <;> simp [signatureOneOneForm]`.
-/
theorem sig_diag : signatureOneOneForm = Matrix.diagonal ![1, -1] := by
  ext p q; fin_cases p <;> fin_cases q <;> simp [signatureOneOneForm]
/- English proof (translation)
Rewrite using `[Jm_diag, sig_diag]`. Apply the tactic sequence `ext k p; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; rcases k with k | k <;> fin_cases p <;> simp [emb, pl] <;> split_ifs <;> simp`.
-/
theorem Jm_emb : Jm R S * emb i0 j0 = emb i0 j0 * signatureOneOneForm := by
  rw [Jm_diag, sig_diag]
  ext k p; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; rcases k with k | k <;> fin_cases p <;> simp [emb, pl] <;>
    split_ifs <;> simp
/- English proof (translation)
Rewrite using `[Jm_diag, sig_diag]`. Apply the tactic sequence `ext p k; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; rcases k with k | k <;> fin_cases p <;> simp [emb, pl] <;> split_ifs <;> simp`.
-/
theorem embT_Jm : (emb i0 j0)ᵀ * Jm R S = signatureOneOneForm * (emb i0 j0)ᵀ := by
  rw [Jm_diag, sig_diag]
  ext p k; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; rcases k with k | k <;> fin_cases p <;> simp [emb, pl] <;>
    split_ifs <;> simp
/- English proof (translation)
Apply the tactic sequence `ext k l; rcases k with k | k <;> rcases l with l | l <;>`. Simplify using `[inPlane, emb, pl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.diagonal_apply, Function.update_apply]`. Apply the tactic sequence `by_cases h1 : k = i0 <;> by_cases h2 : l = i0 <;> simp [h1, h2]`. Substitute `h1` using the available equality. Simplify using `[Ne.symm h2]`.

Apply the tactic sequence `by_cases h1 : k = j0 <;> by_cases h2 : l = j0 <;> simp [h1, h2]`. Substitute `h1` using the available equality. Simplify using `[Ne.symm h2]`.
-/
theorem inPlane_diag (a b : ℂ) : inPlane i0 j0 !![a, 0; 0, b] = Matrix.fromBlocks (Matrix.diagonal (Function.update 1 i0 a)) 0 0
    (Matrix.diagonal (Function.update 1 j0 b)) := by
  ext k l; rcases k with k | k <;> rcases l with l | l <;>
    simp [inPlane, emb, pl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.diagonal_apply, Function.update_apply]
  · by_cases h1 : k = i0 <;> by_cases h2 : l = i0 <;> simp [h1, h2]
    subst h1; simp [Ne.symm h2]
  · by_cases h1 : k = j0 <;> by_cases h2 : l = j0 <;> simp [h1, h2]
    subst h1; simp [Ne.symm h2]
/- English proof (translation)
Simplify using `[inPlane]`.
-/
theorem inPlane_one : inPlane i0 j0 1 = 1 := by simp [inPlane]
/- English proof (translation)
Establish `e3 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (emb i0 j0 * Z) = Z` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, embT_emb, Matrix.one_mul]`. Establish `hM : M * M' - 1 = (M - 1) + (M' - 1) + (M - 1) * (M' - 1)` using `by noncomm_ring`. Simplify using `only [inPlane, hM, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, e3]`. Normalize the expressions using the abelian group laws.
-/
theorem inPlane_mul (M M' : Matrix (Fin 2) (Fin 2) ℂ) : inPlane i0 j0 (M * M') = inPlane i0 j0 M * inPlane i0 j0 M' := by
  have e3 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (emb i0 j0 * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, embT_emb, Matrix.one_mul]
  have hM : M * M' - 1 = (M - 1) + (M' - 1) + (M - 1) * (M' - 1) := by noncomm_ring
  simp only [inPlane, hM, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, e3]
  abel
/- English proof (translation)
Simplify using `[inPlane, Matrix.conjTranspose_mul, emb_ct, embT_ct, Matrix.mul_assoc]`.
-/
theorem inPlane_ct (M : Matrix (Fin 2) (Fin 2) ℂ) : (inPlane i0 j0 M)ᴴ = inPlane i0 j0 Mᴴ := by
  simp [inPlane, Matrix.conjTranspose_mul, emb_ct, embT_ct, Matrix.mul_assoc]
/- English proof (translation)
Establish `e1 : ∀ Z : Matrix (Fin R ⊕ Fin S) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (Jm R S * Z) = signatureOneOneForm * ((emb i0 j0)ᵀ * Z)` using `fun Z => by rw [← Matrix.mul_assoc, embT_Jm, Matrix.mul_assoc]`. Establish `e2 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, Jm R S * (emb i0 j0 * Z) = emb i0 j0 * (signatureOneOneForm * Z)` using `fun Z => by rw [← Matrix.mul_assoc, Jm_emb, Matrix.mul_assoc]`. Establish `e3 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (emb i0 j0 * Z) = Z` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, embT_emb, Matrix.one_mul]`. Establish `key : (Mᴴ - 1) * signatureOneOneForm + signatureOneOneForm * (M - 1) + (Mᴴ - 1) * (signatureOneOneForm * (M - 1)) = 0`.

Establish `: (Mᴴ - 1) * signatureOneOneForm + signatureOneOneForm * (M - 1) + (Mᴴ - 1) * (signatureOneOneForm * (M - 1)) = Mᴴ * signatureOneOneForm * M - signatureOneOneForm` using `by noncomm_ring`. Rewrite using `[this, h, sub_self]`. Establish `key' : emb i0 j0 * ((Mᴴ - 1) * (signatureOneOneForm * (emb i0 j0)ᵀ)) + emb i0 j0 * (signatureOneOneForm * ((M - 1) * (emb i0 j0)ᵀ)) + emb i0 j0 * ((Mᴴ - 1) * (signatureOneOneForm * ((M - 1) * (emb i0 j0)ᵀ))) = 0`. Use `congrArg (fun X => emb i0 j0 * X * (emb i0 j0)ᵀ) key` as an intermediate fact. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero] at this`.

Conclude with `this`. Rewrite using `[inPlane_ct]`. Simplify using `only [inPlane, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, e1, e2, e3, embT_Jm]`. Rewrite using `[← sub_eq_zero]`. Rewrite `key'` using `[← sub_eq_zero]`.

Rewrite using `[← key']`. Normalize the expressions using the abelian group laws.
-/
theorem inPlane_mem (M : Matrix (Fin 2) (Fin 2) ℂ) (h : Mᴴ * signatureOneOneForm * M = signatureOneOneForm) :
    (inPlane i0 j0 M)ᴴ * Jm R S * inPlane i0 j0 M = Jm R S := by
  have e1 : ∀ Z : Matrix (Fin R ⊕ Fin S) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (Jm R S * Z) = signatureOneOneForm * ((emb i0 j0)ᵀ * Z) :=
    fun Z => by rw [← Matrix.mul_assoc, embT_Jm, Matrix.mul_assoc]
  have e2 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, Jm R S * (emb i0 j0 * Z) = emb i0 j0 * (signatureOneOneForm * Z) :=
    fun Z => by rw [← Matrix.mul_assoc, Jm_emb, Matrix.mul_assoc]
  have e3 : ∀ Z : Matrix (Fin 2) (Fin R ⊕ Fin S) ℂ, (emb i0 j0)ᵀ * (emb i0 j0 * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, embT_emb, Matrix.one_mul]
  have key : (Mᴴ - 1) * signatureOneOneForm + signatureOneOneForm * (M - 1) + (Mᴴ - 1) * (signatureOneOneForm * (M - 1)) = 0 := by
    have : (Mᴴ - 1) * signatureOneOneForm + signatureOneOneForm * (M - 1) + (Mᴴ - 1) * (signatureOneOneForm * (M - 1)) = Mᴴ * signatureOneOneForm * M - signatureOneOneForm := by noncomm_ring
    rw [this, h, sub_self]
  have key' : emb i0 j0 * ((Mᴴ - 1) * (signatureOneOneForm * (emb i0 j0)ᵀ)) + emb i0 j0 * (signatureOneOneForm * ((M - 1) * (emb i0 j0)ᵀ)) +
      emb i0 j0 * ((Mᴴ - 1) * (signatureOneOneForm * ((M - 1) * (emb i0 j0)ᵀ))) = 0 := by
    have := congrArg (fun X => emb i0 j0 * X * (emb i0 j0)ᵀ) key
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero] at this
    exact this
  rw [inPlane_ct]
  simp only [inPlane, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, e1, e2, e3, embT_Jm]
  rw [← sub_eq_zero]; rw [← sub_eq_zero] at key'; rw [← key']; abel

/- English proof (translation)
Introduce `R S χ hmul _ hne i0 j0 x`. Establish `hG : ∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → (g * h)ᴴ * Jm R S * (g * h) = Jm R S`. Introduce `g h hg hh`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1mem : (1 : Mat R S)ᴴ * Jm R S * 1 = Jm R S` using `by simp`. Establish `h1 : χ 1 = 1`. Establish `e` using `hmul 1 1 h1mem h1mem`. Rewrite `e` using `[Matrix.one_mul]`. Conclude with `mul_left_cancel₀ (hne 1 h1mem) (e.symm.trans (mul_one _).symm)`.

Establish `key : ∀ a b c d : Mat R S, aᴴ * Jm R S * a = Jm R S → bᴴ * Jm R S * b = Jm R S → cᴴ * Jm R S * c = Jm R S → dᴴ * Jm R S * d = Jm R S → a * c = 1 → b * d = 1 → χ (a * b * c * d) = 1`. Introduce `a b c d ha hb hc hd hac hbd`. Establish `hab` using `hG a b ha hb`. Establish `habc` using `hG _ c hab hc`. Rewrite using `[hmul _ d habc hd, hmul _ c hab hc, hmul a b ha hb]`.

Establish `e1` using `hmul a c ha hc`. Establish `e2` using `hmul b d hb hd`. Rewrite `e1` using `[hac, h1]`. Rewrite `e2` using `[hbd, h1]`. Take the linear combination `(-(χ b * χ d)) * e1 - e2`.

Establish `hn : ∀ t : ℝ, χ (inPlane i0 j0 (upperUnip t)) = 1`. Introduce `t`. Establish `e` using `key (inPlane i0 j0 boost) (inPlane i0 j0 (upperUnip (t / 3))) (inPlane i0 j0 boostInv) (inPlane i0 j0 (upperUnip (-(t / 3)))) (inPlane_mem i0 j0 _ boost_mem) (inPlane_mem i0 j0 _ (upperUnip_mem _)) (inPlane_mem i0 j0 _ boostInv_mem) (inPlane_mem i0 j0 _ (upperUnip_mem _)) (by rw …`. Rewrite `e` using `[← inPlane_mul, ← inPlane_mul, ← inPlane_mul, upperUnip_comm, show 3 * (t / 3) = t by ring]`. Then use the resulting hypothesis. Establish `hn' : ∀ t : ℝ, χ (inPlane i0 j0 (lowerUnip t)) = 1`.

Introduce `t`. Establish `e` using `key (inPlane i0 j0 boostInv) (inPlane i0 j0 (lowerUnip (t / 3))) (inPlane i0 j0 boost) (inPlane i0 j0 (lowerUnip (-(t / 3)))) (inPlane_mem i0 j0 _ boostInv_mem) (inPlane_mem i0 j0 _ (lowerUnip_mem _)) (inPlane_mem i0 j0 _ boost_mem) (inPlane_mem i0 j0 _ (lowerUnip_mem _)) (by rw …`. Rewrite `e` using `[← inPlane_mul, ← inPlane_mul, ← inPlane_mul, lowerUnip_comm, show 3 * (t / 3) = t by ring]`. Then use the resulting hypothesis. Establish `m` using `inPlane_mem i0 j0 _ (upperUnip_mem x)`. Establish `m'` using `inPlane_mem i0 j0 _ (lowerUnip_mem (2 * x / (1 + 4 * x ^ 2)))`.

Rewrite using `[← inPlane_diag, ← rot_eq, inPlane_mul, inPlane_mul, hmul _ _ (hG _ _ m m') m, hmul _ _ m m']`. Simplify using `only [hn, hn', mul_one]`.
-/
theorem char_eq_one_rot : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∀ (i0 : Fin R) (j0 : Fin S) (x : ℝ),
      χ (Matrix.fromBlocks (Matrix.diagonal (Function.update 1 i0 ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)))) 0 0
        (Matrix.diagonal (Function.update 1 j0 ((1 - 2 * Complex.I * x) / (1 + 2 * Complex.I * x))))) = 1 := by
  intro R S χ hmul _ hne i0 j0 x
  have hG : ∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S →
      (g * h)ᴴ * Jm R S * (g * h) = Jm R S := by
    intro g h hg hh
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Jm R S * (g * h) = hᴴ * (gᴴ * Jm R S * g) * h := by simp only [Matrix.mul_assoc]
      _ = Jm R S := by rw [hg, hh]
  have h1mem : (1 : Mat R S)ᴴ * Jm R S * 1 = Jm R S := by simp
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 h1mem h1mem
    rw [Matrix.one_mul] at e
    exact mul_left_cancel₀ (hne 1 h1mem) (e.symm.trans (mul_one _).symm)
  have key : ∀ a b c d : Mat R S, aᴴ * Jm R S * a = Jm R S → bᴴ * Jm R S * b = Jm R S →
      cᴴ * Jm R S * c = Jm R S → dᴴ * Jm R S * d = Jm R S → a * c = 1 → b * d = 1 → χ (a * b * c * d) = 1 := by
    intro a b c d ha hb hc hd hac hbd
    have hab := hG a b ha hb
    have habc := hG _ c hab hc
    rw [hmul _ d habc hd, hmul _ c hab hc, hmul a b ha hb]
    have e1 := hmul a c ha hc
    have e2 := hmul b d hb hd
    rw [hac, h1] at e1
    rw [hbd, h1] at e2
    linear_combination (-(χ b * χ d)) * e1 - e2
  have hn : ∀ t : ℝ, χ (inPlane i0 j0 (upperUnip t)) = 1 := by
    intro t
    have e := key (inPlane i0 j0 boost) (inPlane i0 j0 (upperUnip (t / 3))) (inPlane i0 j0 boostInv) (inPlane i0 j0 (upperUnip (-(t / 3))))
      (inPlane_mem i0 j0 _ boost_mem) (inPlane_mem i0 j0 _ (upperUnip_mem _)) (inPlane_mem i0 j0 _ boostInv_mem) (inPlane_mem i0 j0 _ (upperUnip_mem _))
      (by rw [← inPlane_mul, boost_boostInv, inPlane_one]) (by rw [← inPlane_mul, upperUnip_neg, inPlane_one])
    rwa [← inPlane_mul, ← inPlane_mul, ← inPlane_mul, upperUnip_comm, show 3 * (t / 3) = t by ring] at e
  have hn' : ∀ t : ℝ, χ (inPlane i0 j0 (lowerUnip t)) = 1 := by
    intro t
    have e := key (inPlane i0 j0 boostInv) (inPlane i0 j0 (lowerUnip (t / 3))) (inPlane i0 j0 boost) (inPlane i0 j0 (lowerUnip (-(t / 3))))
      (inPlane_mem i0 j0 _ boostInv_mem) (inPlane_mem i0 j0 _ (lowerUnip_mem _)) (inPlane_mem i0 j0 _ boost_mem) (inPlane_mem i0 j0 _ (lowerUnip_mem _))
      (by rw [← inPlane_mul, boostInv_boost, inPlane_one]) (by rw [← inPlane_mul, lowerUnip_neg, inPlane_one])
    rwa [← inPlane_mul, ← inPlane_mul, ← inPlane_mul, lowerUnip_comm, show 3 * (t / 3) = t by ring] at e
  have m := inPlane_mem i0 j0 _ (upperUnip_mem x)
  have m' := inPlane_mem i0 j0 _ (lowerUnip_mem (2 * x / (1 + 4 * x ^ 2)))
  rw [← inPlane_diag, ← rot_eq, inPlane_mul, inPlane_mul, hmul _ _ (hG _ _ m m') m, hmul _ _ m m']
  simp only [hn, hn', mul_one]

end GlobalTheory.UnitaryCharRot
