import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContDiffAtSecondCoordinate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul

namespace Formalism.FourierDecayAlt.P.PBI

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.Ux3 Formalism.FourierDecayAlt.P.PBI.Sm
open scoped ComplexConjugate

noncomputable section

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section msgen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {m n : Type*} [Fintype m] [Fintype n]

/- English proof (translation)
Introduce `i j` and use `by simpa only [Matrix.neg_apply] using (hf i j).neg`.
-/
theorem ms_neg {f : E → Matrix m n ℂ} (hf : MS f x) : MS (fun y => -f y) x :=
  fun i j => by simpa only [Matrix.neg_apply] using (hf i j).neg

/- English proof (translation)
The claim follows from `ms_smul contDiffAt_const hf`.
-/
theorem ms_csmul (c : ℂ) {f : E → Matrix m n ℂ} (hf : MS f x) : MS (fun y => c • f y) x :=
  ms_smul contDiffAt_const hf

/- English proof (translation)
Introduce and unpack `(i | i) (l | l)`. Simplify using `using hA i l`. Simplify using `using hB i l`. Simplify using `using hC i l`. Simplify using `using hD i l`.
-/
theorem ms_fromBlocks {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
    {A : E → Matrix m₁ n₁ ℂ} {B : E → Matrix m₁ n₂ ℂ} {C : E → Matrix m₂ n₁ ℂ} {D : E → Matrix m₂ n₂ ℂ}
    (hA : MS A x) (hB : MS B x) (hC : MS C x) (hD : MS D x) :
    MS (fun y => Matrix.fromBlocks (A y) (B y) (C y) (D y)) x := by
  rintro (i | i) (l | l)
  · simpa using hA i l
  · simpa using hB i l
  · simpa using hC i l
  · simpa using hD i l

/- English proof (translation)
Introduce and unpack `(i | i) l`. Simplify using `using hA i l`. Simplify using `using hB i l`.
-/
theorem ms_fromRows {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    {A : E → Matrix m₁ n ℂ} {B : E → Matrix m₂ n ℂ} (hA : MS A x) (hB : MS B x) :
    MS (fun y => Matrix.fromRows (A y) (B y)) x := by
  rintro (i | i) l
  · simpa using hA i l
  · simpa using hB i l

/- English proof (translation)
Introduce `i l`. Break down `l with l | l` into its components or cases. Simplify using `using hA i l`. Simplify using `using hB i l`.
-/
theorem ms_fromCols {n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂]
    {A : E → Matrix m n₁ ℂ} {B : E → Matrix m n₂ ℂ} (hA : MS A x) (hB : MS B x) :
    MS (fun y => Matrix.fromCols (A y) (B y)) x := by
  intro i l
  rcases l with l | l
  · simpa using hA i l
  · simpa using hB i l

end msgen

section chart

variable {k j ρ : ℕ}

/- English proof (translation)
Introduce `i l`. Establish `h` using `ms_fromBlocks (ms_fromBlocks h11 h12 h21 h22) (ms_fromRows h13 h23) (ms_fromCols h31 h32) h33 ((eB k j ρ).symm i) ((eB k j ρ).symm l)`. Simplify `h` using `[blk3, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem measurable_block_three {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    {A11 : E → Matrix (Fin j) (Fin j) ℂ} {A12 : E → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : E → Matrix (Fin j) (Fin j) ℂ} {A21 : E → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : E → B.Mat k ρ}
    {A23 : E → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : E → Matrix (Fin j) (Fin j) ℂ}
    {A32 : E → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : E → Matrix (Fin j) (Fin j) ℂ}
    (h11 : MS A11 x) (h12 : MS A12 x) (h13 : MS A13 x) (h21 : MS A21 x) (h22 : MS A22 x) (h23 : MS A23 x)
    (h31 : MS A31 x) (h32 : MS A32 x) (h33 : MS A33 x) :
    MS (fun y => blk3 (k := k) (j := j) (ρ := ρ) (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y)
      (A33 y)) x := by
  intro i l
  have h := ms_fromBlocks (ms_fromBlocks h11 h12 h21 h22) (ms_fromRows h13 h23) (ms_fromCols h31 h32) h33
    ((eB k j ρ).symm i) ((eB k j ρ).symm l)
  simpa [blk3, Matrix.reindex_apply, Matrix.submatrix_apply] using h

/- English proof (translation)
Introduce `i l` and use `by have h := contDiffAt_pi.1 (contDiffAt_pi.1 (contDiffAt_id (𝕜 := ℝ) (n := ∞') (x := y₀)) i) l simpa using h`.
-/
theorem ms_ofMt (y₀ : Mt k j) : MS (fun y : Mt k j => Matrix.of y) y₀ := fun i l => by
  have h := contDiffAt_pi.1 (contDiffAt_pi.1 (contDiffAt_id (𝕜 := ℝ) (n := ∞') (x := y₀)) i) l
  simpa using h

def bk11 (M : B.Mat k (j + ρ)) : Matrix (Fin j) (Fin j) ℂ :=
  M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inl b)))
def bk21 (M : B.Mat k (j + ρ)) : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ :=
  M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inl (Sum.inl b)))
def bk22 (M : B.Mat k (j + ρ)) : B.Mat k ρ :=
  M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b)))
def bk31 (M : B.Mat k (j + ρ)) : Matrix (Fin j) (Fin j) ℂ :=
  M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inl (Sum.inl b)))
def bk32 (M : B.Mat k (j + ρ)) : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ :=
  M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inl (Sum.inr b)))
def bk33 (M : B.Mat k (j + ρ)) : Matrix (Fin j) (Fin j) ℂ :=
  M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inr b))

def chC (M : B.Mat k (j + ρ)) : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ := -(bk21 M * (bk31 M)⁻¹)
def chS (M : B.Mat k (j + ρ)) : Matrix (Fin j) (Fin j) ℂ :=
  G.wMat j * (-(G.wMat j * (chC M)ᴴ * Hpk k ρ) * chC M - bk11 M * (bk31 M)⁻¹) +
    (1 / 2 : ℂ) • ((chC M)ᴴ * Hpk k ρ * chC M)

def chC' (M : B.Mat k (j + ρ)) : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ :=
  -(Hpk k ρ * ((bk31 M)⁻¹ * bk32 M)ᴴ * G.wMat j)
def chS' (M : B.Mat k (j + ρ)) : Matrix (Fin j) (Fin j) ℂ :=
  G.wMat j * ((bk31 M)⁻¹ * bk33 M) + (1 / 2 : ℂ) • ((chC' M)ᴴ * Hpk k ρ * chC' M)
def chX (M : B.Mat k (j + ρ)) : RC k j ρ := (Matrix.of.symm (chC M), skewCoords (chS M))
def chX' (M : B.Mat k (j + ρ)) : RC k j ρ := (Matrix.of.symm (chC' M), skewCoords (chS' M))

def chZ (M : B.Mat k (j + ρ)) : Matrix (Fin j) (Fin j) ℂ := G.wMat j * bk31 M
def chMu (M : B.Mat k (j + ρ)) : B.Mat k ρ := bk22 (Rn k j ρ (chX M) * M * (Rn k j ρ (chX' M))⁻¹)

def chart (y : Mt k (j + ρ)) : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) :=
  ((chX (Matrix.of y), chX' (Matrix.of y)), (Matrix.of.symm (chZ (Matrix.of y)), Matrix.of.symm (chMu (Matrix.of y))))

end chart

section smooth

variable {k j ρ : ℕ}

/- English proof (translation)
Introduce `a b`. Establish `e : (fun y => skewOf (skewCoords (S y)) a b) = fun y => (if a < b then S y a b else 0) - (if b < a then conj (S y b a) else 0) + (if a = b then Complex.I * (((S y a a).im : ℝ) : ℂ) else 0)`. Use function extensionality and compare the values at `y`. Simplify using `only [skewOf, skewCoords, G.strictUpper, Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hab : a < b`.

Establish `hba : ¬ b < a` using `fun h => absurd (lt_trans hab h) (lt_irrefl a)`. Establish `hne : a ≠ b` using `ne_of_lt hab`. Simplify using `[hab, hba, hne]`. Distinguish the cases in `hba : b < a`. Establish `hne : a ≠ b` using `ne_of_gt hba`.

Simplify using `[hab, hba, hne, Complex.star_def]`. Establish `hab' : a = b` using `le_antisymm (not_lt.1 hba) (not_lt.1 hab)`. Substitute `hab'` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Use `ContDiffAt.add (ContDiffAt.sub ?_ ?_) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hS a b`. Conclude with `contDiffAt_const`. Use `split_ifs`.

Conclude with `cd_conj (hS b a)`. Conclude with `contDiffAt_const`. Use `split_ifs`. Conclude with `contDiffAt_const.mul (cd_ofReal ((Complex.imCLM.contDiff (n := ∞')).contDiffAt.comp _ (hS a a)))`. Conclude with `contDiffAt_const`.
-/
theorem ms_skewOfCoords {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    {S : E → Matrix (Fin j) (Fin j) ℂ} (hS : MS S x) : MS (fun y => skewOf (skewCoords (S y))) x := by
  intro a b
  have e : (fun y => skewOf (skewCoords (S y)) a b) = fun y =>
      (if a < b then S y a b else 0) - (if b < a then conj (S y b a) else 0) +
        (if a = b then Complex.I * (((S y a a).im : ℝ) : ℂ) else 0) := by
    funext y
    simp only [skewOf, skewCoords, G.strictUpper, Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hab : a < b
    · have hba : ¬ b < a := fun h => absurd (lt_trans hab h) (lt_irrefl a)
      have hne : a ≠ b := ne_of_lt hab
      simp [hab, hba, hne]
    · by_cases hba : b < a
      · have hne : a ≠ b := ne_of_gt hba
        simp [hab, hba, hne, Complex.star_def]
      · have hab' : a = b := le_antisymm (not_lt.1 hba) (not_lt.1 hab)
        subst hab'
        simp
  rw [e]
  refine ContDiffAt.add (ContDiffAt.sub ?_ ?_) ?_
  · split_ifs
    · exact hS a b
    · exact contDiffAt_const
  · split_ifs
    · exact cd_conj (hS b a)
    · exact contDiffAt_const
  · split_ifs
    · exact contDiffAt_const.mul (cd_ofReal ((Complex.imCLM.contDiff (n := ∞')).contDiffAt.comp _ (hS a a)))
    · exact contDiffAt_const

/- English proof (translation)
Simplify using `only [rn_eq, Equiv.apply_symm_apply]`. Use `measurable_block_three (ms_const _) ?_ ?_ (ms_const _) (ms_const _) hC (ms_const _) (ms_const _) (ms_const _)` and prove the remaining obligations. Conclude with `ms_neg (ms_mul (ms_mul (ms_const _) (ms_conjT hC)) (ms_const _))`. Conclude with `ms_mul (ms_const _) (ms_add (ms_csmul _ (ms_mul (ms_mul (ms_conjT hC) (ms_const _)) hC)) (ms_skewOfCoords hS))`.
-/
theorem ms_rn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    {C : E → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {S : E → Matrix (Fin j) (Fin j) ℂ} (hC : MS C x) (hS : MS S x) :
    MS (fun y => Rn k j ρ (Matrix.of.symm (C y), skewCoords (S y))) x := by
  simp only [rn_eq, Equiv.apply_symm_apply]
  refine measurable_block_three (ms_const _) ?_ ?_ (ms_const _) (ms_const _) hC (ms_const _) (ms_const _) (ms_const _)
  · exact ms_neg (ms_mul (ms_mul (ms_const _) (ms_conjT hC)) (ms_const _))
  · exact ms_mul (ms_const _) (ms_add (ms_csmul _ (ms_mul (ms_mul (ms_conjT hC) (ms_const _)) hC))
      (ms_skewOfCoords hS))

/- English proof (translation)
Simplify using `only [rn_eq, uni_inv, Equiv.apply_symm_apply]`. Establish `ha` using `ms_neg (ms_mul (ms_mul (ms_const (G.wMat j)) (ms_conjT hC)) (ms_const (Hpk k ρ)))`. Establish `hb` using `ms_mul (ms_const (G.wMat j)) (ms_add (ms_csmul (-(1 / 2 : ℂ)) (ms_mul (ms_mul (ms_conjT hC) (ms_const (Hpk k ρ))) hC)) (ms_skewOfCoords hS))`. Conclude with `measurable_block_three (ms_const _) (ms_neg ha) (ms_sub (ms_mul ha hC) hb) (ms_const _) (ms_const _) (ms_neg hC) (ms_const _) (ms_const _) (ms_const _)`.
-/
theorem ms_rn_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    {C : E → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {S : E → Matrix (Fin j) (Fin j) ℂ} (hC : MS C x) (hS : MS S x) :
    MS (fun y => (Rn k j ρ (Matrix.of.symm (C y), skewCoords (S y)))⁻¹) x := by
  simp only [rn_eq, uni_inv, Equiv.apply_symm_apply]
  have ha := ms_neg (ms_mul (ms_mul (ms_const (G.wMat j)) (ms_conjT hC)) (ms_const (Hpk k ρ)))
  have hb := ms_mul (ms_const (G.wMat j)) (ms_add (ms_csmul (-(1 / 2 : ℂ))
    (ms_mul (ms_mul (ms_conjT hC) (ms_const (Hpk k ρ))) hC)) (ms_skewOfCoords hS))
  exact measurable_block_three (ms_const _) (ms_neg ha) (ms_sub (ms_mul ha hC) hb) (ms_const _) (ms_const _) (ms_neg hC)
    (ms_const _) (ms_const _) (ms_const _)

/- English proof (translation)
Establish `hM` using `ms_ofMt (k := k) (j := j + ρ) y₀`. Establish `h11 : MS (fun y : Mt k (j + ρ) => bk11 (Matrix.of y)) y₀` using `ms_submatrix hM _ _`. Establish `h21 : MS (fun y : Mt k (j + ρ) => bk21 (Matrix.of y)) y₀` using `ms_submatrix hM _ _`. Establish `h31 : MS (fun y : Mt k (j + ρ) => bk31 (Matrix.of y)) y₀` using `ms_submatrix hM _ _`. Establish `h32 : MS (fun y : Mt k (j + ρ) => bk32 (Matrix.of y)) y₀` using `ms_submatrix hM _ _`.

Establish `h33 : MS (fun y : Mt k (j + ρ) => bk33 (Matrix.of y)) y₀` using `ms_submatrix hM _ _`. Establish `hinv : MS (fun y : Mt k (j + ρ) => (bk31 (Matrix.of y))⁻¹) y₀` using `ms_inv h31 h₀`. Establish `hC : MS (fun y : Mt k (j + ρ) => chC (Matrix.of y)) y₀` using `ms_neg (ms_mul h21 hinv)`. Establish `hS : MS (fun y : Mt k (j + ρ) => chS (Matrix.of y)) y₀` using `ms_add (ms_mul (ms_const _) (ms_sub (ms_mul (ms_neg (ms_mul (ms_mul (ms_const _) (ms_conjT hC)) (ms_const _))) hC) (ms_mul h11 hinv))) (ms_csmul _ (ms_mul (ms_mul (ms_conjT hC) (ms_const _)) hC))`. Establish `hC' : MS (fun y : Mt k (j + ρ) => chC' (Matrix.of y)) y₀` using `ms_neg (ms_mul (ms_mul (ms_const _) (ms_conjT (ms_mul hinv h32))) (ms_const _))`.

Establish `hS' : MS (fun y : Mt k (j + ρ) => chS' (Matrix.of y)) y₀` using `ms_add (ms_mul (ms_const _) (ms_mul hinv h33)) (ms_csmul _ (ms_mul (ms_mul (ms_conjT hC') (ms_const _)) hC'))`. Establish `hZ : MS (fun y : Mt k (j + ρ) => chZ (Matrix.of y)) y₀` using `ms_mul (ms_const _) h31`. Establish `hMu : MS (fun y : Mt k (j + ρ) => chMu (Matrix.of y)) y₀` using `ms_submatrix (ms_mul (ms_mul (ms_rn hC hS) hM) (ms_rn_inv hC' hS')) _ _`. Establish `hX : ∀ {Cf : Mt k (j + ρ) → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {Sf : Mt k (j + ρ) → Matrix (Fin j) (Fin j) ℂ}, MS Cf y₀ → MS Sf y₀ → ContDiffAt ℝ ∞' (fun y => ((Matrix.of.symm (Cf y), skewCoords (Sf y)) : RC k j ρ)) y₀`. Introduce `Cf Sf hCf hSf`.

Use `ContDiffAt.prodMk ?_ (ContDiffAt.prodMk ?_ ?_)` and prove the remaining obligations. Conclude with `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun a => by simpa using hCf i a`. Conclude with `contDiffAt_pi.2 fun q => by simpa [skewCoords] using hSf q.1.1 q.1.2`. Conclude with `contDiffAt_pi.2 fun i => by`. Establish `h` using `(Complex.imCLM.contDiff (n := ∞')).contDiffAt.comp _ (hSf i i)`.

Simplify using `only [Function.comp_def, Complex.imCLM_apply] at h`. Simplify `h` using `[skewCoords]`. Use `ContDiffAt.prodMk (ContDiffAt.prodMk (hX hC hS) (hX hC' hS')) (ContDiffAt.prodMk ?_ ?_)` and prove the remaining obligations. Conclude with `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun a => by simpa using hZ i a`. Conclude with `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun a => by simpa using hMu i a`.
-/
theorem chart_contDiffAt (y₀ : Mt k (j + ρ)) (h₀ : (bk31 (Matrix.of y₀)).det ≠ 0) :
    ContDiffAt ℝ ∞' (chart (k := k) (j := j) (ρ := ρ)) y₀ := by
  have hM := ms_ofMt (k := k) (j := j + ρ) y₀
  have h11 : MS (fun y : Mt k (j + ρ) => bk11 (Matrix.of y)) y₀ := ms_submatrix hM _ _
  have h21 : MS (fun y : Mt k (j + ρ) => bk21 (Matrix.of y)) y₀ := ms_submatrix hM _ _
  have h31 : MS (fun y : Mt k (j + ρ) => bk31 (Matrix.of y)) y₀ := ms_submatrix hM _ _
  have h32 : MS (fun y : Mt k (j + ρ) => bk32 (Matrix.of y)) y₀ := ms_submatrix hM _ _
  have h33 : MS (fun y : Mt k (j + ρ) => bk33 (Matrix.of y)) y₀ := ms_submatrix hM _ _
  have hinv : MS (fun y : Mt k (j + ρ) => (bk31 (Matrix.of y))⁻¹) y₀ := ms_inv h31 h₀
  have hC : MS (fun y : Mt k (j + ρ) => chC (Matrix.of y)) y₀ := ms_neg (ms_mul h21 hinv)
  have hS : MS (fun y : Mt k (j + ρ) => chS (Matrix.of y)) y₀ :=
    ms_add (ms_mul (ms_const _) (ms_sub (ms_mul (ms_neg (ms_mul (ms_mul (ms_const _) (ms_conjT hC))
      (ms_const _))) hC) (ms_mul h11 hinv))) (ms_csmul _ (ms_mul (ms_mul (ms_conjT hC) (ms_const _)) hC))
  have hC' : MS (fun y : Mt k (j + ρ) => chC' (Matrix.of y)) y₀ :=
    ms_neg (ms_mul (ms_mul (ms_const _) (ms_conjT (ms_mul hinv h32))) (ms_const _))
  have hS' : MS (fun y : Mt k (j + ρ) => chS' (Matrix.of y)) y₀ :=
    ms_add (ms_mul (ms_const _) (ms_mul hinv h33)) (ms_csmul _ (ms_mul (ms_mul (ms_conjT hC') (ms_const _)) hC'))
  have hZ : MS (fun y : Mt k (j + ρ) => chZ (Matrix.of y)) y₀ := ms_mul (ms_const _) h31
  have hMu : MS (fun y : Mt k (j + ρ) => chMu (Matrix.of y)) y₀ :=
    ms_submatrix (ms_mul (ms_mul (ms_rn hC hS) hM) (ms_rn_inv hC' hS')) _ _
  have hX : ∀ {Cf : Mt k (j + ρ) → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ}
      {Sf : Mt k (j + ρ) → Matrix (Fin j) (Fin j) ℂ}, MS Cf y₀ → MS Sf y₀ →
      ContDiffAt ℝ ∞' (fun y => ((Matrix.of.symm (Cf y), skewCoords (Sf y)) : RC k j ρ)) y₀ := by
    intro Cf Sf hCf hSf
    refine ContDiffAt.prodMk ?_ (ContDiffAt.prodMk ?_ ?_)
    · exact contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun a => by simpa using hCf i a
    · exact contDiffAt_pi.2 fun q => by simpa [skewCoords] using hSf q.1.1 q.1.2
    · exact contDiffAt_pi.2 fun i => by
        have h := (Complex.imCLM.contDiff (n := ∞')).contDiffAt.comp _ (hSf i i)
        simp only [Function.comp_def, Complex.imCLM_apply] at h
        simpa [skewCoords] using h
  refine ContDiffAt.prodMk (ContDiffAt.prodMk (hX hC hS) (hX hC' hS')) (ContDiffAt.prodMk ?_ ?_)
  · exact contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun a => by simpa using hZ i a
  · exact contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun a => by simpa using hMu i a

/- English proof (translation)
Introduce `y hy` and use `(chart_contDiffAt y hy).contDiffWithinAt`.
-/
theorem chart_contDiffOn :
    ContDiffOn ℝ ∞' (chart (k := k) (j := j) (ρ := ρ)) {y | (bk31 (Matrix.of y)).det ≠ 0} :=
  fun y hy => (chart_contDiffAt y hy).contDiffWithinAt

/- English proof (translation)
Establish `hc : Continuous fun y : Mt k (j + ρ) => (bk31 (Matrix.of y)).det`. Unfold `bk31`. Use `fun_prop`. Conclude with `isOpen_ne_fun hc continuous_const`.
-/
theorem isOpen_det_bottom_left_ne_zero : IsOpen {y : Mt k (j + ρ) | (bk31 (Matrix.of y)).det ≠ 0} := by
  have hc : Continuous fun y : Mt k (j + ρ) => (bk31 (Matrix.of y)).det := by
    unfold bk31
    fun_prop
  exact isOpen_ne_fun hc continuous_const

end smooth

section ident

variable {k j ρ : ℕ}

section blocks
variable (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
  (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
  (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[bk11, block3_apply]`.
-/
theorem block_three_top_left : bk11 (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = A11 := by ext a b; simp [bk11, block3_apply]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[bk21, block3_apply]`.
-/
theorem block_three_middle_left : bk21 (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = A21 := by ext a b; simp [bk21, block3_apply]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[bk22, block3_apply]`.
-/
theorem block_three_center : bk22 (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = A22 := by ext a b; simp [bk22, block3_apply]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[bk31, block3_apply, Matrix.fromCols_apply_inl]`.
-/
theorem block_three_bottom_left : bk31 (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = A31 := by
  ext a b; simp [bk31, block3_apply, Matrix.fromCols_apply_inl]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[bk32, block3_apply, Matrix.fromCols_apply_inr]`.
-/
theorem block_three_bottom_center : bk32 (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = A32 := by
  ext a b; simp [bk32, block3_apply, Matrix.fromCols_apply_inr]
/- English proof (translation)
Use extensionality with `a b`. Simplify using `[bk33, block3_apply]`.
-/
theorem block_three_bottom_right : bk33 (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = A33 := by ext a b; simp [bk33, block3_apply]

end blocks

/- English proof (translation)
Apply `skewOf_inj` to reduce the goal to its premises. Conclude with `skewOf_coords _ (skewOf_conjTranspose _)`.
-/
theorem skewCoords_skewOf {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) : skewCoords (skewOf q) = q := by
  apply skewOf_inj
  exact skewOf_coords _ (skewOf_conjTranspose _)

/- English proof (translation)
Take `⟨x, x', Z, γ, hZ, hγ, hgeq⟩` from `bigCell_exists g hg hD`. It suffices to establish `hx : chX g = x ∧ chX' g = x' ∧ chZ g = Z ∧ chMu g = γ by`. Take `⟨h1, h2, h3, h4⟩` from `hx`. Rewrite using `[h1, h2, h3, h4]`. Conclude with `⟨hZ, hγ, hgeq⟩`.

Establish `hb : g = blk3 ((-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * Matrix.of x.1 - G.wMat j * (-(1 / 2 : ℂ) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2)) * (G.wMat j * Z)) ((-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * Matrix.of x.1 - G.wMat j * (-(1 / 2 : ℂ) • ((Matrix.of …`. Rewrite using `[hgeq, rn_eq, rn_eq, uni_inv]`. Unfold `mMap`. Rewrite using `[block3_mul, block3_mul]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]`.

Establish `hu : IsUnit (G.wMat j * Z).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `(wMat_det j).mul (isUnit_iff_ne_zero.mpr hZ)`. Establish `hWW : G.wMat j * G.wMat j = 1` using `wMat_mul_self j`. Establish `hHH : Hpk k ρ * Hpk k ρ = 1` using `hpk_sq k ρ`.

Establish `i1 : (G.wMat j * Z) * (G.wMat j * Z)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `i2 : (G.wMat j * Z)⁻¹ * (G.wMat j * Z) = 1` using `Matrix.nonsing_inv_mul _ hu`. Establish `e31 : bk31 g = G.wMat j * Z` using `by rw [hb, block_three_bottom_left]`. Establish `eZ : chZ g = Z`. Unfold `chZ`.

Rewrite using `[e31, ← Matrix.mul_assoc, hWW, Matrix.one_mul]`. Establish `eC : chC g = Matrix.of x.1`. Unfold `chC`. Rewrite using `[e31, hb, block_three_middle_left]`. Simplify using `only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc, i1, Matrix.mul_one]`.

Establish `eC' : chC' g = Matrix.of x'.1`. Unfold `chC'`. Rewrite using `[e31, hb, block_three_bottom_center, ← Matrix.mul_assoc, i2, Matrix.one_mul]`. Simplify using `only [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, wMat_conjTranspose, hpk_herm, Matrix.conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hHH, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, hWW, Matrix.mul_one]`.

Establish `eS' : chS' g = skewOf x'.2`. Unfold `chS'`. Rewrite using `[eC', e31, hb, block_three_bottom_right, ← Matrix.mul_assoc (G.wMat j * Z)⁻¹, i2, Matrix.one_mul, ← Matrix.mul_assoc, hWW, Matrix.one_mul]`. Use `module`. Establish `eS : chS g = skewOf x.2`.

Unfold `chS`. Rewrite using `[eC, e31, hb, block_three_top_left, Matrix.mul_assoc _ (G.wMat j * Z), i1, Matrix.mul_one]`. Simplify using `only [sub_sub_cancel_left, Matrix.mul_neg, neg_neg, Matrix.mul_add, ← Matrix.mul_assoc, hWW, Matrix.one_mul, Matrix.mul_sub]`. Use `module`. Establish `eX : chX g = x`.

Unfold `chX`. Rewrite using `[eC, eS, Equiv.symm_apply_apply, skewCoords_skewOf]`. Establish `eX' : chX' g = x'`. Unfold `chX'`. Rewrite using `[eC', eS', Equiv.symm_apply_apply, skewCoords_skewOf]`.

Use `⟨eX, eX', eZ, ?_⟩` and prove the remaining obligations. Unfold `chMu`. Rewrite using `[eX, eX']`. Use `conv_lhs => rw [hgeq]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, rn_mul_inv, Matrix.one_mul, Matrix.mul_assoc, rn_mul_inv, Matrix.mul_one]`.

Unfold `mMap`. Rewrite using `[block_three_center]`.
-/
theorem chart_spec (g : B.Mat k (j + ρ)) (hg : g ∈ B.GV k (j + ρ)) (hD : DjU k j ρ g ≠ 0) :
    (chZ g).det ≠ 0 ∧ chMu g ∈ B.GV k ρ ∧
      g = (Rn k j ρ (chX g))⁻¹ * mMap k j ρ (chZ g) (chMu g) * Rn k j ρ (chX' g) := by
  obtain ⟨x, x', Z, γ, hZ, hγ, hgeq⟩ := bigCell_exists g hg hD
  suffices hx : chX g = x ∧ chX' g = x' ∧ chZ g = Z ∧ chMu g = γ by
    obtain ⟨h1, h2, h3, h4⟩ := hx
    rw [h1, h2, h3, h4]
    exact ⟨hZ, hγ, hgeq⟩
  have hb : g = blk3
      ((-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * Matrix.of x.1 -
          G.wMat j * (-(1 / 2 : ℂ) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2)) * (G.wMat j * Z))
      ((-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * Matrix.of x.1 -
          G.wMat j * (-(1 / 2 : ℂ) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2)) * (G.wMat j * Z) *
          -(G.wMat j * (Matrix.of x'.1)ᴴ * Hpk k ρ) + - -(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * γ)
      ((-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * Matrix.of x.1 -
          G.wMat j * (-(1 / 2 : ℂ) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2)) * (G.wMat j * Z) *
          (G.wMat j * (-(1 / 2 : ℂ) • ((Matrix.of x'.1)ᴴ * Hpk k ρ * Matrix.of x'.1) + skewOf x'.2)) +
        - -(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * γ * Matrix.of x'.1 + Zᴴ⁻¹ * G.wMat j)
      (-Matrix.of x.1 * (G.wMat j * Z))
      (-Matrix.of x.1 * (G.wMat j * Z) * -(G.wMat j * (Matrix.of x'.1)ᴴ * Hpk k ρ) + γ)
      (-Matrix.of x.1 * (G.wMat j * Z) *
          (G.wMat j * (-(1 / 2 : ℂ) • ((Matrix.of x'.1)ᴴ * Hpk k ρ * Matrix.of x'.1) + skewOf x'.2)) +
        γ * Matrix.of x'.1)
      (G.wMat j * Z) (G.wMat j * Z * -(G.wMat j * (Matrix.of x'.1)ᴴ * Hpk k ρ))
      (G.wMat j * Z * (G.wMat j * (-(1 / 2 : ℂ) • ((Matrix.of x'.1)ᴴ * Hpk k ρ * Matrix.of x'.1) + skewOf x'.2))) := by
    rw [hgeq, rn_eq, rn_eq, uni_inv]
    unfold mMap
    rw [block3_mul, block3_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  have hu : IsUnit (G.wMat j * Z).det := by
    rw [Matrix.det_mul]; exact (wMat_det j).mul (isUnit_iff_ne_zero.mpr hZ)
  have hWW : G.wMat j * G.wMat j = 1 := wMat_mul_self j
  have hHH : Hpk k ρ * Hpk k ρ = 1 := hpk_sq k ρ
  have i1 : (G.wMat j * Z) * (G.wMat j * Z)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have i2 : (G.wMat j * Z)⁻¹ * (G.wMat j * Z) = 1 := Matrix.nonsing_inv_mul _ hu
  have e31 : bk31 g = G.wMat j * Z := by rw [hb, block_three_bottom_left]
  have eZ : chZ g = Z := by
    unfold chZ; rw [e31, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have eC : chC g = Matrix.of x.1 := by
    unfold chC
    rw [e31, hb, block_three_middle_left]
    simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc, i1, Matrix.mul_one]
  have eC' : chC' g = Matrix.of x'.1 := by
    unfold chC'
    rw [e31, hb, block_three_bottom_center, ← Matrix.mul_assoc, i2, Matrix.one_mul]
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, wMat_conjTranspose, hpk_herm,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hHH,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  have eS' : chS' g = skewOf x'.2 := by
    unfold chS'
    rw [eC', e31, hb, block_three_bottom_right, ← Matrix.mul_assoc (G.wMat j * Z)⁻¹, i2, Matrix.one_mul, ← Matrix.mul_assoc, hWW,
      Matrix.one_mul]
    module
  have eS : chS g = skewOf x.2 := by
    unfold chS
    rw [eC, e31, hb, block_three_top_left, Matrix.mul_assoc _ (G.wMat j * Z), i1, Matrix.mul_one]
    simp only [sub_sub_cancel_left, Matrix.mul_neg, neg_neg, Matrix.mul_add, ← Matrix.mul_assoc, hWW,
      Matrix.one_mul, Matrix.mul_sub]
    module
  have eX : chX g = x := by
    unfold chX; rw [eC, eS, Equiv.symm_apply_apply, skewCoords_skewOf]
  have eX' : chX' g = x' := by
    unfold chX'; rw [eC', eS', Equiv.symm_apply_apply, skewCoords_skewOf]
  refine ⟨eX, eX', eZ, ?_⟩
  unfold chMu
  rw [eX, eX']
  conv_lhs => rw [hgeq]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rn_mul_inv, Matrix.one_mul, Matrix.mul_assoc, rn_mul_inv,
    Matrix.mul_one]
  unfold mMap
  rw [block_three_center]

/- English proof (translation)
Establish `h` using `hat_z_of_block3 (bk11 g) (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b)))) (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inr b))) (bk21 g) (bk22 g) (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a …`. Establish `e : g = blk3 (bk11 g) (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b)))) (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inr b))) (bk21 g) (bk22 g) (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) …` using `block3_eta g`. Unfold `DjU`. Use `conv_lhs => rw [e]`. Rewrite using `[h]`.
-/
theorem djU_eq (g : B.Mat k (j + ρ)) : DjU k j ρ g = (G.wMat j * bk31 g).det := by
  have h := hat_z_of_block3 (bk11 g) (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b))))
    (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inr b))) (bk21 g) (bk22 g)
    (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inr b))) (bk31 g) (bk32 g) (bk33 g)
  have e : g = blk3 (bk11 g) (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b))))
      (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inr b))) (bk21 g) (bk22 g)
      (g.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inr b))) (bk31 g) (bk32 g)
      (bk33 g) := block3_eta g
  unfold DjU
  conv_lhs => rw [e]
  rw [h]

/- English proof (translation)
Rewrite using `[djU_eq, Matrix.det_mul]`. Establish `hW` using `(wMat_det j).ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce `h h0; exact h (by rw [h0, mul_zero])`. Introduce `h`.

Conclude with `mul_ne_zero hW h`.
-/
theorem djU_ne_iff (g : B.Mat k (j + ρ)) : DjU k j ρ g ≠ 0 ↔ (bk31 g).det ≠ 0 := by
  rw [djU_eq, Matrix.det_mul]
  have hW := (wMat_det j).ne_zero
  constructor
  · intro h h0; exact h (by rw [h0, mul_zero])
  · intro h; exact mul_ne_zero hW h

end ident

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

/- English proof (translation)
Establish `hset : {y : Mt k (j + ρ) | DjU k j ρ (Matrix.of y) ≠ 0} = {y | (PBI.bk31 (Matrix.of y)).det ≠ 0}`. Use extensionality with `y`. Conclude with `PBI.djU_ne_iff _`. Use `⟨PBI.chart, by rw [hset]; exact PBI.isOpen_det_bottom_left_ne_zero, by rw [hset]; exact PBI.chart_contDiffOn, ?_⟩` and prove the remaining obligations. Introduce `g hg hD`.

Establish `h` using `PBI.chart_spec g hg hD`. Simplify `h` using `[PBI.chart]`.
-/
theorem pb_chartSmooth (k j ρ : ℕ) :
    ∃ φ : Mt k (j + ρ) → (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ),
      IsOpen {y : Mt k (j + ρ) | DjU k j ρ (Matrix.of y) ≠ 0} ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ {y | DjU k j ρ (Matrix.of y) ≠ 0} ∧
      ∀ g ∈ B.GV k (j + ρ), DjU k j ρ g ≠ 0 →
        (Matrix.of (φ (Matrix.of.symm g)).2.1).det ≠ 0 ∧ Matrix.of (φ (Matrix.of.symm g)).2.2 ∈ B.GV k ρ ∧
        g = (Rn k j ρ (φ (Matrix.of.symm g)).1.1)⁻¹ *
          mMap k j ρ (Matrix.of (φ (Matrix.of.symm g)).2.1) (Matrix.of (φ (Matrix.of.symm g)).2.2) *
          Rn k j ρ (φ (Matrix.of.symm g)).1.2 := by
  have hset : {y : Mt k (j + ρ) | DjU k j ρ (Matrix.of y) ≠ 0} = {y | (PBI.bk31 (Matrix.of y)).det ≠ 0} := by
    ext y; exact PBI.djU_ne_iff _
  refine ⟨PBI.chart, by rw [hset]; exact PBI.isOpen_det_bottom_left_ne_zero, by rw [hset]; exact PBI.chart_contDiffOn, ?_⟩
  intro g hg hD
  have h := PBI.chart_spec g hg hD
  simpa [PBI.chart] using h

end Formalism.FourierDecayAlt.P
