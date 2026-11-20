import Mathlib
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwasawaGen

/- English proof (translation)
Introduce `X hX`. Choose the witnesses or unpack the hypotheses as in `⟨P, hP, P_ent⟩ : ∃ P ∈ 𝔤, ∀ i j, P i j = if h j < h i then X i j else 0 := by`. Use `⟨_, hf (fun t => if 0 < t then 1 else 0) X hX, fun i j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hij : h j < h i`. Simplify using `[hij]`.

Simplify using `[hij]`. Choose the witnesses or unpack the hypotheses as in `⟨Z, hZ, Z_ent⟩ : ∃ Z ∈ 𝔤, ∀ i j, Z i j = if h i = h j then X i j else 0 := by`. Use `⟨_, hf (fun t => if t = 0 then 1 else 0) X hX, fun i j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hij : h i = h j`. Simplify using `[hij]`.

Simplify using `[hij, sub_eq_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM, M_ent⟩ : ∃ M ∈ 𝔤, ∀ i j, M i j = if h i < h j then X i j else 0 := by`. Use `⟨_, hf (fun t => if t < 0 then 1 else 0) X hX, fun i j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hij : h i < h j`. Simplify using `[hij]`.

Simplify using `[hij]`. Establish `hsum : X = P + Z + M`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, P_ent, Z_ent, M_ent]`. Break down `lt_trichotomy (h i) (h j) with hij | hij | hij` into its components or cases.

Simplify using `[hij, hij.ne, not_lt.2 hij.le]`. Simplify using `[hij]`. Simplify using `[hij, hij.ne', not_lt.2 hij.le]`. Use `set Y : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (Z + Zᴴ) with hYdef`. Establish `hY : Y ∈ 𝔤` using `𝔤.smul_mem _ (𝔤.add_mem hZ (hstar Z hZ))`.

Establish `Y_herm : Yᴴ = Y`. Use extensionality with `i j`. Simplify using `[hYdef, Matrix.conjTranspose_apply, add_comm]`. Establish `Y_ent : ∀ i j, h i ≠ h j → Y i j = 0`. Introduce `i j hij`.

Simplify using `[hYdef, Matrix.conjTranspose_apply, Z_ent, hij, hij.symm]`. Establish `Y_comm : Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ))`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Distinguish the cases in `hij : h i = h j`.

Rewrite using `[hij, mul_comm]`. Rewrite using `[Y_ent i j hij]`. Simplify using the standard rewrite rules. Establish `Y_diag : Y.IsDiag` using `hreg Y hY Y_herm Y_comm`. Use `⟨(1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ, ?_, P + Y + Mᴴ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `𝔤.sub_mem (𝔤.add_mem (𝔤.smul_mem _ (𝔤.sub_mem hZ (hstar Z hZ))) hM) (hstar M hM)`. Conclude with `𝔤.add_mem (𝔤.add_mem hP hY) (hstar M hM)`. Establish `hZsplit : Z = (1 / 2 : ℝ) • (Z - Zᴴ) + Y`. Rewrite using `[hYdef, ← smul_add]`. Establish `: Z - Zᴴ + (Z + Zᴴ) = (2 : ℝ) • Z`.

Rewrite using `[two_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this, smul_smul]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, star_trivial]`. Use extensionality with `i j`. Simplify using `only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply]`. Simplify using `only [smul_eq_mul, Complex.real_smul, smul_sub]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i j hji`. Establish `hji' : j < i` using `hji`. Establish `hle : h i ≤ h j` using `hanti hji'.le`. Establish `h1 : P i j = 0`. Rewrite using `[P_ent, if_neg (not_lt.2 hle)]`.

Establish `h2 : Y i j = 0` using `Y_diag hji'.ne'`. Establish `h3 : Mᴴ i j = 0`. Rewrite using `[Matrix.conjTranspose_apply, M_ent, if_neg (not_lt.2 hle)]`. Simplify using the standard rewrite rules. Simplify using `only [Matrix.add_apply, h1, h2, h3, add_zero]`.
-/
theorem skew_add_upper {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hanti : Antitone h)
    (hf : ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤)
    (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hreg : ∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) :
    ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  intro X hX
  obtain ⟨P, hP, P_ent⟩ : ∃ P ∈ 𝔤, ∀ i j, P i j = if h j < h i then X i j else 0 := by
    refine ⟨_, hf (fun t => if 0 < t then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h j < h i
    · simp [hij]
    · simp [hij]
  obtain ⟨Z, hZ, Z_ent⟩ : ∃ Z ∈ 𝔤, ∀ i j, Z i j = if h i = h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t = 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i = h j
    · simp [hij]
    · simp [hij, sub_eq_zero]
  obtain ⟨M, hM, M_ent⟩ : ∃ M ∈ 𝔤, ∀ i j, M i j = if h i < h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t < 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i < h j
    · simp [hij]
    · simp [hij]
  have hsum : X = P + Z + M := by
    ext i j
    simp only [Matrix.add_apply, P_ent, Z_ent, M_ent]
    rcases lt_trichotomy (h i) (h j) with hij | hij | hij
    · simp [hij, hij.ne, not_lt.2 hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt.2 hij.le]
  set Y : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (Z + Zᴴ) with hYdef
  have hY : Y ∈ 𝔤 := 𝔤.smul_mem _ (𝔤.add_mem hZ (hstar Z hZ))
  have Y_herm : Yᴴ = Y := by
    ext i j
    simp [hYdef, Matrix.conjTranspose_apply, add_comm]
  have Y_ent : ∀ i j, h i ≠ h j → Y i j = 0 := by
    intro i j hij
    simp [hYdef, Matrix.conjTranspose_apply, Z_ent, hij, hij.symm]
  have Y_comm : Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : h i = h j
    · rw [hij, mul_comm]
    · rw [Y_ent i j hij]; simp
  have Y_diag : Y.IsDiag := hreg Y hY Y_herm Y_comm
  refine ⟨(1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ, ?_, P + Y + Mᴴ, ?_, ?_, ?_, ?_⟩
  · exact 𝔤.sub_mem (𝔤.add_mem (𝔤.smul_mem _ (𝔤.sub_mem hZ (hstar Z hZ))) hM) (hstar M hM)
  · exact 𝔤.add_mem (𝔤.add_mem hP hY) (hstar M hM)
  · have hZsplit : Z = (1 / 2 : ℝ) • (Z - Zᴴ) + Y := by
      rw [hYdef, ← smul_add]
      have : Z - Zᴴ + (Z + Zᴴ) = (2 : ℝ) • Z := by
        rw [two_smul]; abel
      rw [this, smul_smul]; norm_num
    calc X = P + Z + M := hsum
      _ = P + ((1 / 2 : ℝ) • (Z - Zᴴ) + Y) + M := by rw [← hZsplit]
      _ = (1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ + (P + Y + Mᴴ) := by abel
  · simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_trivial]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply]
    simp only [smul_eq_mul, Complex.real_smul, smul_sub]
    ring
  · intro i j hji
    have hji' : j < i := hji
    have hle : h i ≤ h j := hanti hji'.le
    have h1 : P i j = 0 := by
      rw [P_ent, if_neg (not_lt.2 hle)]
    have h2 : Y i j = 0 := Y_diag hji'.ne'
    have h3 : Mᴴ i j = 0 := by
      rw [Matrix.conjTranspose_apply, M_ent, if_neg (not_lt.2 hle)]; simp
    simp only [Matrix.add_apply, h1, h2, h3, add_zero]

end GlobalTheory.CompanionTheory.IwasawaGen
