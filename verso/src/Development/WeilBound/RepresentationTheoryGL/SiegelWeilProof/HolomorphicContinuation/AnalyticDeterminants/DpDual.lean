import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

noncomputable section

open Matrix
open scoped ContDiff ComplexOrder

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

section detD

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Unfold `detD`. Rewrite using `[(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]`.
-/
theorem detD_congr {F G : Matrix ι ι ℂ → ℂ} (h : F =ᶠ[nhds 0] G) : detD F = detD G := by
  unfold detD
  rw [(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]

/- English proof (translation)
Unfold `detD`. Establish `e : iteratedFDeriv ℂ (Fintype.card ι) (fun T => c * F T) 0 = c • iteratedFDeriv ℂ (Fintype.card ι) F 0`. Simplify `iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c) hF` using `only [smul_eq_mul]`. Rewrite using `[e, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[ContinuousMultilinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dp_detD_const_mul (c : ℂ) {F : Matrix ι ι ℂ → ℂ} (hF : ContDiffAt ℂ (Fintype.card ι) F 0) :
    detD (fun T => c * F T) = c * detD F := by
  unfold detD
  have e : iteratedFDeriv ℂ (Fintype.card ι) (fun T => c * F T) 0 =
      c • iteratedFDeriv ℂ (Fintype.card ι) F 0 := by
    simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c) hF
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hent : ∀ a b : ι, ContDiff ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S) a b)`. Introduce `a b`. Establish `e : (fun S : Matrix ι ι ℂ => (1 + M * S) a b) = fun S => (1 : Matrix ι ι ℂ) a b + ∑ c, M a c * S c b`. Use function extensionality and compare the values at `S`. Simplify using `[Matrix.add_apply, Matrix.mul_apply]`.

Rewrite using `[e]`. Conclude with `contDiff_const.add (ContDiff.sum fun c _ => contDiff_const.mul (contDiff_apply_apply ℂ ℂ c b))`. Simplify using `only [Matrix.det_apply]`. Conclude with `ContDiff.sum fun σ _ => (contDiff_prod fun i _ => hent _ _).const_smul _`.
-/
theorem contDiff_det_one_add (M : Matrix ι ι ℂ) {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S).det) := by
  have hent : ∀ a b : ι, ContDiff ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S) a b) := by
    intro a b
    have e : (fun S : Matrix ι ι ℂ => (1 + M * S) a b) =
        fun S => (1 : Matrix ι ι ℂ) a b + ∑ c, M a c * S c b := by
      funext S; simp [Matrix.add_apply, Matrix.mul_apply]
    rw [e]
    exact contDiff_const.add (ContDiff.sum fun c _ => contDiff_const.mul (contDiff_apply_apply ℂ ℂ c b))
  simp only [Matrix.det_apply]
  exact ContDiff.sum fun σ _ => (contDiff_prod fun i _ => hent _ _).const_smul _

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg t`. Simplify using `only [zpow_natCast]`. Conclude with `((contDiff_det_one_add M).pow m).contDiffAt`. Simplify using `only [_root_.zpow_neg, zpow_natCast]`. Use `(((contDiff_det_one_add M).pow m).contDiffAt).inv ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem contDiffAt_det_zpow (M : Matrix ι ι ℂ) (t : ℤ) {k : WithTop ℕ∞} :
    ContDiffAt ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S).det ^ t) 0 := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg t
  · simp only [zpow_natCast]
    exact ((contDiff_det_one_add M).pow m).contDiffAt
  · simp only [_root_.zpow_neg, zpow_natCast]
    refine (((contDiff_det_one_add M).pow m).contDiffAt).inv ?_
    simp

end detD

section blocks

variable {n : ℕ}

def dp_incl (s : Finset (Fin n)) : Matrix (Fin n) s ℂ := fun a c => if a = (c : Fin n) then 1 else 0

def proj (s : Finset (Fin n)) : Matrix s (Fin n) ℂ := fun c b => if (c : Fin n) = b then 1 else 0

/- English proof (translation)
Simplify using `only [dp_incl, Matrix.mul_apply, ite_mul, one_mul, zero_mul]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨a, h⟩]`. Simplify using the standard rewrite rules. Introduce `c _ hc`.

Rewrite using `[if_neg]`. Introduce `hac`. Conclude with `hc (Subtype.ext hac.symm)`. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `h c.2`.
-/
theorem incl_mul_apply {m : Type} [Fintype m] (s : Finset (Fin n)) (X : Matrix s m ℂ) (a : Fin n) (d : m) :
    (dp_incl s * X) a d = if h : a ∈ s then X ⟨a, h⟩ d else 0 := by
  simp only [dp_incl, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro hac
      exact hc (Subtype.ext hac.symm)
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    rintro rfl
    exact h c.2

/- English proof (translation)
Simplify using `only [proj, Matrix.mul_apply, mul_ite, mul_one, mul_zero]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨b, h⟩]`. Simplify using the standard rewrite rules. Introduce `c _ hc`.

Rewrite using `[if_neg]`. Introduce `hcb`. Conclude with `hc (Subtype.ext hcb)`. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `h c.2`.
-/
theorem mul_proj_apply {m : Type} [Fintype m] (s : Finset (Fin n)) (X : Matrix m s ℂ) (d : m) (b : Fin n) :
    (X * proj s) d b = if h : b ∈ s then X d ⟨b, h⟩ else 0 := by
  simp only [proj, Matrix.mul_apply, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨b, h⟩]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro hcb
      exact hc (Subtype.ext hcb)
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    rintro rfl
    exact h c.2

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[incl_mul_apply]`. Distinguish the cases in `ha : a ∈ s`. Rewrite using `[dif_pos ha, mul_proj_apply]`. Distinguish the cases in `hb : b ∈ s`.

Rewrite using `[dif_pos hb, embOn, dif_pos ⟨ha, hb⟩]`. Rewrite using `[dif_neg hb, embOn, dif_neg (fun h => hb h.2)]`. Rewrite using `[dif_neg ha, embOn, dif_neg (fun h => ha h.1)]`.
-/
theorem dp_embOn_eq (s : Finset (Fin n)) (T : Matrix s s ℂ) : embOn s T = dp_incl s * (T * proj s) := by
  ext a b
  rw [incl_mul_apply]
  by_cases ha : a ∈ s
  · rw [dif_pos ha, mul_proj_apply]
    by_cases hb : b ∈ s
    · rw [dif_pos hb, embOn, dif_pos ⟨ha, hb⟩]
    · rw [dif_neg hb, embOn, dif_neg (fun h => hb h.2)]
  · rw [dif_neg ha, embOn, dif_neg (fun h => ha h.1)]

/- English proof (translation)
Use extensionality with `c d`. Simplify using `only [proj, dp_incl, Matrix.mul_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.submatrix_apply]`.
-/
theorem proj_mul_mul_incl (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) :
    proj s * M * dp_incl s = M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n)) := by
  ext c d
  simp only [proj, dp_incl, Matrix.mul_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.submatrix_apply]

/- English proof (translation)
Rewrite using `[dp_embOn_eq, ← Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc (proj s), proj_mul_mul_incl, Matrix.det_one_add_mul_comm]`.
-/
theorem dp_det_one_add_mul_embOn (M : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det =
      (1 + M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n)) * T).det := by
  rw [dp_embOn_eq, ← Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc (proj s),
    proj_mul_mul_incl, Matrix.det_one_add_mul_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use extensionality with `a c`. Simplify using `only [Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Simplify using `only [embOn]`.

Use `split_ifs with h1 h2`. Conclude with `absurd h2.1 (by simpa [blkB] using h1.2)`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Use extensionality with `a c`. Simplify using `only [Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Simplify using `only [embOn]`. Use `split_ifs with h1 h2`.

Conclude with `absurd h1.2 (by simpa [blkB] using h2.1)`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem embOn_mul_embOn_compl (j : ℕ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) :
    embOn (blkB j) S * embOn (blkA j) T = 0 ∧ embOn (blkA j) T * embOn (blkB j) S = 0 := by
  constructor
  · ext a c
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [embOn]
    split_ifs with h1 h2
    · exact absurd h2.1 (by simpa [blkB] using h1.2)
    · simp
    · simp
    · simp
  · ext a c
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [embOn]
    split_ifs with h1 h2
    · exact absurd h1.2 (by simpa [blkB] using h2.1)
    · simp
    · simp
    · simp

end blocks

section group

variable {n : ℕ}

/- English proof (translation)
Simplify using `[JJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]`.
-/
theorem JJ_mul_self : JJ n * JJ n = -1 := by
  simp [JJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]

/- English proof (translation)
Establish `h : xᴴ * JJ n * x = JJ n` using `hx`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.neg_mul, Matrix.mul_assoc]`. Use `_ = 1 := by rw [h, JJ_mul_self, neg_neg]`.
-/
theorem inv_of_InG {x : M2 n} (hx : InG x) : -(JJ n * xᴴ * JJ n) * x = 1 := by
  have h : xᴴ * JJ n * x = JJ n := hx
  calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by
        simp only [Matrix.neg_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h, JJ_mul_self, neg_neg]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (inv_of_InG hx)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `isUnit_iff_ne_zero.2 (fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h)`.
-/
theorem isUnit_det_of_InG {x : M2 n} (hx : InG x) : IsUnit x.det := by
  have h := congrArg Matrix.det (inv_of_InG hx)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_ne_zero.2 (fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h)

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (inv_of_InG hx)`.
-/
theorem inv_eq_of_InG {x : M2 n} (hx : InG x) : x⁻¹ = -(JJ n * xᴴ * JJ n) :=
  Matrix.inv_eq_left_inv (inv_of_InG hx)

/- English proof (translation)
Establish `h1 : x * -(JJ n * xᴴ * JJ n) = 1`. Rewrite using `[← inv_eq_of_InG hx]`. Conclude with `Matrix.mul_nonsing_inv x (isUnit_det_of_InG hx)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[JJ_mul_self]`.

Simplify using the standard rewrite rules. Use `_ = (x * -(JJ n * xᴴ * JJ n)) * JJ n := by`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_one]`. Use `_ = JJ n := by rw [h1, Matrix.one_mul]`.
-/
theorem mul_J_mul_of_InG {x : M2 n} (hx : InG x) : x * JJ n * xᴴ = JJ n := by
  have h1 : x * -(JJ n * xᴴ * JJ n) = 1 := by
    rw [← inv_eq_of_InG hx]; exact Matrix.mul_nonsing_inv x (isUnit_det_of_InG hx)
  calc x * JJ n * xᴴ = x * JJ n * xᴴ * (JJ n * JJ n) * (-1) := by
        rw [JJ_mul_self]; simp
    _ = (x * -(JJ n * xᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_one]
    _ = JJ n := by rw [h1, Matrix.one_mul]

/- English proof (translation)
Establish `h` using `mul_J_mul_of_InG hx`. Rewrite `h` using `[← Matrix.fromBlocks_toBlocks x]`. Simplify using `only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.fromBlocks_inj] at h`. Take `⟨-, -, h21, h22⟩` from `h`. Prove the components needed by the constructor for the conclusion.

Use `h22` as an intermediate fact. Rewrite `this` using `[Matrix.neg_mul, neg_add_eq_zero]`. Conclude with `this.symm`. Rewrite `h21` using `[Matrix.neg_mul, neg_add_eq_iff_eq_add]`. Rewrite using `[sub_eq_iff_eq_add, ← sub_eq_iff_eq_add']`.

Rewrite using `[h21]`. Normalize the expressions using the abelian group laws.
-/
theorem blocks_of_InG {x : M2 n} (hx : InG x) :
    x.toBlocks₂₁ * (x.toBlocks₂₂)ᴴ = x.toBlocks₂₂ * (x.toBlocks₂₁)ᴴ ∧
      x.toBlocks₂₂ * (x.toBlocks₁₁)ᴴ - x.toBlocks₂₁ * (x.toBlocks₁₂)ᴴ = 1 := by
  have h := mul_J_mul_of_InG hx
  rw [← Matrix.fromBlocks_toBlocks x] at h
  simp only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one,
    Matrix.mul_neg, zero_add, add_zero, Matrix.fromBlocks_inj] at h
  obtain ⟨-, -, h21, h22⟩ := h
  constructor
  · have := h22
    rw [Matrix.neg_mul, neg_add_eq_zero] at this
    exact this.symm
  · rw [Matrix.neg_mul, neg_add_eq_iff_eq_add] at h21
    rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add']
    rw [h21]; abel

/- English proof (translation)
Rewrite using `[inv_eq_of_InG hx]`. Use `conv_lhs => rw [← Matrix.fromBlocks_toBlocks x]`. Simplify using `[JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]`.
-/
theorem inv_blocks_of_InG {x : M2 n} (hx : InG x) :
    x⁻¹ = Matrix.fromBlocks (x.toBlocks₂₂)ᴴ (-(x.toBlocks₁₂)ᴴ) (-(x.toBlocks₂₁)ᴴ) (x.toBlocks₁₁)ᴴ := by
  rw [inv_eq_of_InG hx]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks x]
  simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

/- English proof (translation)
Establish `h` using `(blocks_of_InG hx).1`. Simplify using `only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_I]`. Rewrite using `[h]`. Use `module`.
-/
theorem u_mul_u_conj {x : M2 n} (hx : InG x) : u1 x * (u1 x)ᴴ = u2 x * (u2 x)ᴴ := by
  have h := (blocks_of_InG hx).1
  simp only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
    Complex.star_def, Complex.conj_I]
  rw [h]
  module

/- English proof (translation)
Establish `huu` using `u_mul_u_conj hx`. Take `⟨-, h1⟩` from `blocks_of_InG hx`. Establish `h1' : x.toBlocks₁₁ * (x.toBlocks₂₂)ᴴ - x.toBlocks₁₂ * (x.toBlocks₂₁)ᴴ = 1`. Use `congrArg Matrix.conjTranspose h1` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]`.

Establish `key : ∀ v : Fin n → ℂ, (u1 x)ᴴ *ᵥ v = 0 → (u2 x)ᴴ *ᵥ v = 0 → v = 0`. Introduce `v e1 e2`. Establish `hC : (x.toBlocks₂₁)ᴴ *ᵥ v = 0`. Establish `: (u2 x)ᴴ *ᵥ v - (u1 x)ᴴ *ᵥ v = (2 * Complex.I) • ((x.toBlocks₂₁)ᴴ *ᵥ v)`. Simplify using `only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, Complex.star_def, Complex.conj_I]`.

Use `module`. Rewrite `this` using `[e1, e2, sub_zero]`. Conclude with `(smul_eq_zero.1 this.symm).resolve_left (by simp)`. Establish `hD : (x.toBlocks₂₂)ᴴ *ᵥ v = 0`. Establish `: (u2 x)ᴴ *ᵥ v + (u1 x)ᴴ *ᵥ v = (2 : ℂ) • ((x.toBlocks₂₂)ᴴ *ᵥ v)`.

Simplify using `only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, Complex.star_def, Complex.conj_I]`. Use `module`. Rewrite `this` using `[e1, e2, add_zero]`. Conclude with `(smul_eq_zero.1 this.symm).resolve_left (by norm_num)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hC, hD, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]`. Establish `other : ∀ (U V : Matrix (Fin n) (Fin n) ℂ), U * Uᴴ = V * Vᴴ → ∀ v : Fin n → ℂ, Uᴴ *ᵥ v = 0 → Vᴴ *ᵥ v = 0`. Introduce `U V hUV v hv`. Establish `: star (Vᴴ *ᵥ v) ⬝ᵥ (Vᴴ *ᵥ v) = 0`. Rewrite using `[Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← dotProduct_mulVec, Matrix.mulVec_mulVec, ← hUV, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, dotProduct_zero]`.

Conclude with `dotProduct_star_self_eq_zero.1 this`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `h0' : ((u1 x)ᴴ).det = 0` using `by rw [Matrix.det_conjTranspose, h0, star_zero]`. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0'`.

Conclude with `hv (key v hv0 (other _ _ huu v hv0))`. Introduce `h0`. Establish `h0' : ((u2 x)ᴴ).det = 0` using `by rw [Matrix.det_conjTranspose, h0, star_zero]`. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0'`. Conclude with `hv (key v (other _ _ huu.symm v hv0) hv0)`.
-/
theorem det_u_ne {x : M2 n} (hx : InG x) : (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0 := by
  have huu := u_mul_u_conj hx
  obtain ⟨-, h1⟩ := blocks_of_InG hx
  have h1' : x.toBlocks₁₁ * (x.toBlocks₂₂)ᴴ - x.toBlocks₁₂ * (x.toBlocks₂₁)ᴴ = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul] using this

  have key : ∀ v : Fin n → ℂ, (u1 x)ᴴ *ᵥ v = 0 → (u2 x)ᴴ *ᵥ v = 0 → v = 0 := by
    intro v e1 e2
    have hC : (x.toBlocks₂₁)ᴴ *ᵥ v = 0 := by
      have : (u2 x)ᴴ *ᵥ v - (u1 x)ᴴ *ᵥ v = (2 * Complex.I) • ((x.toBlocks₂₁)ᴴ *ᵥ v) := by
        simp only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
          Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, Complex.star_def, Complex.conj_I]
        module
      rw [e1, e2, sub_zero] at this
      exact (smul_eq_zero.1 this.symm).resolve_left (by simp)
    have hD : (x.toBlocks₂₂)ᴴ *ᵥ v = 0 := by
      have : (u2 x)ᴴ *ᵥ v + (u1 x)ᴴ *ᵥ v = (2 : ℂ) • ((x.toBlocks₂₂)ᴴ *ᵥ v) := by
        simp only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
          Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, Complex.star_def, Complex.conj_I]
        module
      rw [e1, e2, add_zero] at this
      exact (smul_eq_zero.1 this.symm).resolve_left (by norm_num)
    calc v = (x.toBlocks₁₁ * (x.toBlocks₂₂)ᴴ - x.toBlocks₁₂ * (x.toBlocks₂₁)ᴴ) *ᵥ v := by rw [h1', Matrix.one_mulVec]
      _ = 0 := by
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hC, hD, Matrix.mulVec_zero,
          Matrix.mulVec_zero, sub_zero]

  have other : ∀ (U V : Matrix (Fin n) (Fin n) ℂ), U * Uᴴ = V * Vᴴ → ∀ v : Fin n → ℂ, Uᴴ *ᵥ v = 0 → Vᴴ *ᵥ v = 0 := by
    intro U V hUV v hv
    have : star (Vᴴ *ᵥ v) ⬝ᵥ (Vᴴ *ᵥ v) = 0 := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← dotProduct_mulVec, Matrix.mulVec_mulVec,
        ← hUV, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, dotProduct_zero]
    exact dotProduct_star_self_eq_zero.1 this
  constructor
  · intro h0
    have h0' : ((u1 x)ᴴ).det = 0 := by rw [Matrix.det_conjTranspose, h0, star_zero]
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    exact hv (key v hv0 (other _ _ huu v hv0))
  · intro h0
    have h0' : ((u2 x)ᴴ).det = 0 := by rw [Matrix.det_conjTranspose, h0, star_zero]
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    exact hv (key v (other _ _ huu.symm v hv0) hv0)

end group

section cm

variable {n : ℕ}

def CmI (n : ℕ) : M2 n := (-(Complex.I / 2)) • Matrix.fromBlocks 1 (Complex.I • 1) (-1) (Complex.I • 1)

/- English proof (translation)
Establish `hI : (-(Complex.I / 2)) * (2 * Complex.I) = 1`. Take the linear combination `(-1 : ℂ) * Complex.I_mul_I`. Rewrite using `[CmI, Cm, Matrix.smul_mul, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]`. Use `congr 1`. Rewrite using `[show (1 : Matrix (Fin n) (Fin n) ℂ) * (Complex.I • 1) + (Complex.I • 1) * 1 = (2 * Complex.I) • 1 by`.

Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Use the proof step `module, smul_smul, hI, one_smul]`. Rewrite using `[show (1 : Matrix (Fin n) (Fin n) ℂ) * -(Complex.I • 1) + (Complex.I • 1) * 1 = 0 by`. Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Use the proof step `module, smul_zero]`.

Rewrite using `[show (-1 : Matrix (Fin n) (Fin n) ℂ) * (Complex.I • 1) + (Complex.I • 1) * 1 = 0 by`. Simplify using `only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one]`. Use the proof step `module, smul_zero]`. Rewrite using `[show (-1 : Matrix (Fin n) (Fin n) ℂ) * -(Complex.I • 1) + (Complex.I • 1) * 1 = (2 * Complex.I) • 1 by`. Simplify using `only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul, Matrix.mul_one]`.

Use the proof step `module, smul_smul, hI,`. Use the proof step `one_smul]`.
-/
theorem CmI_mul_Cm : CmI n * Cm n = 1 := by
  have hI : (-(Complex.I / 2)) * (2 * Complex.I) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_mul_I
  rw [CmI, Cm, Matrix.smul_mul, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  congr 1
  · rw [show (1 : Matrix (Fin n) (Fin n) ℂ) * (Complex.I • 1) + (Complex.I • 1) * 1 = (2 * Complex.I) • 1 by
      simp only [Matrix.one_mul, Matrix.mul_one]; module, smul_smul, hI, one_smul]
  · rw [show (1 : Matrix (Fin n) (Fin n) ℂ) * -(Complex.I • 1) + (Complex.I • 1) * 1 = 0 by
      simp only [Matrix.one_mul, Matrix.mul_one]; module, smul_zero]
  · rw [show (-1 : Matrix (Fin n) (Fin n) ℂ) * (Complex.I • 1) + (Complex.I • 1) * 1 = 0 by
      simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one]; module, smul_zero]
  · rw [show (-1 : Matrix (Fin n) (Fin n) ℂ) * -(Complex.I • 1) + (Complex.I • 1) * 1 = (2 * Complex.I) • 1 by
      simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul, Matrix.mul_one]; module, smul_smul, hI,
      one_smul]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (CmI_mul_Cm (n := n))`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `isUnit_iff_ne_zero.2 (fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h)`.
-/
theorem isUnit_det_Cm : IsUnit (Cm n).det := by
  have h := congrArg Matrix.det (CmI_mul_Cm (n := n))
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_ne_zero.2 (fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h)

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv CmI_mul_Cm`.
-/
theorem dp_Cm_inv : (Cm n)⁻¹ = CmI n := Matrix.inv_eq_left_inv CmI_mul_Cm

/- English proof (translation)
Rewrite using `[← dp_Cm_inv]`. Conclude with `Matrix.mul_nonsing_inv _ isUnit_det_Cm`.
-/
theorem Cm_mul_CmI : Cm n * CmI n = 1 := by
  rw [← dp_Cm_inv]; exact Matrix.mul_nonsing_inv _ isUnit_det_Cm

/- English proof (translation)
Rewrite using `[mX, Matrix.fromBlocks_one, Matrix.mul_one, dp_Cm_inv, Cm_mul_CmI]`.
-/
theorem mX_one : mX (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 1 = 1 := by
  rw [mX, Matrix.fromBlocks_one, Matrix.mul_one, dp_Cm_inv, Cm_mul_CmI]

def Lr (n : ℕ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := Matrix.fromCols 1 (Complex.I • 1)

def Rc (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := Matrix.fromRows 1 0

/- English proof (translation)
Use `conv_rhs => rw [← Matrix.fromBlocks_toBlocks Z]`. Rewrite using `[Lr, Rc, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]`. Simplify using the standard rewrite rules.
-/
theorem ub_eq (Z : M2 n) :
    Z.toBlocks₁₁ + Complex.I • Z.toBlocks₂₁ = (Lr n * Z : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * Rc n := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks Z]
  rw [Lr, Rc, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp

/- English proof (translation)
Establish `hI : (-(Complex.I / 2)) * (2 * Complex.I) = 1`. Take the linear combination `(-1 : ℂ) * Complex.I_mul_I`. Establish `hI2 : (-(Complex.I / 2)) * (2 * Complex.I * Complex.I) = Complex.I`. Take the linear combination `(-Complex.I) * Complex.I_mul_I`. Establish `e1 : (Lr n * Cm n : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) = (Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) (0 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ)`.

Rewrite using `[Lr, Cm, Matrix.fromCols_mul_fromBlocks]`. Use `congr 1`. Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Use `module`. Simplify using `only [Matrix.one_mul, Matrix.mul_one]`.

Use `module`. Establish `e2 : ((Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) (0 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) Q R 1 : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) = (Matrix.fromCols ((2 * Complex.I) • (1 : Mat …`. Rewrite using `[Matrix.fromCols_mul_fromBlocks]`. Simplify using the standard rewrite rules. Establish `e3 : ((Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ((2 * Complex.I) • Q) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * CmI n : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) = Matrix.fromCols (1 - Q) (Complex.I • (1 + Q))`.

Rewrite using `[CmI, Matrix.mul_smul, Matrix.fromCols_mul_fromBlocks]`. Use extensionality with `a b`. Break down `b with b | b` into its components or cases. Simplify using `only [Matrix.smul_apply, Matrix.fromCols_apply_inl, Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_apply, Matrix.sub_apply, smul_eq_mul]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `only [Matrix.one_apply_eq]`. Take the linear combination `(1 - Q a a) * hI`. Simplify using `only [Matrix.one_apply_ne hab]`. Take the linear combination `(- Q a b) * hI`.

Simplify using `only [Matrix.smul_apply, Matrix.fromCols_apply_inr, Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_eq_mul]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `only [Matrix.one_apply_eq]`. Take the linear combination `(1 + Q a a) * hI2`.

Simplify using `only [Matrix.one_apply_ne hab]`. Take the linear combination `(Q a b) * hI2`. Rewrite using `[mX, dp_Cm_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, e2, e3]`.
-/
theorem Lr_mX (Q R : Matrix (Fin n) (Fin n) ℂ) :
    (Lr n * mX 1 Q R 1 : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) = Matrix.fromCols (1 - Q) (Complex.I • (1 + Q)) := by
  have hI : (-(Complex.I / 2)) * (2 * Complex.I) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_mul_I
  have hI2 : (-(Complex.I / 2)) * (2 * Complex.I * Complex.I) = Complex.I := by
    linear_combination (-Complex.I) * Complex.I_mul_I
  have e1 : (Lr n * Cm n : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) =
      (Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) (0 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) := by
    rw [Lr, Cm, Matrix.fromCols_mul_fromBlocks]
    congr 1
    · simp only [Matrix.one_mul, Matrix.mul_one]; module
    · simp only [Matrix.one_mul, Matrix.mul_one]; module
  have e2 : ((Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) (0 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) Q R 1 :
        Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) =
      (Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ((2 * Complex.I) • Q) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) := by
    rw [Matrix.fromCols_mul_fromBlocks]
    simp
  have e3 : ((Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ((2 * Complex.I) • Q) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * CmI n :
        Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) = Matrix.fromCols (1 - Q) (Complex.I • (1 + Q)) := by
    rw [CmI, Matrix.mul_smul, Matrix.fromCols_mul_fromBlocks]
    ext a b
    rcases b with b | b
    · simp only [Matrix.smul_apply, Matrix.fromCols_apply_inl, Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_apply, Matrix.sub_apply, smul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq]
        linear_combination (1 - Q a a) * hI
      · simp only [Matrix.one_apply_ne hab]
        linear_combination (- Q a b) * hI
    · simp only [Matrix.smul_apply, Matrix.fromCols_apply_inr, Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq]
        linear_combination (1 + Q a a) * hI2
      · simp only [Matrix.one_apply_ne hab]
        linear_combination (Q a b) * hI2
  rw [mX, dp_Cm_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, e2, e3]

/- English proof (translation)
Establish `hinv : (x * mX 1 Q R 1)⁻¹ = mX 1 (-Q) (-R) 1 * x⁻¹`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Establish `hx1 : x⁻¹ * x = 1` using `Matrix.nonsing_inv_mul x (isUnit_det_of_InG hx)`. Establish `hfb : Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-Q) (-R) 1 * Matrix.fromBlocks 1 Q R 1 = 1`. Rewrite using `[Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`.

Simplify using `[hQR, hRQ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[hx1, Matrix.mul_one, mX, mX, dp_Cm_inv]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [CmI_mul_Cm, Matrix.mul_one, hfb, Matrix.mul_one, Cm_mul_CmI]`. Rewrite using `[ub1, hinv, ub_eq, ← Matrix.mul_assoc (Lr n), Lr_mX, Matrix.mul_assoc, inv_blocks_of_InG hx, Rc, Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows]`. Simplify using `only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.mul_one, Matrix.mul_zero, add_zero, sub_neg_eq_add, neg_neg, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Mat …`.

Use `module`.
-/
theorem inverse_first_block_unipotent_formula {x : M2 n} (hx : InG x) (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    ub1 (x * mX 1 Q R 1) = (u1 x)ᴴ + Q * (u2 x)ᴴ := by
  have hinv : (x * mX 1 Q R 1)⁻¹ = mX 1 (-Q) (-R) 1 * x⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    have hx1 : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul x (isUnit_det_of_InG hx)
    have hfb : Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-Q) (-R) 1 * Matrix.fromBlocks 1 Q R 1 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [hQR, hRQ]
    calc mX 1 (-Q) (-R) 1 * x⁻¹ * (x * mX 1 Q R 1) = mX 1 (-Q) (-R) 1 * (x⁻¹ * x) * mX 1 Q R 1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hx1, Matrix.mul_one, mX, mX, dp_Cm_inv]
          calc Cm n * Matrix.fromBlocks 1 (-Q) (-R) 1 * CmI n * (Cm n * Matrix.fromBlocks 1 Q R 1 * CmI n)
              = Cm n * (Matrix.fromBlocks 1 (-Q) (-R) 1 * (CmI n * Cm n) * Matrix.fromBlocks 1 Q R 1) * CmI n := by
                simp only [Matrix.mul_assoc]
            _ = 1 := by rw [CmI_mul_Cm, Matrix.mul_one, hfb, Matrix.mul_one, Cm_mul_CmI]
  rw [ub1, hinv, ub_eq, ← Matrix.mul_assoc (Lr n), Lr_mX, Matrix.mul_assoc, inv_blocks_of_InG hx, Rc,
    Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows]
  simp only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_I, Matrix.mul_one, Matrix.mul_zero, add_zero, sub_neg_eq_add, neg_neg,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, neg_smul, smul_neg]
  module

end cm

section main

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[Fintype.card_coe]`. Establish `: blkA (n` using `n) j = Finset.image (Fin.castLE hj) Finset.univ := by`. Use extensionality with `i`. Simplify using `only [blkA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨⟨i, h⟩, Fin.ext rfl⟩`. Introduce and unpack `⟨a, -, rfl⟩`. Conclude with `a.isLt`. Rewrite using `[this, Finset.card_image_of_injective _ (Fin.castLE_injective hj), Finset.card_univ, Fintype.card_fin]`.
-/
theorem dp_card_blkA {j : ℕ} (hj : j ≤ n) : Fintype.card (blkA (n := n) j) = j := by
  rw [Fintype.card_coe]
  have : blkA (n := n) j = Finset.image (Fin.castLE hj) Finset.univ := by
    ext i
    simp only [blkA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨⟨i, h⟩, Fin.ext rfl⟩
    · rintro ⟨a, -, rfl⟩; exact a.isLt
  rw [this, Finset.card_image_of_injective _ (Fin.castLE_injective hj), Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Rewrite using `[Fintype.card_coe, blkB, Finset.card_compl, Fintype.card_fin, ← Fintype.card_coe, dp_card_blkA hj]`.
-/
theorem dp_card_blkB {j : ℕ} (hj : j ≤ n) : Fintype.card (blkB (n := n) j) = n - j := by
  rw [Fintype.card_coe, blkB, Finset.card_compl, Fintype.card_fin, ← Fintype.card_coe, dp_card_blkA hj]

/- English proof (translation)
Introduce `n j p q x hj hx`. Take `⟨h1, h2⟩` from `det_u_ne hx`. Establish `hu1 : IsUnit (u1 x).det` using `isUnit_iff_ne_zero.2 h1`. Establish `hu2 : IsUnit (u2 x).det` using `isUnit_iff_ne_zero.2 h2`. Establish `hwinv : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x`.

Rewrite using `[wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu2]`. Establish `hu1w : u1 x * (wM x)⁻¹ = u2 x`. Rewrite using `[hwinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul]`. Establish `hu2w : u2 x * wM x = u1 x`. Rewrite using `[wM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu2, Matrix.one_mul]`.

Establish `hwc : wM x * (u1 x)ᴴ = (u2 x)ᴴ`. Rewrite using `[wM, Matrix.mul_assoc, u_mul_u_conj hx, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu2, Matrix.one_mul]`. Establish `hub : ub1 x = (u1 x)ᴴ`. Use `inverse_first_block_unipotent_formula hx 0 0 (by simp) (by simp)` as an intermediate fact. Rewrite `this` using `[mX_one, Matrix.mul_one, Matrix.zero_mul, add_zero]`.

Conclude with `this`. Establish `key : ∀ (T : Matrix (blkA (n` using `n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ), (1 + wM x * embOn (blkB j) S).det ≠ 0 → fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) = fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n) * (1 + wM x * embOn (blkB j) S).det ^ (q - n) := by`. Introduce `T S hb`. Take `⟨hSQ, hTQ⟩` from `embOn_mul_embOn_compl j S T`. Establish `e1 : u1 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) = u1 x * (1 + (wM x)⁻¹ * embOn (blkA j) T)`.

Rewrite using `[(hU n x _ _ _ _).1, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hu1w]`. Establish `e2 : u2 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) = u2 x * (1 + wM x * embOn (blkB j) S)`. Rewrite using `[(hU n x _ _ _ _).2, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hu2w, add_comm]`. Establish `e3 : ub1 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) = (1 + embOn (blkB j) S * wM x) * ub1 x`. Rewrite using `[inverse_first_block_unipotent_formula hx _ _ hSQ hTQ, hub, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hwc]`.

Unfold `fV`. Rewrite using `[e1, e2, e3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_one_add_mul_comm (embOn (blkB j) S) (wM x), mul_zpow, mul_zpow, mul_zpow]`. Establish `hbb : (1 + wM x * embOn (blkB j) S).det ^ q * (1 + wM x * embOn (blkB j) S).det ^ (-(n : ℤ)) = (1 + wM x * embOn (blkB j) S).det ^ (q - n)`. Rewrite using `[← zpow_add₀ hb]`. Put the polynomial expressions in normal form.

Rewrite using `[← hbb]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB : ∀ T : Matrix (blkA (n` using `n) j) (blkA j) ℂ, detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ => fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) = fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n) * ((∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), (((q - n : ℤ) : ℂ) + i)) * minor …`. Introduce `T`. Establish `hev : (fun S : Matrix (blkB (n` using `n) j) (blkB j) ℂ => fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) =ᶠ[nhds 0] fun S => (fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n)) * (1 + (wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n)) * S).det ^ (q …`.

Establish `hc : ContinuousAt (fun S : Matrix (blkB (n` using `n) j) (blkB j) ℂ => (1 + (wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n)) * S).det) 0 := (contDiff_det_one_add _ (k := 0)).continuous.continuousAt`. Establish `h0 : (1 + (wM x).submatrix (fun i : blkB (n` using `n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n)) * (0 : Matrix (blkB (n := n) j) (blkB j) ℂ)).det ≠ 0 := by simp`. Use `filter_upwards [hc.eventually_ne h0] with S hS`. Rewrite `hS`, the goal using `[← dp_det_one_add_mul_embOn]`. Rewrite using `[key T S hS]`.

Establish `hCB` using `hC (blkB (n := n) j) ((wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n))) (q - n)`. Rewrite using `[detD_congr hev, dp_detD_const_mul _ (contDiffAt_det_zpow _ _), hCB]`. Both sides reduce to the same expression. Establish `hOuter : (fun T : Matrix (blkA (n` using `n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ => fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1))) = fun T => (fV p q x * ((∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), (((q - n : ℤ) : ℂ) + i)) * minorOn (blkB j) (wM x))) * (1 + ((wM x)⁻¹ …`. Use function extensionality and compare the values at `T`.

Rewrite using `[hB T, dp_det_one_add_mul_embOn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hCA` using `hC (blkA (n := n) j) (((wM x)⁻¹).submatrix (fun i : blkA (n := n) j => (i : Fin n)) (fun i : blkA (n := n) j => (i : Fin n))) (p - n)`. Rewrite using `[hOuter, dp_detD_const_mul _ (contDiffAt_det_zpow _ _), hCA, dp_card_blkA hj, dp_card_blkB hj]`. Simplify using `only [minorOn]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dpDual (hC : Cayley) (hU : UAct) : DpDual := by
  intro n j p q x hj hx
  obtain ⟨h1, h2⟩ := det_u_ne hx
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h1
  have hu2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 h2
  have hwinv : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x := by
    rw [wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu2]
  have hu1w : u1 x * (wM x)⁻¹ = u2 x := by
    rw [hwinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul]
  have hu2w : u2 x * wM x = u1 x := by
    rw [wM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu2, Matrix.one_mul]
  have hwc : wM x * (u1 x)ᴴ = (u2 x)ᴴ := by
    rw [wM, Matrix.mul_assoc, u_mul_u_conj hx, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu2, Matrix.one_mul]
  have hub : ub1 x = (u1 x)ᴴ := by
    have := inverse_first_block_unipotent_formula hx 0 0 (by simp) (by simp)
    rw [mX_one, Matrix.mul_one, Matrix.zero_mul, add_zero] at this
    exact this
  have key : ∀ (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (1 + wM x * embOn (blkB j) S).det ≠ 0 →
      fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) =
        fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n) *
          (1 + wM x * embOn (blkB j) S).det ^ (q - n) := by
    intro T S hb
    obtain ⟨hSQ, hTQ⟩ := embOn_mul_embOn_compl j S T
    have e1 : u1 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) =
        u1 x * (1 + (wM x)⁻¹ * embOn (blkA j) T) := by
      rw [(hU n x _ _ _ _).1, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hu1w]
    have e2 : u2 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) =
        u2 x * (1 + wM x * embOn (blkB j) S) := by
      rw [(hU n x _ _ _ _).2, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hu2w, add_comm]
    have e3 : ub1 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) =
        (1 + embOn (blkB j) S * wM x) * ub1 x := by
      rw [inverse_first_block_unipotent_formula hx _ _ hSQ hTQ, hub, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hwc]
    unfold fV
    rw [e1, e2, e3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_one_add_mul_comm (embOn (blkB j) S) (wM x), mul_zpow, mul_zpow, mul_zpow]
    have hbb : (1 + wM x * embOn (blkB j) S).det ^ q * (1 + wM x * embOn (blkB j) S).det ^ (-(n : ℤ)) =
        (1 + wM x * embOn (blkB j) S).det ^ (q - n) := by
      rw [← zpow_add₀ hb]; ring_nf
    rw [← hbb]
    ring
  have hB : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) =
        fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n) *
          ((∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), (((q - n : ℤ) : ℂ) + i)) *
            minorOn (blkB j) (wM x)) := by
    intro T
    have hev : (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) =ᶠ[nhds 0]
        fun S => (fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n)) *
          (1 + (wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n)) *
            S).det ^ (q - n) := by
      have hc : ContinuousAt (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          (1 + (wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n)) *
            S).det) 0 :=
        (contDiff_det_one_add _ (k := 0)).continuous.continuousAt
      have h0 : (1 + (wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n))
          (fun i : blkB (n := n) j => (i : Fin n)) * (0 : Matrix (blkB (n := n) j) (blkB j) ℂ)).det ≠ 0 := by simp
      filter_upwards [hc.eventually_ne h0] with S hS
      rw [← dp_det_one_add_mul_embOn] at hS ⊢
      rw [key T S hS]
    have hCB := hC (blkB (n := n) j)
      ((wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n))) (q - n)
    rw [detD_congr hev, dp_detD_const_mul _ (contDiffAt_det_zpow _ _), hCB]
    rfl
  have hOuter : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1))) =
      fun T => (fV p q x * ((∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), (((q - n : ℤ) : ℂ) + i)) *
            minorOn (blkB j) (wM x))) *
        (1 + ((wM x)⁻¹).submatrix (fun i : blkA (n := n) j => (i : Fin n)) (fun i : blkA (n := n) j => (i : Fin n)) *
          T).det ^ (p - n) := by
    funext T
    rw [hB T, dp_det_one_add_mul_embOn]
    ring
  have hCA := hC (blkA (n := n) j)
    (((wM x)⁻¹).submatrix (fun i : blkA (n := n) j => (i : Fin n)) (fun i : blkA (n := n) j => (i : Fin n))) (p - n)
  rw [hOuter, dp_detD_const_mul _ (contDiffAt_det_zpow _ _), hCA, dp_card_blkA hj, dp_card_blkB hj]
  simp only [minorOn]
  push_cast
  ring

end main

end PositivityTheory.Rg.Sw.LVs
