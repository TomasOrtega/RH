import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS.UComm

variable {A : Type} [Field A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Simplify using `only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hform_add_left (σ : A →+* A) (J : Matrix n n A) (x y z : n → A) :
    hform σ J (x + y) z = hform σ J x z + hform σ J y z := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hform_add_right (σ : A →+* A) (J : Matrix n n A) (x y z : n → A) :
    hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_left (σ : A →+* A) (J : Matrix n n A) (c : A) (x y : n → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_right (σ : A →+* A) (J : Matrix n n A) (c : A) (x y : n → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use `congrFun (congrFun hH i) j` as an intermediate fact. Simplify `this` using `[cT]`.
-/
theorem herm_apply (σ : A →+* A) {J : Matrix n n A} (hH : IsHerm σ J) (i j : n) :
    σ (J j i) = J i j := by
  have := congrFun (congrFun hH i) j
  simpa [cT] using this

/- English proof (translation)
Simplify using `only [hform, map_sum, map_mul, hσ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[herm_apply σ hH]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigma_hform (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (x y : n → A) : σ (hform σ J x y) = hform σ J y x := by
  simp only [hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [herm_apply σ hH]; ring

def rowv (σ : A →+* A) (J : Matrix n n A) (v : n → A) : n → A := (fun i => σ (v i)) ᵥ* J

/- English proof (translation)
Rewrite using `[hform_eq, rowv, dotProduct_mulVec]`.
-/
theorem rowv_dot (σ : A →+* A) (J : Matrix n n A) (v x : n → A) :
    rowv σ J v ⬝ᵥ x = hform σ J v x := by
  rw [hform_eq, rowv, dotProduct_mulVec]

def proj (σ : A →+* A) (J : Matrix n n A) (v : n → A) : Matrix n n A := vecMulVec v (rowv σ J v)

/- English proof (translation)
Rewrite using `[proj, vecMulVec_mul_vecMulVec, rowv_dot]`. Use extensionality with `i j`. Simplify using `[vecMulVec_apply, mul_left_comm]`.
-/
theorem proj_mul_proj (σ : A →+* A) (J : Matrix n n A) (v : n → A) :
    proj σ J v * proj σ J v = hform σ J v v • proj σ J v := by
  rw [proj, vecMulVec_mul_vecMulVec, rowv_dot]
  ext i j; simp [vecMulVec_apply, mul_left_comm]

/- English proof (translation)
Rewrite using `[proj, vecMulVec_mulVec, rowv_dot, op_smul_eq_smul]`.
-/
theorem proj_mulVec (σ : A →+* A) (J : Matrix n n A) (v x : n → A) :
    proj σ J v *ᵥ x = hform σ J v x • v := by
  rw [proj, vecMulVec_mulVec, rowv_dot, op_smul_eq_smul]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [cT, proj, rowv, transpose_apply, map_apply, vecMulVec_apply, vecMul, dotProduct, mulVec, map_mul, map_sum, hσ, herm_apply σ hH]`. Rewrite using `[mul_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cT_proj (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (v : n → A) : cT σ (proj σ J v) = vecMulVec (J *ᵥ v) (fun i => σ (v i)) := by
  ext i k
  simp only [cT, proj, rowv, transpose_apply, map_apply, vecMulVec_apply, vecMul, dotProduct,
    mulVec, map_mul, map_sum, hσ, herm_apply σ hH]
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Rewrite using `[cT_proj σ hσ hH, vecMulVec_mul, proj, mul_vecMulVec]`. Both sides reduce to the same expression.
-/
theorem cT_proj_mul (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (v : n → A) : cT σ (proj σ J v) * J = J * proj σ J v := by
  rw [cT_proj σ hσ hH, vecMulVec_mul, proj, mul_vecMulVec]; rfl

def refl (σ : A →+* A) (J : Matrix n n A) (v : n → A) : Matrix n n A :=
  1 + (-(2 / hform σ J v v)) • proj σ J v

/- English proof (translation)
Use `set q := hform σ J v v`. Establish `hP` using `proj_mul_proj σ J v`. Establish `hc : -(2 / q) + -(2 / q) + -(2 / q) * -(2 / q) * q = 0` using `by field_simp; ring`. Simplify using `only [refl, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hP, smul_smul]`. Rewrite using `[add_assoc, ← add_assoc ((-(2 / q)) • proj σ J v), ← add_smul, ← add_smul, hc, zero_smul, add_zero]`.
-/
theorem refl_mul_self (σ : A →+* A) (J : Matrix n n A) (v : n → A) (hv : hform σ J v v ≠ 0) :
    refl σ J v * refl σ J v = 1 := by
  set q := hform σ J v v
  have hP := proj_mul_proj σ J v
  have hc : -(2 / q) + -(2 / q) + -(2 / q) * -(2 / q) * q = 0 := by field_simp; ring
  simp only [refl, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hP, smul_smul]
  rw [add_assoc, ← add_assoc ((-(2 / q)) • proj σ J v), ← add_smul, ← add_smul, hc, zero_smul,
    add_zero]

/- English proof (translation)
Establish `hq : σ (hform σ J v v) = hform σ J v v` using `sigma_hform σ hσ hH v v`. Establish `hc : σ (-(2 / hform σ J v v)) = -(2 / hform σ J v v)`. Rewrite using `[map_neg, map_div₀, hq, map_ofNat]`. Establish `h1 : cT σ (refl σ J v) * J = J * refl σ J v`. Rewrite using `[refl, cT_add, cT_smul, Formalism.UG.cT_one, hc, add_mul, Matrix.one_mul, Matrix.smul_mul, cT_proj_mul σ hσ hH, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]`.

Rewrite using `[h1, Matrix.mul_assoc, refl_mul_self σ J v hv, Matrix.mul_one]`.
-/
theorem refl_unitary (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (v : n → A) (hv : hform σ J v v ≠ 0) :
    cT σ (refl σ J v) * J * refl σ J v = J := by
  have hq : σ (hform σ J v v) = hform σ J v v := sigma_hform σ hσ hH v v
  have hc : σ (-(2 / hform σ J v v)) = -(2 / hform σ J v v) := by
    rw [map_neg, map_div₀, hq, map_ofNat]
  have h1 : cT σ (refl σ J v) * J = J * refl σ J v := by
    rw [refl, cT_add, cT_smul, Formalism.UG.cT_one, hc, add_mul, Matrix.one_mul, Matrix.smul_mul,
      cT_proj_mul σ hσ hH, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  rw [h1, Matrix.mul_assoc, refl_mul_self σ J v hv, Matrix.mul_one]

/- English proof (translation)
Set `g : GL n A` to `⟨refl σ J v, refl σ J v, refl_mul_self σ J v hv, refl_mul_self σ J v hv⟩`. Establish `hg : g ∈ UJ σ J` using `refl_unitary σ hσ hH v hv`. Establish `h1 : refl σ J v * a = a * refl σ J v` using `hcomm g hg`. Establish `hc : -(2 / hform σ J v v) ≠ 0` using `neg_ne_zero.2 (div_ne_zero two_ne_zero hv)`. Establish `h2 : proj σ J v * a = a * proj σ J v`.

Simplify using `only [refl, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul] at h1`. Conclude with `smul_right_injective _ hc (add_left_cancel h1)`. Establish `h3` using `congrArg (· *ᵥ v) h2`. Simplify using `only [← mulVec_mulVec, proj_mulVec, mulVec_smul] at h3`. Use `⟨(hform σ J v v)⁻¹ * hform σ J v (a *ᵥ v), ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_smul, h3, smul_smul, inv_mul_cancel₀ hv, one_smul]`.
-/
theorem eigen [CharZero A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hH : IsHerm σ J)
    (a : Matrix n n A) (hcomm : ∀ g ∈ UJ σ J, (g : Matrix n n A) * a = a * (g : Matrix n n A))
    (v : n → A) (hv : hform σ J v v ≠ 0) : ∃ μ : A, a *ᵥ v = μ • v := by
  let g : GL n A := ⟨refl σ J v, refl σ J v, refl_mul_self σ J v hv, refl_mul_self σ J v hv⟩
  have hg : g ∈ UJ σ J := refl_unitary σ hσ hH v hv
  have h1 : refl σ J v * a = a * refl σ J v := hcomm g hg
  have hc : -(2 / hform σ J v v) ≠ 0 := neg_ne_zero.2 (div_ne_zero two_ne_zero hv)
  have h2 : proj σ J v * a = a * proj σ J v := by
    simp only [refl, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul] at h1
    exact smul_right_injective _ hc (add_left_cancel h1)
  have h3 := congrArg (· *ᵥ v) h2
  simp only [← mulVec_mulVec, proj_mulVec, mulVec_smul] at h3
  refine ⟨(hform σ J v v)⁻¹ * hform σ J v (a *ᵥ v), ?_⟩
  rw [mul_smul, h3, smul_smul, inv_mul_cancel₀ hv, one_smul]

/- English proof (translation)
Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Take `⟨i⟩` from `hn`. Use `set x : n → A := Pi.single i 1`. Use `set y : n → A := J⁻¹ *ᵥ Pi.single i 1`.

Establish `hsx : (fun k => σ (x k)) = x`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[x]`.

Simplify using `[x, hk]`. Establish `hxy : hform σ J x y = 1`. Rewrite using `[hform_eq, hsx, mulVec_mulVec, mul_nonsing_inv _ hJ, one_mulVec]`. Simplify using `[x]`. Establish `hyx : hform σ J y x = 1` using `by rw [← sigma_hform σ hσ hH, hxy, map_one]`.

Establish `h` using `hall (x + y)`. Rewrite `h` using `[hform_add_left, hform_add_right, hform_add_right, hall x, hall y, hxy, hyx]`. Evaluate the numerical expressions using `at h`.
-/
theorem exists_nonisotropic (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) [CharZero A] {J : Matrix n n A}
    (hH : IsHerm σ J) (hJ : IsUnit J.det) (hn : Nonempty n) : ∃ w, hform σ J w w ≠ 0 := by
  by_contra hall
  push_neg at hall
  obtain ⟨i⟩ := hn
  set x : n → A := Pi.single i 1
  set y : n → A := J⁻¹ *ᵥ Pi.single i 1
  have hsx : (fun k => σ (x k)) = x := by
    funext k; by_cases hk : k = i
    · subst hk; simp [x]
    · simp [x, hk]
  have hxy : hform σ J x y = 1 := by
    rw [hform_eq, hsx, mulVec_mulVec, mul_nonsing_inv _ hJ, one_mulVec]
    simp [x]
  have hyx : hform σ J y x = 1 := by rw [← sigma_hform σ hσ hH, hxy, map_one]
  have h := hall (x + y)
  rw [hform_add_left, hform_add_right, hform_add_right, hall x, hall y, hxy, hyx] at h
  norm_num at h

/- English proof (translation)
Rewrite `h2`, `h3` using `[mulVec_add, mulVec_smul, h1]`. Distinguish the cases in `hμ : μ = μ'`. Substitute `hμ` using the available equality. Establish `h4 : (c - c') • ((l - μ) • w) = 0` using `by linear_combination (norm := module) h2 - h3`. Break down `smul_eq_zero.1 h4 with h | h` into its components or cases.

Conclude with `absurd (sub_eq_zero.1 h) hc`. Break down `smul_eq_zero.1 h with h | h` into its components or cases. Establish `hl : l = μ` using `sub_eq_zero.1 h`. Substitute `hl` using the available equality. Take the linear combination `(norm := module) h2`.

Conclude with `absurd h hw`. Establish `h5 : (μ - μ') • v = (c • l - c' • l - μ * c + μ' * c') • w`. Take the linear combination `(norm := module) h3 - h2`. Establish `hv : v = ((μ - μ')⁻¹ * (c • l - c' • l - μ * c + μ' * c')) • w`. Rewrite using `[← smul_smul, ← h5, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hμ), one_smul]`.

Rewrite using `[hv, mulVec_smul, h1, smul_comm]`.
-/
theorem comb (M : Matrix n n A) (v w : n → A) (hw : w ≠ 0) (l μ μ' c c' : A) (hc : c ≠ c')
    (h1 : M *ᵥ w = l • w) (h2 : M *ᵥ (v + c • w) = μ • (v + c • w))
    (h3 : M *ᵥ (v + c' • w) = μ' • (v + c' • w)) : M *ᵥ v = l • v := by
  rw [mulVec_add, mulVec_smul, h1] at h2 h3
  by_cases hμ : μ = μ'
  · subst hμ
    have h4 : (c - c') • ((l - μ) • w) = 0 := by linear_combination (norm := module) h2 - h3
    rcases smul_eq_zero.1 h4 with h | h
    · exact absurd (sub_eq_zero.1 h) hc
    rcases smul_eq_zero.1 h with h | h
    · have hl : l = μ := sub_eq_zero.1 h
      subst hl
      linear_combination (norm := module) h2
    · exact absurd h hw
  · have h5 : (μ - μ') • v = (c • l - c' • l - μ * c + μ' * c') • w := by
      linear_combination (norm := module) h3 - h2
    have hv : v = ((μ - μ')⁻¹ * (c • l - c' • l - μ * c + μ' * c')) • w := by
      rw [← smul_smul, ← h5, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hμ), one_smul]
    rw [hv, mulVec_smul, h1, smul_comm]

/- English proof (translation)
Apply the tactic sequence `by_cases h0 : γ + 0 * β + 0 * 0 * α = 0 <;> by_cases h1 : γ + 1 * β + 1 * 1 * α = 0 <;>`. Apply the tactic sequence `by_cases h2 : γ + 2 * β + 2 * 2 * α = 0 <;> by_cases h3 : γ + 3 * β + 3 * 3 * α = 0`. Apply the tactic sequence `all_goals first`. Consider the case `exact absurd (show α = 0 by linear_combination (1/2 : A) * h0 - h1 + (1/2 : A) * h2) hα`. Consider the case `exact absurd (show α = 0 by linear_combination (1/2 : A) * h1 - h2 + (1/2 : A) * h3) hα`.

Consider the case `exact absurd (show α = 0 by linear_combination (1/3 : A) * h0 - (1/2 : A) * h1 + (1/6 : A) * h3) hα`. Consider the case `exact absurd (show α = 0 by linear_combination (1/6 : A) * h0 - (1/2 : A) * h2 + (1/3 : A) * h3) hα`. Consider the case `exact ⟨0, 1, by norm_num, by norm_num, by norm_num, h0, h1⟩`. Consider the case `exact ⟨0, 2, by norm_num, by norm_num, by norm_num, h0, h2⟩`. Consider the case `exact ⟨0, 3, by norm_num, by norm_num, by norm_num, h0, h3⟩`.

Consider the case `exact ⟨1, 2, by norm_num, by norm_num, by norm_num, h1, h2⟩`. Consider the case `exact ⟨1, 3, by norm_num, by norm_num, by norm_num, h1, h3⟩`. Consider the case `exact ⟨2, 3, by norm_num, by norm_num, by norm_num, h2, h3⟩`.
-/
theorem quad [CharZero A] (α β γ : A) (hα : α ≠ 0) : ∃ c c' : A, c ≠ c' ∧
    (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) ∧ (c' = 0 ∨ c' = 1 ∨ c' = 2 ∨ c' = 3) ∧
    γ + c * β + c * c * α ≠ 0 ∧ γ + c' * β + c' * c' * α ≠ 0 := by
  by_cases h0 : γ + 0 * β + 0 * 0 * α = 0 <;> by_cases h1 : γ + 1 * β + 1 * 1 * α = 0 <;>
    by_cases h2 : γ + 2 * β + 2 * 2 * α = 0 <;> by_cases h3 : γ + 3 * β + 3 * 3 * α = 0
  all_goals first
    | exact absurd (show α = 0 by linear_combination (1/2 : A) * h0 - h1 + (1/2 : A) * h2) hα
    | exact absurd (show α = 0 by linear_combination (1/2 : A) * h1 - h2 + (1/2 : A) * h3) hα
    | exact absurd (show α = 0 by linear_combination (1/3 : A) * h0 - (1/2 : A) * h1 + (1/6 : A) * h3) hα
    | exact absurd (show α = 0 by linear_combination (1/6 : A) * h0 - (1/2 : A) * h2 + (1/3 : A) * h3) hα
    | exact ⟨0, 1, by norm_num, by norm_num, by norm_num, h0, h1⟩
    | exact ⟨0, 2, by norm_num, by norm_num, by norm_num, h0, h2⟩
    | exact ⟨0, 3, by norm_num, by norm_num, by norm_num, h0, h3⟩
    | exact ⟨1, 2, by norm_num, by norm_num, by norm_num, h1, h2⟩
    | exact ⟨1, 3, by norm_num, by norm_num, by norm_num, h1, h3⟩
    | exact ⟨2, 3, by norm_num, by norm_num, by norm_num, h2, h3⟩

end GlobalTheory.RegSS.UComm

namespace GlobalTheory.RegSS

open UComm in
/- English proof (translation)
Introduce `A _ _ hA σ hσ n _ _ J hH hJ a hcomm`. Use `letI := hA.toField`. Break down `isEmpty_or_nonempty n with hn | hn` into its components or cases. Conclude with `⟨0, by ext i; exact isEmptyElim i⟩`. Take `⟨w, hw⟩` from `exists_nonisotropic σ hσ hH hJ hn`.

Take `⟨l, hl⟩` from `eigen σ hσ hH a hcomm w hw`. Establish `hw0 : w ≠ 0` using `by rintro rfl; simp [hform] at hw`. Establish `hall : ∀ v, a *ᵥ v = l • v`. Introduce `v`. Establish `hexp : ∀ c : A, σ c = c → hform σ J (v + c • w) (v + c • w) = hform σ J v v + c * (hform σ J v w + hform σ J w v) + c * c * hform σ J w w`.

Introduce `c hc`. Rewrite using `[hform_add_left, hform_add_right, hform_add_right, hform_smul_left, hform_smul_left, hform_smul_right, hform_smul_right, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfix : ∀ c : A, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) → σ c = c`. Apply the tactic sequence `rintro c (rfl | rfl | rfl | rfl) <;> simp [map_ofNat]`.

Take `⟨c, c', hcc, hc, hc', h1, h2⟩` from `quad (hform σ J w w) (hform σ J v w + hform σ J w v) (hform σ J v v) hw`. Rewrite `h1` using `[← hexp c (hfix c hc)]`. Rewrite `h2` using `[← hexp c' (hfix c' hc')]`. Take `⟨μ, hμ⟩` from `eigen σ hσ hH a hcomm _ h1`. Take `⟨μ', hμ'⟩` from `eigen σ hσ hH a hcomm _ h2`.

Conclude with `comb a v w hw0 l μ μ' c c' hcc hl hμ hμ'`. Use `⟨l, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `congrFun (hall (Pi.single j 1)) i` as an intermediate fact. Rewrite `this` using `[mulVec_single_one]`.

Simplify `this` using `[Matrix.one_apply, Pi.single_apply, eq_comm]`.
-/
theorem unitaryCommutant : UnitaryCommutant := by
  intro A _ _ hA σ hσ n _ _ J hH hJ a hcomm
  letI := hA.toField
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨0, by ext i; exact isEmptyElim i⟩
  obtain ⟨w, hw⟩ := exists_nonisotropic σ hσ hH hJ hn
  obtain ⟨l, hl⟩ := eigen σ hσ hH a hcomm w hw
  have hw0 : w ≠ 0 := by rintro rfl; simp [hform] at hw
  have hall : ∀ v, a *ᵥ v = l • v := by
    intro v
    have hexp : ∀ c : A, σ c = c → hform σ J (v + c • w) (v + c • w) =
        hform σ J v v + c * (hform σ J v w + hform σ J w v) + c * c * hform σ J w w := by
      intro c hc
      rw [hform_add_left, hform_add_right, hform_add_right, hform_smul_left, hform_smul_left,
        hform_smul_right, hform_smul_right, hc]
      ring
    have hfix : ∀ c : A, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) → σ c = c := by
      rintro c (rfl | rfl | rfl | rfl) <;> simp [map_ofNat]
    obtain ⟨c, c', hcc, hc, hc', h1, h2⟩ :=
      quad (hform σ J w w) (hform σ J v w + hform σ J w v) (hform σ J v v) hw
    rw [← hexp c (hfix c hc)] at h1
    rw [← hexp c' (hfix c' hc')] at h2
    obtain ⟨μ, hμ⟩ := eigen σ hσ hH a hcomm _ h1
    obtain ⟨μ', hμ'⟩ := eigen σ hσ hH a hcomm _ h2
    exact comb a v w hw0 l μ μ' c c' hcc hl hμ hμ'
  refine ⟨l, ?_⟩
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  rw [mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

end GlobalTheory.RegSS
