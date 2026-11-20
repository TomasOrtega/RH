import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevMulVecOutside

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.LineStabiliser

open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser

variable (k r' : ℕ)

def fst : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

def lst : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem e0_eq : e0 k r' = Pi.single (fst k r') 1 := rfl

/- English proof (translation)
Use extensionality with `i`. Establish `hi` using `i.isLt`. Rewrite using `[e0_eq, mulVec_single_one, Matrix.col_apply, Pi.single_apply]`. Simplify using `only [Hpk, fst, lst, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem gram_mulVec_e0 : Hpk k (1 + r') *ᵥ e0 k r' = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  rw [e0_eq, mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use extensionality with `i`. Establish `hi` using `i.isLt`. Establish `h : star (e0 k r') = Pi.single (fst k r') 1`. Rewrite using `[e0_eq, ← Pi.single_star, star_one]`. Rewrite using `[h, single_one_vecMul, Matrix.row_apply, Pi.single_apply]`.

Simplify using `only [Hpk, fst, lst, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem star_e0_vecMul_hpk_eq_single_lst : star (e0 k r') ᵥ* Hpk k (1 + r') = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  have h : star (e0 k r') = Pi.single (fst k r') 1 := by
    rw [e0_eq, ← Pi.single_star, star_one]
  rw [h, single_one_vecMul, Matrix.row_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Rewrite using `[dotProduct_mulVec, star_e0_vecMul_hpk_eq_single_lst, single_one_dotProduct]`.
-/
theorem pair_e0_left (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    star (e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ v) = v (lst k r') := by
  rw [dotProduct_mulVec, star_e0_vecMul_hpk_eq_single_lst, single_one_dotProduct]

/- English proof (translation)
Unfold `liftVec`. Rewrite using `[dif_neg]`. Simplify using `only [lst]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lift_lst (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (lst k r') = 0 := by
  unfold liftVec
  rw [dif_neg]
  simp only [lst]
  omega

/- English proof (translation)
Rewrite using `[e0_eq, Pi.single_apply, if_neg]`. Simplify using `only [lst, fst, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem e0_lst_eq_zero : e0 k r' (lst k r') = 0 := by
  rw [e0_eq, Pi.single_apply, if_neg]
  simp only [lst, fst, Fin.ext_iff]
  omega

/- English proof (translation)
Establish `hc : ∀ j, ((incl k 1 r')ᴴ *ᵥ u) j = u (levPos k 1 r' j)` using `fun j => inclH_mul k 1 r' (Matrix.of fun a _ => u a) j j`. Use extensionality with `i`. Establish `hi` using `i.isLt`. Rewrite using `[Pi.add_apply, Pi.smul_apply, e0_eq, Pi.single_apply, smul_eq_mul]`. Unfold `liftVec`.

Distinguish the cases in `h : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1`. Rewrite using `[dif_pos h, hc, if_neg (by simp only [fst, Fin.ext_iff]; omega), mul_zero, add_zero]`. Use `congr 1`. Simplify using `only [levPos, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[dif_neg h, zero_add]`. Distinguish the cases in `h0 : i = fst k r'`. Rewrite using `[if_pos h0, mul_one, h0]`. Rewrite using `[if_neg h0, mul_zero, ← hu]`. Use `congr 1`.

Simplify using `only [fst, lst, Fin.ext_iff] at h0 ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem decomp (u : Fin (2 * (1 + r') + k + 1) → ℂ) (hu : u (lst k r') = 0) :
    u = liftVec k 1 r' ((incl k 1 r')ᴴ *ᵥ u) + u (fst k r') • e0 k r' := by
  have hc : ∀ j, ((incl k 1 r')ᴴ *ᵥ u) j = u (levPos k 1 r' j) := fun j =>
    inclH_mul k 1 r' (Matrix.of fun a _ => u a) j j
  ext i
  have hi := i.isLt
  rw [Pi.add_apply, Pi.smul_apply, e0_eq, Pi.single_apply, smul_eq_mul]
  unfold liftVec
  by_cases h : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos h, hc, if_neg (by simp only [fst, Fin.ext_iff]; omega), mul_zero, add_zero]
    congr 1
    simp only [levPos, Fin.ext_iff]
    omega
  · rw [dif_neg h, zero_add]
    by_cases h0 : i = fst k r'
    · rw [if_pos h0, mul_one, h0]
    · rw [if_neg h0, mul_zero, ← hu]
      congr 1
      simp only [fst, lst, Fin.ext_iff] at h0 ⊢
      omega

/- English proof (translation)
Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hp]`.
-/
theorem pair_unitary {n : ℕ} (H p : Matrix (Fin n) (Fin n) ℂ) (hp : pᴴ * H * p = H) (v w : Fin n → ℂ) :
    star (p *ᵥ w) ⬝ᵥ (H *ᵥ (p *ᵥ v)) = star w ⬝ᵥ (H *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hp]

/- English proof (translation)
Rewrite using `[liftVec_eq, liftVec_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, gram_inner]`.
-/
theorem pair_lift (v w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' w) ⬝ᵥ (Hpk k (1 + r') *ᵥ liftVec k 1 r' v) = star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [liftVec_eq, liftVec_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, gram_inner]

/- English proof (translation)
Rewrite using `[star_add, add_dotProduct, star_smul, smul_dotProduct, pair_e0_left, mulVec_add, dotProduct_add, pair_lift, mulVec_smul, gram_mulVec_e0, dotProduct_smul, dotProduct_single_one]`. Simplify using `[lift_lst, e0_lst_eq_zero]`.
-/
theorem pair_shift (v w : Fin (2 * r' + k + 1) → ℂ) (c d : ℂ) :
    star (liftVec k 1 r' w + d • e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ (liftVec k 1 r' v + c • e0 k r')) =
      star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [star_add, add_dotProduct, star_smul, smul_dotProduct, pair_e0_left, mulVec_add, dotProduct_add,
    pair_lift, mulVec_smul, gram_mulVec_e0, dotProduct_smul, dotProduct_single_one]
  simp [lift_lst, e0_lst_eq_zero]

/- English proof (translation)
Introduce `k r' a p hp he`. Establish `hp' : pᴴ * Hpk k (1 + r') * p = Hpk k (1 + r')` using `hp`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Establish `h` using `pair_unitary _ p hp' (Pi.single (lst k r') 1) (e0 k r')`.

Rewrite `h` using `[he, zero_smul, star_zero, zero_dotProduct, pair_e0_left]`. Simplify using `at h`. Establish `hl : ∀ w, (p *ᵥ liftVec k 1 r' w) (lst k r') = 0`. Introduce `w`. Establish `h` using `pair_unitary _ p hp' (liftVec k 1 r' w) (e0 k r')`.

Rewrite `h` using `[he, star_smul, smul_dotProduct, pair_e0_left, pair_e0_left, lift_lst, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h).resolve_left (star_ne_zero.2 ha)`. Establish `hd : ∀ w, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (((incl k 1 r')ᴴ * p * incl k 1 r') *ᵥ w) + (p *ᵥ liftVec k 1 r' w) (fst k r') • e0 k r'`. Introduce `w`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, ← liftVec_eq k 1 r' w]`.

Conclude with `decomp k r' _ (hl w)`. Use `⟨ha, (incl k 1 r')ᴴ * p * incl k 1 r', ?_, fun w => ⟨_, hd w⟩⟩` and prove the remaining obligations. Generalize the expression as in `(incl k 1 r')ᴴ * p * incl k 1 r' = g at hd`. Use `show gᴴ * Hpk k r' * g = Hpk k r'`. Use extensionality with `i j`.

Establish `h` using `pair_unitary _ p hp' (liftVec k 1 r' (Pi.single j 1)) (liftVec k 1 r' (Pi.single i 1))`. Rewrite `h` using `[hd (Pi.single j 1), hd (Pi.single i 1), pair_shift, pair_lift, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← Pi.single_star, star_one, single_one_dotProduct, single_one_dotProduct, mulVec_single_one, mulVec_single_one]`. Conclude with `h`.
-/
theorem acts_through_level_one : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  intro k r' a p hp he
  have hp' : pᴴ * Hpk k (1 + r') * p = Hpk k (1 + r') := hp
  have ha : a ≠ 0 := by
    rintro rfl
    have h := pair_unitary _ p hp' (Pi.single (lst k r') 1) (e0 k r')
    rw [he, zero_smul, star_zero, zero_dotProduct, pair_e0_left] at h
    simp at h
  have hl : ∀ w, (p *ᵥ liftVec k 1 r' w) (lst k r') = 0 := by
    intro w
    have h := pair_unitary _ p hp' (liftVec k 1 r' w) (e0 k r')
    rw [he, star_smul, smul_dotProduct, pair_e0_left, pair_e0_left, lift_lst, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (star_ne_zero.2 ha)
  have hd : ∀ w, p *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (((incl k 1 r')ᴴ * p * incl k 1 r') *ᵥ w) +
        (p *ᵥ liftVec k 1 r' w) (fst k r') • e0 k r' := by
    intro w
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← liftVec_eq k 1 r' w]
    exact decomp k r' _ (hl w)
  refine ⟨ha, (incl k 1 r')ᴴ * p * incl k 1 r', ?_, fun w => ⟨_, hd w⟩⟩
  generalize (incl k 1 r')ᴴ * p * incl k 1 r' = g at hd
  show gᴴ * Hpk k r' * g = Hpk k r'
  ext i j
  have h := pair_unitary _ p hp' (liftVec k 1 r' (Pi.single j 1)) (liftVec k 1 r' (Pi.single i 1))
  rw [hd (Pi.single j 1), hd (Pi.single i 1), pair_shift, pair_lift, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec, ← Pi.single_star, star_one, single_one_dotProduct,
    single_one_dotProduct, mulVec_single_one, mulVec_single_one] at h
  exact h

end GlobalTheory.HCXi.LineStabiliser
