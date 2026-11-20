import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero

noncomputable section

open Matrix

namespace GlobalTheory.Hk3.SquareDiag

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n' : ℕ}

def selE (a : Fin n' → ℕ) (n : ℕ) : Matrix (Fin n') (Fin n) L :=
  Matrix.of fun i p => if (i : ℕ) = (p : ℕ) ∧ 0 < a i then 1 else 0

def halfSel (a : Fin n' → ℕ) (i j : Fin n') : L :=
  if a i < a j ∨ (a i = a j ∧ (i : ℕ) < (j : ℕ)) then 1 else if (i : ℕ) = (j : ℕ) then 2⁻¹ else 0

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.diagonal_mul, selE, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem diag_sel (ϖ : L) (a : Fin n' → ℕ) (n : ℕ) :
    (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) =
      (diagonal (fun i : Fin n' => ϖ⁻¹ ^ a i) : Matrix (Fin n') (Fin n') L) * (selE a n : Matrix (Fin n') (Fin n) L) := by
  ext i j
  simp only [Matrix.diagonal_mul, selE, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.diagonal_apply]`. Simplify using `only [selE, Matrix.of_apply, Matrix.transpose_apply]`. Distinguish the cases in `h : (i : ℕ) < n ∧ 0 < a i`. Rewrite using `[Finset.sum_eq_single (⟨i, h.1⟩ : Fin n)]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[h]`. Establish `: (j : ℕ) ≠ (i : ℕ)` using `fun e => hij (Fin.ext e.symm)`. Simplify using `[hij, this]`.

Introduce `b _ hb`. Establish `: (i : ℕ) ≠ (b : ℕ)` using `fun e => hb (Fin.ext e.symm)`. Simplify using `[this]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.

Rewrite using `[if_neg h, ite_self]`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations. Establish `: ¬ ((i : ℕ) = (p : ℕ) ∧ 0 < a i)` using `fun ⟨e, ha⟩ => h ⟨e ▸ p.isLt, ha⟩`. Rewrite using `[if_neg this, zero_mul]`.
-/
theorem selE_mul_transpose (a : Fin n' → ℕ) (n : ℕ) :
    (selE (L := L) a n : Matrix (Fin n') (Fin n) L) * (selE a n : Matrix (Fin n') (Fin n) L)ᵀ = diagonal (fun i : Fin n' => if (i : ℕ) < n ∧ 0 < a i then (1 : L) else 0) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [selE, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : (i : ℕ) < n ∧ 0 < a i
  · rw [Finset.sum_eq_single (⟨i, h.1⟩ : Fin n)]
    · by_cases hij : i = j
      · subst hij; simp [h]
      · have : (j : ℕ) ≠ (i : ℕ) := fun e => hij (Fin.ext e.symm)
        simp [hij, this]
    · intro b _ hb
      have : (i : ℕ) ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
      simp [this]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h, ite_self]
    refine Finset.sum_eq_zero fun p _ => ?_
    have : ¬ ((i : ℕ) = (p : ℕ) ∧ 0 < a i) := fun ⟨e, ha⟩ => h ⟨e ▸ p.isLt, ha⟩
    rw [if_neg this, zero_mul]

/- English proof (translation)
Unfold `halfSel`. Break down `eq_or_ne i j with rfl | hne` into its components or cases. Simplify using `only [lt_irrefl, false_or, and_false, if_false, if_true]`. Rewrite using `[← two_mul, mul_inv_cancel₀ h2]`. Establish `hne' : (i : ℕ) ≠ (j : ℕ)` using `Fin.val_ne_of_ne hne`.

Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp | rw [← two_mul, mul_inv_cancel₀ h2]`.
-/
theorem halfSel_add (h2 : (2 : L) ≠ 0) (a : Fin n' → ℕ) (i j : Fin n') :
    halfSel (L := L) a i j + halfSel a j i = 1 := by
  unfold halfSel
  rcases eq_or_ne i j with rfl | hne
  · simp only [lt_irrefl, false_or, and_false, if_false, if_true]
    rw [← two_mul, mul_inv_cancel₀ h2]
  have hne' : (i : ℕ) ≠ (j : ℕ) := Fin.val_ne_of_ne hne
  split_ifs <;> first | (exfalso; omega) | simp | rw [← two_mul, mul_inv_cancel₀ h2]

end GlobalTheory.Hk3.SquareDiag

namespace GlobalTheory.Hk3.SquareDiag

set_option maxHeartbeats 1000000 in
open GlobalTheory.Hk3 in

/- English proof (translation)
Introduce `L _ _ ϖ σ q δ n n' A B ψ hU hq hA hB hAB hherm hδ hψ hne a hC`. Establish `hσσ` using `hU.1`. Establish `hσv` using `hU.2.1`. Establish `hσϖ` using `hU.2.2.1`. Establish `hvϖ` using `hU.2.2.2.1`.

Establish `h2 : Valued.v (2 : L) = 1` using `GlobalTheory.Hk3.Inh.v_two hU hq`. Establish `h20 : (2 : L) ≠ 0` using `by intro h; rw [h, map_zero] at h2; exact zero_ne_one h2`. Establish `hϖ0 : ϖ ≠ 0` using `by intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ`. Establish `hϖlt : Valued.v ϖ < 1` using `by rw [hvϖ]; decide`. Establish `hϖi : ϖ ∈ Formalism.UG.intL L` using `le_of_lt hϖlt`.

Establish `hδi : δ ∈ Formalism.UG.intL L` using `le_of_eq hδ.1`. Establish `hσi : ∀ x ∈ Formalism.UG.intL L, σ x ∈ Formalism.UG.intL L` using `fun x hx => by show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx`. Establish `hσpow : ∀ k : ℕ, σ (ϖ⁻¹ ^ k) = ϖ⁻¹ ^ k` using `fun k => by rw [map_pow, map_inv₀, hσϖ]`. Use `set D : Matrix (Fin n') (Fin n) L := Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) with hDdef`. Use `set E : Matrix (Fin n') (Fin n) L := selE a n with hEdef`.

Use `set Δ : Matrix (Fin n') (Fin n') L := diagonal (fun i : Fin n' => ϖ⁻¹ ^ a i) with hΔ`. Establish `hDE : D = Δ * E` using `diag_sel ϖ a n`. Establish `hEσ : E.map σ = E`. Apply the tactic sequence `ext i p; simp only [E, selE, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp`. Establish `hΔσ : Δ.map σ = Δ`.

Use extensionality with `i j`. Simplify using `only [Δ, Matrix.map_apply, Matrix.diagonal_apply]`. Use `split_ifs`. Conclude with `hσpow _`. Conclude with `map_zero σ`.

Establish `hDσ : D.map σ = D` using `by rw [hDE, Matrix.map_mul, hEσ, hΔσ]`. Establish `hAm : A.map σ = Aᵀ` using `by ext i j; simp [hherm]`. Establish `hAσ : (A.map σ)ᵀ = A` using `by rw [hAm, Matrix.transpose_transpose]`. Establish `hBA : B * A = 1` using `mul_eq_one_comm.mp hAB`. Establish `hBσ : (B.map σ)ᵀ = B`.

Establish `h1 : (B.map σ)ᵀ * A = 1`. Establish `: ((A * B).map σ)ᵀ = ((1 : Matrix (Fin n) (Fin n) L).map σ)ᵀ` using `by rw [hAB]`. Rewrite `this` using `[Matrix.map_mul, Matrix.transpose_mul, hAσ, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Establish `hEi : ∀ i p, E i p ∈ Formalism.UG.intL L`.

Introduce `i p`. Simplify using `only [E, selE, Matrix.of_apply]`. Use `split_ifs`. Conclude with `(Formalism.UG.intL L).one_mem`. Conclude with `(Formalism.UG.intL L).zero_mem`.

Establish `hErow : ∀ i : Fin n', ¬ ((i : ℕ) < n ∧ 0 < a i) → ∀ p, E i p = 0`. Introduce `i h p`. Simplify using `only [E, selE, Matrix.of_apply]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨e, ha⟩`.

Conclude with `h ⟨e ▸ p.isLt, ha⟩`. Use `set A' : Matrix (Fin n') (Fin n') L := E * A * Eᵀ with hA'def`. Establish `hA'i : ∀ i j, A' i j ∈ Formalism.UG.intL L` using `fun i j => matMul_int (matMul_int hEi hA) (fun p k => hEi k p) i j`. Establish `hA'σ : ∀ i j, σ (A' i j) = A' j i`. Establish `hm : A'.map σ = A'ᵀ`.

Rewrite using `[hA'def, Matrix.map_mul, Matrix.map_mul, hEσ, hAm, Matrix.transpose_map, hEσ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Introduce `i j`. Use `congrFun (congrFun hm i) j` as an intermediate fact. Simplify using `using this`. Use `set s : Fin n' → L := fun i => if (i : ℕ) < n ∧ 0 < a i then (1 : L) else 0 with hsdef`.

Establish `hEE : E * Eᵀ = diagonal s` using `selE_mul_transpose a n`. Establish `hA's : ∀ i j, A' i j * s i = A' i j ∧ A' i j * s j = A' i j`. Introduce `i j`. Distinguish the cases in `hi : (i : ℕ) < n ∧ 0 < a i`. Distinguish the cases in `hj : (j : ℕ) < n ∧ 0 < a j`.

Simplify using `[s, hi, hj]`. Establish `: A' i j = 0`. Simplify using `only [A', Matrix.mul_apply, Matrix.transpose_apply, hErow j hj, mul_zero, Finset.sum_const_zero]`. Simplify using `[this]`. Establish `: A' i j = 0`.

Simplify using `only [A', Matrix.mul_apply, Matrix.transpose_apply, hErow i hi, zero_mul, Finset.sum_const_zero]`. Simplify using `[this]`. Use `set G : Matrix (Fin n') (Fin n') L := D * A * (D.map σ)ᵀ with hGdef`. Establish `hGΔ : G = Δ * A' * Δ`. Rewrite using `[hGdef, hDσ, hDE, Matrix.transpose_mul, hΔ, Matrix.diagonal_transpose, hA'def]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `hGe : ∀ i j, G i j = ϖ⁻¹ ^ a i * A' i j * ϖ⁻¹ ^ a j`. Introduce `i j`. Rewrite using `[hGΔ, hΔ, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Establish `hGσ : ∀ i j, σ (G i j) = G j i`.

Introduce `i j`. Rewrite using `[hGe, hGe, map_mul, map_mul, hσpow, hσpow, hA'σ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbound : ∀ i j, ϖ ^ (max (max (a i) (a j)) 1) * G j i ∈ Formalism.UG.intL L`. Introduce `i j`.

Use `set m := max (max (a i) (a j)) 1 with hm`. Establish `hmi : a i ≤ m` using `by omega`. Establish `hmj : a j ≤ m` using `by omega`. Establish `hm1 : 1 ≤ m` using `by omega`. Establish `hsm : ∀ b' ∈ Formalism.UG.intL L, Valued.v (δ * (b' * ϖ ^ m)) < 1 ∧ ∀ k ≤ m, δ * (b' * ϖ ^ m) * ϖ⁻¹ ^ k ∈ Formalism.UG.intL L`.

Introduce `b' hb'`. Use `⟨?_, fun k hk => ?_⟩` and prove the remaining obligations. Establish `e : δ * (b' * ϖ ^ m) = (δ * b' * ϖ ^ (m - 1)) * ϖ`. Rewrite using `[mul_assoc, ← pow_succ, Nat.sub_add_cancel hm1, mul_assoc]`. Establish `hx : Valued.v (δ * b' * ϖ ^ (m - 1)) ≤ 1` using `mul_mem (mul_mem hδi hb') (pow_mem hϖi _)`.

Rewrite using `[e, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hx) hϖlt`. Establish `e : δ * (b' * ϖ ^ m) * ϖ⁻¹ ^ k = δ * b' * ϖ ^ (m - k)`. Rewrite using `[← pow_sub_mul_pow ϖ hk, inv_pow]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `mul_mem (mul_mem hδi hb') (pow_mem hϖi _)`. Establish `hw : δ ^ 2 * ϖ ^ m * G j i ∈ Formalism.UG.intL L`. Use `int_of_psi hU ψ hne _ (fun b hb => ?_)` and prove the remaining obligations. Establish `hσb` using `hσi b hb`.

Use `set x := δ * (b * ϖ ^ m) with hx`. Use `set y := δ * (σ b * ϖ ^ m) with hy`. Establish `hσx : σ x = -y` using `by rw [hx, hy, map_mul, map_mul, map_pow, hσϖ, hδ.2]; ring`. Establish `hσy : σ y = -x` using `by rw [hx, hy, map_mul, map_mul, map_pow, hσϖ, hδ.2, hσσ]; ring`. Use `set C : Matrix (Fin n') (Fin n') L := Matrix.single i j x + Matrix.single j i y with hCdef`.

Establish `hskew : ∀ k l, σ (C k l) = - C l k`. Introduce `k l`. Simplify using `only [hCdef, Matrix.add_apply, Matrix.single_apply]`. Establish `e1 : (i = l ∧ j = k) ↔ (j = k ∧ i = l)` using `and_comm`. Establish `e2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l)` using `and_comm`.

Apply the tactic sequence `by_cases hP : i = k ∧ j = l <;> by_cases hQ : j = k ∧ i = l`. Rewrite using `[if_pos hP, if_pos hQ, if_pos (e1.2 hQ), if_pos (e2.2 hP), map_add, hσx, hσy]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_pos hP, if_neg hQ, if_neg (fun h => hQ (e1.1 h)), if_pos (e2.2 hP), map_add, hσx, map_zero]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hP, if_pos hQ, if_pos (e1.2 hQ), if_neg (fun h => hP (e2.1 h)), map_add, hσy, map_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hP, if_neg hQ, if_neg (fun h => hQ (e1.1 h)), if_neg (fun h => hP (e2.1 h)), map_add, map_zero]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsmall : ∀ k l, Valued.v (C k l) < 1`.

Introduce `k l`. Simplify using `only [hCdef, Matrix.add_apply, Matrix.single_apply]`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `(hsm b hb).1`.

Rewrite using `[map_zero]`. Conclude with `zero_lt_one`. Use `split_ifs`. Conclude with `(hsm (σ b) hσb).1`. Rewrite using `[map_zero]`.

Conclude with `zero_lt_one`. Establish `hsingle : ∀ (r s' : Fin n') (z : L), (∀ p, z * D s' p ∈ Formalism.UG.intL L) → ∀ k p, (Matrix.single r s' z * D) k p ∈ Formalism.UG.intL L`. Introduce `r s' z hz k p`. Distinguish the cases in `h : k = r`. Substitute `h` using the available equality.

Rewrite using `[Matrix.single_mul_apply_same]`. Conclude with `hz p`. Rewrite using `[Matrix.single_mul_apply_of_ne _ _ _ _ _ h]`. Conclude with `(Formalism.UG.intL L).zero_mem`. Establish `hDrow : ∀ (s' : Fin n') (b' : L), b' ∈ Formalism.UG.intL L → a s' ≤ m → ∀ p, δ * (b' * ϖ ^ m) * D s' p ∈ Formalism.UG.intL L`.

Introduce `s' b' hb' hs' p`. Rewrite using `[hDdef, Matrix.of_apply]`. Use `split_ifs`. Conclude with `(hsm b' hb').2 _ hs'`. Rewrite using `[mul_zero]`.

Conclude with `(Formalism.UG.intL L).zero_mem`. Establish `hint : ∀ k p, (C * D) k p ∈ Formalism.UG.intL L`. Introduce `k p`. Rewrite using `[hCdef, Matrix.add_mul, Matrix.add_apply]`. Conclude with `add_mem (hsingle i j x (hDrow j b hb hmj) k p) (hsingle j i y (hDrow i (σ b) hσb hmi) k p)`.

Establish `h` using `hC C hskew hsmall hint`. Establish `htr : Matrix.trace (C * G) = x * G j i + y * G i j`. Rewrite using `[hCdef, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul, smul_eq_mul, smul_eq_mul]`. Rewrite `h` using `[htr]`. Establish `key : (δ * (x * G j i + y * G i j) + σ (δ * (x * G j i + y * G i j))) / 2 = b * (δ ^ 2 * ϖ ^ m * G j i) + σ (b * (δ ^ 2 * ϖ ^ m * G j i))`.

Rewrite using `[hx, hy]`. Simplify using `only [map_add, map_mul, map_pow, hσϖ, hδ.2, hσσ, hGσ]`. Rewrite using `[div_eq_iff h20]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← key]`.

Conclude with `h`. Establish `e : Valued.v (δ ^ 2 * ϖ ^ m * G j i) = Valued.v (ϖ ^ m * G j i)`. Rewrite using `[mul_assoc, map_mul, map_pow, hδ.1, one_pow, one_mul]`. Rewrite using `[GlobalTheory.Hk3.mem_intL_iff, ← e]`. Conclude with `hw`.

Use `set t : Fin n' → Fin n' → L := halfSel a with htdef`. Establish `ht : ∀ i j, t i j + t j i = 1` using `halfSel_add h20 a`. Establish `h2i : (2 : L)⁻¹ ∈ Formalism.UG.intL L` using `by rw [GlobalTheory.Hk3.mem_intL_iff, map_inv₀, h2, inv_one]`. Establish `htσ : ∀ i j, σ (t i j) = t i j`. Apply the tactic sequence `intro i j; simp only [htdef, halfSel]; split_ifs <;> simp [map_inv₀, map_ofNat]`.

Establish `hcore : ∀ i j, a i ≤ a j → ϖ⁻¹ ^ a i * A' i j ∈ Formalism.UG.intL L`. Introduce `i j hle`. Break down `Nat.eq_zero_or_pos (a i) with h0 | hpos` into its components or cases. Rewrite using `[h0, pow_zero, one_mul]`. Conclude with `hA'i i j`.

Establish `hmx : max (max (a j) (a i)) 1 = a j` using `by omega`. Use `hbound j i` as an intermediate fact. Rewrite `this` using `[hmx, hGe i j]`. Establish `e : ϖ ^ a j * (ϖ⁻¹ ^ a i * A' i j * ϖ⁻¹ ^ a j) = ϖ⁻¹ ^ a i * A' i j`. Rewrite using `[inv_pow, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Use `set W : Matrix (Fin n') (Fin n') L := Matrix.of fun i j => t i j * (ϖ⁻¹ ^ a i * A' i j) with hWdef`. Establish `hWi : ∀ i j, W i j ∈ Formalism.UG.intL L`. Introduce `i j`.

Simplify using `only [hWdef, Matrix.of_apply, htdef, halfSel]`. Use `split_ifs with h1 h3`. Apply the tactic sequence `exact mul_mem (Formalism.UG.intL L).one_mem (hcore i j (by rcases h1 with h | ⟨h, -⟩ <;> omega))`. Conclude with `mul_mem h2i (hcore i j (le_of_eq (congrArg a (Fin.ext h3))))`. Rewrite using `[zero_mul]`.

Conclude with `(Formalism.UG.intL L).zero_mem`. Use `set Z : Matrix (Fin n') (Fin n) L := W * E with hZdef`. Use `set Zσ : Matrix (Fin n) (Fin n') L := (Z.map σ)ᵀ with hZσdef`. Establish `hZi : ∀ i p, Z i p ∈ Formalism.UG.intL L` using `matMul_int hWi hEi`. Establish `hZσi : ∀ p i, Zσ p i ∈ Formalism.UG.intL L` using `fun p i => hσi _ (hZi i p)`.

Establish `hDZ : D * Zσ = Δ * (diagonal s * (W.map σ)ᵀ)`. Rewrite using `[hDE, hZσdef, hZdef, Matrix.map_mul, Matrix.transpose_mul, hEσ, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE]`. Establish `hZD : Z * Dᵀ = W * (diagonal s * Δ)`. Rewrite using `[hZdef, hDE, Matrix.transpose_mul, hΔ, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE]`. Establish `hsplit : G = D * Zσ + Z * Dᵀ`.

Use extensionality with `i j`. Rewrite using `[hGe, Matrix.add_apply, hDZ, hZD, hΔ, Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal]`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, hWdef, Matrix.of_apply, map_mul, htσ, hσpow, hA'σ]`. Take `⟨e1, e2⟩` from `hA's i j`. Take the linear combination `(-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * t j i)) * e1 + (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * t i j)) * e2 + (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * A' i j)) * ht i j`.

Use `⟨Z * B, fun i p => matMul_int hZi hB i p, ?_⟩` and prove the remaining obligations. Establish `hlσ : ((D - Z * B).map σ)ᵀ = Dᵀ - B * Zσ`. Rewrite using `[hZσdef, Matrix.map_sub _ (map_sub σ), hDσ, Matrix.transpose_sub, Matrix.map_mul, Matrix.transpose_mul, hBσ]`. Establish `hM : (D - Z * B) * A * ((D - Z * B).map σ)ᵀ = Z * B * Zσ`. Rewrite using `[hlσ, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]`.

Establish `e1 : D * A * (B * Zσ) = D * Zσ` using `by rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hAB, Matrix.one_mul]`. Establish `e2 : Z * B * A * Dᵀ = Z * Dᵀ` using `by rw [Matrix.mul_assoc Z, hBA, Matrix.mul_one]`. Establish `e3 : Z * B * A * (B * Zσ) = Z * B * Zσ`. Combine the equalities or inequalities in the displayed calculation. Establish `e4 : D * A * Dᵀ = G` using `by rw [hGdef, hDσ]`.

Rewrite using `[e1, e2, e3, e4, hsplit]`. Normalize the expressions using the abelian group laws. Introduce `i j`. Rewrite using `[hM]`. Conclude with `matMul_int (matMul_int hZi hB) hZσi i j`.
-/
theorem square_diag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A B : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) → (∀ i j, B i j ∈ Formalism.UG.intL L) → A * B = 1 →
    (∀ i j, σ (A i j) = A j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ a : Fin n' → ℕ,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))).map σ))) + σ (δ * Matrix.trace (C * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))).map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q δ n n' A B ψ hU hq hA hB hAB hherm hδ hψ hne a hC
  classical
  have hσσ := hU.1
  have hσv := hU.2.1
  have hσϖ := hU.2.2.1
  have hvϖ := hU.2.2.2.1
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have h20 : (2 : L) ≠ 0 := by intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
  have hϖ0 : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖlt : Valued.v ϖ < 1 := by rw [hvϖ]; decide
  have hϖi : ϖ ∈ Formalism.UG.intL L := le_of_lt hϖlt
  have hδi : δ ∈ Formalism.UG.intL L := le_of_eq hδ.1
  have hσi : ∀ x ∈ Formalism.UG.intL L, σ x ∈ Formalism.UG.intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
  have hσpow : ∀ k : ℕ, σ (ϖ⁻¹ ^ k) = ϖ⁻¹ ^ k := fun k => by rw [map_pow, map_inv₀, hσϖ]
  set D : Matrix (Fin n') (Fin n) L := Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) with hDdef
  set E : Matrix (Fin n') (Fin n) L := selE a n with hEdef
  set Δ : Matrix (Fin n') (Fin n') L := diagonal (fun i : Fin n' => ϖ⁻¹ ^ a i) with hΔ
  have hDE : D = Δ * E := diag_sel ϖ a n
  have hEσ : E.map σ = E := by
    ext i p; simp only [E, selE, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp
  have hΔσ : Δ.map σ = Δ := by
    ext i j; simp only [Δ, Matrix.map_apply, Matrix.diagonal_apply]; split_ifs
    · exact hσpow _
    · exact map_zero σ
  have hDσ : D.map σ = D := by rw [hDE, Matrix.map_mul, hEσ, hΔσ]
  have hAm : A.map σ = Aᵀ := by ext i j; simp [hherm]
  have hAσ : (A.map σ)ᵀ = A := by rw [hAm, Matrix.transpose_transpose]
  have hBA : B * A = 1 := mul_eq_one_comm.mp hAB
  have hBσ : (B.map σ)ᵀ = B := by
    have h1 : (B.map σ)ᵀ * A = 1 := by
      have : ((A * B).map σ)ᵀ = ((1 : Matrix (Fin n) (Fin n) L).map σ)ᵀ := by rw [hAB]
      rwa [Matrix.map_mul, Matrix.transpose_mul, hAσ, Matrix.map_one _ (map_zero σ) (map_one σ),
        Matrix.transpose_one] at this
    calc (B.map σ)ᵀ = (B.map σ)ᵀ * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = B := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hEi : ∀ i p, E i p ∈ Formalism.UG.intL L := by
    intro i p; simp only [E, selE, Matrix.of_apply]; split_ifs
    · exact (Formalism.UG.intL L).one_mem
    · exact (Formalism.UG.intL L).zero_mem
  have hErow : ∀ i : Fin n', ¬ ((i : ℕ) < n ∧ 0 < a i) → ∀ p, E i p = 0 := by
    intro i h p; simp only [E, selE, Matrix.of_apply]
    rw [if_neg]; rintro ⟨e, ha⟩; exact h ⟨e ▸ p.isLt, ha⟩
  set A' : Matrix (Fin n') (Fin n') L := E * A * Eᵀ with hA'def
  have hA'i : ∀ i j, A' i j ∈ Formalism.UG.intL L := fun i j =>
    matMul_int (matMul_int hEi hA) (fun p k => hEi k p) i j
  have hA'σ : ∀ i j, σ (A' i j) = A' j i := by
    have hm : A'.map σ = A'ᵀ := by
      rw [hA'def, Matrix.map_mul, Matrix.map_mul, hEσ, hAm, Matrix.transpose_map, hEσ, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun hm i) j
    simpa using this
  set s : Fin n' → L := fun i => if (i : ℕ) < n ∧ 0 < a i then (1 : L) else 0 with hsdef
  have hEE : E * Eᵀ = diagonal s := selE_mul_transpose a n
  have hA's : ∀ i j, A' i j * s i = A' i j ∧ A' i j * s j = A' i j := by
    intro i j
    by_cases hi : (i : ℕ) < n ∧ 0 < a i
    · by_cases hj : (j : ℕ) < n ∧ 0 < a j
      · simp [s, hi, hj]
      · have : A' i j = 0 := by
          simp only [A', Matrix.mul_apply, Matrix.transpose_apply, hErow j hj, mul_zero, Finset.sum_const_zero]
        simp [this]
    · have : A' i j = 0 := by
        simp only [A', Matrix.mul_apply, Matrix.transpose_apply, hErow i hi, zero_mul, Finset.sum_const_zero]
      simp [this]
  set G : Matrix (Fin n') (Fin n') L := D * A * (D.map σ)ᵀ with hGdef
  have hGΔ : G = Δ * A' * Δ := by
    rw [hGdef, hDσ, hDE, Matrix.transpose_mul, hΔ, Matrix.diagonal_transpose, hA'def]
    simp only [Matrix.mul_assoc]
  have hGe : ∀ i j, G i j = ϖ⁻¹ ^ a i * A' i j * ϖ⁻¹ ^ a j := by
    intro i j; rw [hGΔ, hΔ, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hGσ : ∀ i j, σ (G i j) = G j i := by
    intro i j; rw [hGe, hGe, map_mul, map_mul, hσpow, hσpow, hA'σ]; ring

  have hbound : ∀ i j, ϖ ^ (max (max (a i) (a j)) 1) * G j i ∈ Formalism.UG.intL L := by
    intro i j
    set m := max (max (a i) (a j)) 1 with hm
    have hmi : a i ≤ m := by omega
    have hmj : a j ≤ m := by omega
    have hm1 : 1 ≤ m := by omega
    have hsm : ∀ b' ∈ Formalism.UG.intL L, Valued.v (δ * (b' * ϖ ^ m)) < 1 ∧
        ∀ k ≤ m, δ * (b' * ϖ ^ m) * ϖ⁻¹ ^ k ∈ Formalism.UG.intL L := by
      intro b' hb'
      refine ⟨?_, fun k hk => ?_⟩
      · have e : δ * (b' * ϖ ^ m) = (δ * b' * ϖ ^ (m - 1)) * ϖ := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm1, mul_assoc]
        have hx : Valued.v (δ * b' * ϖ ^ (m - 1)) ≤ 1 := mul_mem (mul_mem hδi hb') (pow_mem hϖi _)
        rw [e, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) hϖlt
      · have e : δ * (b' * ϖ ^ m) * ϖ⁻¹ ^ k = δ * b' * ϖ ^ (m - k) := by
          rw [← pow_sub_mul_pow ϖ hk, inv_pow]; field_simp
        rw [e]; exact mul_mem (mul_mem hδi hb') (pow_mem hϖi _)
    have hw : δ ^ 2 * ϖ ^ m * G j i ∈ Formalism.UG.intL L := by
      refine int_of_psi hU ψ hne _ (fun b hb => ?_)
      have hσb := hσi b hb
      set x := δ * (b * ϖ ^ m) with hx
      set y := δ * (σ b * ϖ ^ m) with hy
      have hσx : σ x = -y := by rw [hx, hy, map_mul, map_mul, map_pow, hσϖ, hδ.2]; ring
      have hσy : σ y = -x := by rw [hx, hy, map_mul, map_mul, map_pow, hσϖ, hδ.2, hσσ]; ring
      set C : Matrix (Fin n') (Fin n') L := Matrix.single i j x + Matrix.single j i y with hCdef
      have hskew : ∀ k l, σ (C k l) = - C l k := by
        intro k l
        simp only [hCdef, Matrix.add_apply, Matrix.single_apply]
        have e1 : (i = l ∧ j = k) ↔ (j = k ∧ i = l) := and_comm
        have e2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
        by_cases hP : i = k ∧ j = l <;> by_cases hQ : j = k ∧ i = l
        · rw [if_pos hP, if_pos hQ, if_pos (e1.2 hQ), if_pos (e2.2 hP), map_add, hσx, hσy]; ring
        · rw [if_pos hP, if_neg hQ, if_neg (fun h => hQ (e1.1 h)), if_pos (e2.2 hP), map_add, hσx, map_zero]; ring
        · rw [if_neg hP, if_pos hQ, if_pos (e1.2 hQ), if_neg (fun h => hP (e2.1 h)), map_add, hσy, map_zero]; ring
        · rw [if_neg hP, if_neg hQ, if_neg (fun h => hQ (e1.1 h)), if_neg (fun h => hP (e2.1 h)), map_add, map_zero]; ring
      have hsmall : ∀ k l, Valued.v (C k l) < 1 := by
        intro k l
        simp only [hCdef, Matrix.add_apply, Matrix.single_apply]
        refine Valuation.map_add_lt _ ?_ ?_
        · split_ifs
          · exact (hsm b hb).1
          · rw [map_zero]; exact zero_lt_one
        · split_ifs
          · exact (hsm (σ b) hσb).1
          · rw [map_zero]; exact zero_lt_one
      have hsingle : ∀ (r s' : Fin n') (z : L), (∀ p, z * D s' p ∈ Formalism.UG.intL L) →
          ∀ k p, (Matrix.single r s' z * D) k p ∈ Formalism.UG.intL L := by
        intro r s' z hz k p
        by_cases h : k = r
        · subst h; rw [Matrix.single_mul_apply_same]; exact hz p
        · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ h]; exact (Formalism.UG.intL L).zero_mem
      have hDrow : ∀ (s' : Fin n') (b' : L), b' ∈ Formalism.UG.intL L → a s' ≤ m →
          ∀ p, δ * (b' * ϖ ^ m) * D s' p ∈ Formalism.UG.intL L := by
        intro s' b' hb' hs' p
        rw [hDdef, Matrix.of_apply]
        split_ifs
        · exact (hsm b' hb').2 _ hs'
        · rw [mul_zero]; exact (Formalism.UG.intL L).zero_mem
      have hint : ∀ k p, (C * D) k p ∈ Formalism.UG.intL L := by
        intro k p
        rw [hCdef, Matrix.add_mul, Matrix.add_apply]
        exact add_mem (hsingle i j x (hDrow j b hb hmj) k p) (hsingle j i y (hDrow i (σ b) hσb hmi) k p)
      have h := hC C hskew hsmall hint
      have htr : Matrix.trace (C * G) = x * G j i + y * G i j := by
        rw [hCdef, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul, smul_eq_mul, smul_eq_mul]
      rw [htr] at h
      have key : (δ * (x * G j i + y * G i j) + σ (δ * (x * G j i + y * G i j))) / 2 =
          b * (δ ^ 2 * ϖ ^ m * G j i) + σ (b * (δ ^ 2 * ϖ ^ m * G j i)) := by
        rw [hx, hy]
        simp only [map_add, map_mul, map_pow, hσϖ, hδ.2, hσσ, hGσ]
        rw [div_eq_iff h20]; ring
      rw [← key]; exact h
    have e : Valued.v (δ ^ 2 * ϖ ^ m * G j i) = Valued.v (ϖ ^ m * G j i) := by
      rw [mul_assoc, map_mul, map_pow, hδ.1, one_pow, one_mul]
    rw [GlobalTheory.Hk3.mem_intL_iff, ← e]; exact hw
  set t : Fin n' → Fin n' → L := halfSel a with htdef
  have ht : ∀ i j, t i j + t j i = 1 := halfSel_add h20 a
  have h2i : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by rw [GlobalTheory.Hk3.mem_intL_iff, map_inv₀, h2, inv_one]
  have htσ : ∀ i j, σ (t i j) = t i j := by
    intro i j; simp only [htdef, halfSel]; split_ifs <;> simp [map_inv₀, map_ofNat]
  have hcore : ∀ i j, a i ≤ a j → ϖ⁻¹ ^ a i * A' i j ∈ Formalism.UG.intL L := by
    intro i j hle
    rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hA'i i j
    · have hmx : max (max (a j) (a i)) 1 = a j := by omega
      have := hbound j i
      rw [hmx, hGe i j] at this
      have e : ϖ ^ a j * (ϖ⁻¹ ^ a i * A' i j * ϖ⁻¹ ^ a j) = ϖ⁻¹ ^ a i * A' i j := by
        rw [inv_pow, inv_pow]; field_simp
      rwa [e] at this
  set W : Matrix (Fin n') (Fin n') L := Matrix.of fun i j => t i j * (ϖ⁻¹ ^ a i * A' i j) with hWdef
  have hWi : ∀ i j, W i j ∈ Formalism.UG.intL L := by
    intro i j
    simp only [hWdef, Matrix.of_apply, htdef, halfSel]
    split_ifs with h1 h3
    · exact mul_mem (Formalism.UG.intL L).one_mem (hcore i j (by rcases h1 with h | ⟨h, -⟩ <;> omega))
    · exact mul_mem h2i (hcore i j (le_of_eq (congrArg a (Fin.ext h3))))
    · rw [zero_mul]; exact (Formalism.UG.intL L).zero_mem
  set Z : Matrix (Fin n') (Fin n) L := W * E with hZdef
  set Zσ : Matrix (Fin n) (Fin n') L := (Z.map σ)ᵀ with hZσdef
  have hZi : ∀ i p, Z i p ∈ Formalism.UG.intL L := matMul_int hWi hEi
  have hZσi : ∀ p i, Zσ p i ∈ Formalism.UG.intL L := fun p i => hσi _ (hZi i p)
  have hDZ : D * Zσ = Δ * (diagonal s * (W.map σ)ᵀ) := by
    rw [hDE, hZσdef, hZdef, Matrix.map_mul, Matrix.transpose_mul, hEσ, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE]
  have hZD : Z * Dᵀ = W * (diagonal s * Δ) := by
    rw [hZdef, hDE, Matrix.transpose_mul, hΔ, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE]
  have hsplit : G = D * Zσ + Z * Dᵀ := by
    ext i j
    rw [hGe, Matrix.add_apply, hDZ, hZD, hΔ, Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.diagonal_mul_diagonal,
      Matrix.mul_diagonal]
    simp only [Matrix.transpose_apply, Matrix.map_apply, hWdef, Matrix.of_apply, map_mul, htσ, hσpow, hA'σ]
    obtain ⟨e1, e2⟩ := hA's i j
    linear_combination (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * t j i)) * e1 + (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * t i j)) * e2 +
      (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * A' i j)) * ht i j
  refine ⟨Z * B, fun i p => matMul_int hZi hB i p, ?_⟩
  have hlσ : ((D - Z * B).map σ)ᵀ = Dᵀ - B * Zσ := by
    rw [hZσdef, Matrix.map_sub _ (map_sub σ), hDσ, Matrix.transpose_sub, Matrix.map_mul, Matrix.transpose_mul, hBσ]
  have hM : (D - Z * B) * A * ((D - Z * B).map σ)ᵀ = Z * B * Zσ := by
    rw [hlσ, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have e1 : D * A * (B * Zσ) = D * Zσ := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hAB, Matrix.one_mul]
    have e2 : Z * B * A * Dᵀ = Z * Dᵀ := by rw [Matrix.mul_assoc Z, hBA, Matrix.mul_one]
    have e3 : Z * B * A * (B * Zσ) = Z * B * Zσ := by
      calc Z * B * A * (B * Zσ) = Z * (B * A) * (B * Zσ) := by rw [Matrix.mul_assoc Z B A]
        _ = Z * (B * Zσ) := by rw [hBA, Matrix.mul_one]
        _ = Z * B * Zσ := (Matrix.mul_assoc _ _ _).symm
    have e4 : D * A * Dᵀ = G := by rw [hGdef, hDσ]
    rw [e1, e2, e3, e4, hsplit]; abel
  intro i j
  rw [hM]
  exact matMul_int (matMul_int hZi hB) hZσi i j

end GlobalTheory.Hk3.SquareDiag
