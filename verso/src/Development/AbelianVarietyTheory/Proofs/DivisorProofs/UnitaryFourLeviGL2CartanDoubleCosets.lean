import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Four

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def unitaryFourUpperLeftBlock (g : GU σ 4) : Matrix (Fin 2) (Fin 2) L := !![mat g 0 0, mat g 0 1; mat g 1 0, mat g 1 1]

/- English proof (translation)
Establish `h02` using `hg 0 2 (by decide)`. Establish `h03` using `hg 0 3 (by decide)`. Establish `h12` using `hg 1 2 (by decide)`. Establish `h13` using `hg 1 3 (by decide)`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[unitaryFourUpperLeftBlock, mat_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]`.
-/
theorem unitaryFourUpperLeftBlock_mul_of_mem_levi {g : GU σ 4} (g' : GU σ 4) (hg : g ∈ leviU σ ![0, 0, 1, 1]) :
    unitaryFourUpperLeftBlock (g * g') = unitaryFourUpperLeftBlock g * unitaryFourUpperLeftBlock g' := by
  have h02 := hg 0 2 (by decide)
  have h03 := hg 0 3 (by decide)
  have h12 := hg 1 2 (by decide)
  have h13 := hg 1 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFourUpperLeftBlock, mat_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [unitaryFourUpperLeftBlock, mat_one]`.
-/
theorem unitaryFourUpperLeftBlock_one : unitaryFourUpperLeftBlock (1 : GU σ 4) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryFourUpperLeftBlock, mat_one]

/- English proof (translation)
Establish `h1 : unitaryFourUpperLeftBlock g⁻¹ * unitaryFourUpperLeftBlock g' = 1`. Rewrite using `[← h, ← unitaryFourUpperLeftBlock_mul_of_mem_levi _ (inv_mem hg), inv_mul_cancel, unitaryFourUpperLeftBlock_one]`. Establish `h2 : unitaryFourUpperLeftBlock g' * unitaryFourUpperLeftBlock g'⁻¹ = 1`. Rewrite using `[← unitaryFourUpperLeftBlock_mul_of_mem_levi _ hg', mul_inv_cancel, unitaryFourUpperLeftBlock_one]`. Establish `h3 : unitaryFourUpperLeftBlock g⁻¹ = unitaryFourUpperLeftBlock g'⁻¹` using `left_inv_eq_right_inv h1 h2`.

Establish `low : ∀ i j : Fin 4, mat g⁻¹ j.rev i.rev = mat g'⁻¹ j.rev i.rev → mat g i j = mat g' i j`. Introduce `i j e`. Establish `e1` using `mat_inv_apply g⁻¹ i j`. Establish `e2` using `mat_inv_apply g'⁻¹ i j`. Rewrite `e1`, `e2` using `[inv_inv]`.

Rewrite using `[e1, e2, e]`. Establish `off : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ ![0, 0, 1, 1] j → mat g i j = mat g' i j` using `fun i j e => by rw [hg i j e, hg' i j e]`. Apply `mat_injective` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Conclude with `congrFun (congrFun h 0) 0`. Conclude with `congrFun (congrFun h 0) 1`. Conclude with `off _ _ (by decide)`. Conclude with `off _ _ (by decide)`. Conclude with `congrFun (congrFun h 1) 0`.

Conclude with `congrFun (congrFun h 1) 1`. Conclude with `off _ _ (by decide)`. Conclude with `off _ _ (by decide)`. Conclude with `off _ _ (by decide)`. Conclude with `off _ _ (by decide)`.

Conclude with `low _ _ (congrFun (congrFun h3 1) 1)`. Conclude with `low _ _ (congrFun (congrFun h3 0) 1)`. Conclude with `off _ _ (by decide)`. Conclude with `off _ _ (by decide)`. Conclude with `low _ _ (congrFun (congrFun h3 1) 0)`.

Conclude with `low _ _ (congrFun (congrFun h3 0) 0)`.
-/
theorem unitaryFourUpperLeftBlock_injective_on_levi {g g' : GU σ 4} (hg : g ∈ leviU σ ![0, 0, 1, 1]) (hg' : g' ∈ leviU σ ![0, 0, 1, 1])
    (h : unitaryFourUpperLeftBlock g = unitaryFourUpperLeftBlock g') : g = g' := by
  have h1 : unitaryFourUpperLeftBlock g⁻¹ * unitaryFourUpperLeftBlock g' = 1 := by
    rw [← h, ← unitaryFourUpperLeftBlock_mul_of_mem_levi _ (inv_mem hg), inv_mul_cancel, unitaryFourUpperLeftBlock_one]
  have h2 : unitaryFourUpperLeftBlock g' * unitaryFourUpperLeftBlock g'⁻¹ = 1 := by
    rw [← unitaryFourUpperLeftBlock_mul_of_mem_levi _ hg', mul_inv_cancel, unitaryFourUpperLeftBlock_one]
  have h3 : unitaryFourUpperLeftBlock g⁻¹ = unitaryFourUpperLeftBlock g'⁻¹ := left_inv_eq_right_inv h1 h2
  have low : ∀ i j : Fin 4, mat g⁻¹ j.rev i.rev = mat g'⁻¹ j.rev i.rev → mat g i j = mat g' i j := by
    intro i j e
    have e1 := mat_inv_apply g⁻¹ i j
    have e2 := mat_inv_apply g'⁻¹ i j
    rw [inv_inv] at e1 e2
    rw [e1, e2, e]
  have off : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ ![0, 0, 1, 1] j → mat g i j = mat g' i j :=
    fun i j e => by rw [hg i j e, hg' i j e]
  apply mat_injective
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact congrFun (congrFun h 1) 0
  · exact congrFun (congrFun h 1) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 1)
  · exact low _ _ (congrFun (congrFun h3 0) 1)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 0)
  · exact low _ _ (congrFun (congrFun h3 0) 0)

/- English proof (translation)
Establish `hd' : σ p * σ w - σ r * σ u = -1` using `by simpa using congrArg σ hd`. Establish `hs : ∀ x ∈ intL L, σ x ∈ intL L` using `fun x hx => by show Valued.v (σ x) ≤ 1`. Rewrite using `[h2]`. Conclude with `hx`. Take `⟨k, hk⟩` from `exists_mat (σ := σ) !![p, r, 0, 0; u, w, 0, 0; 0, 0, -σ p, σ r; 0, 0, σ u, -σ w] (by`.

Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [P.fSatake_cTJ]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, antiJ, h1, Fin.rev] <;> first | linear_combination hd | linear_combination -hd | linear_combination hd' | linear_combination -hd' | ring)`. Use `⟨k, ⟨(mem_KU_iff h2 k).2 fun i j => ?_, fun i j hij => ?_⟩, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rw [hk] fin_cases i <;> fin_cases j <;> simp [hp, hr, hu, hw, hs _ hp, hs _ hr, hs _ hu, hs _ hw]`. Apply the tactic sequence `rw [hk] fin_cases i <;> fin_cases j <;> simp at hij ⊢`. Simplify using `[unitaryFourUpperLeftBlock, hk]`.
-/
theorem exists_lift (h1 : ∀ x, σ (σ x) = x) (h2 : ∀ x, Valued.v (σ x) = Valued.v x) {p r u w : L}
    (hp : p ∈ intL L) (hr : r ∈ intL L) (hu : u ∈ intL L) (hw : w ∈ intL L) (hd : p * w - r * u = -1) :
    ∃ k ∈ KU σ 4 ⊓ leviU σ ![0, 0, 1, 1], unitaryFourUpperLeftBlock k = !![p, r; u, w] := by
  have hd' : σ p * σ w - σ r * σ u = -1 := by simpa using congrArg σ hd
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [h2]; exact hx
  obtain ⟨k, hk⟩ := exists_mat (σ := σ) !![p, r, 0, 0; u, w, 0, 0; 0, 0, -σ p, σ r; 0, 0, σ u, -σ w] (by
    ext i j
    rw [Matrix.mul_apply]
    simp only [P.fSatake_cTJ]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, antiJ, h1, Fin.rev] <;>
      first | linear_combination hd | linear_combination -hd | linear_combination hd' | linear_combination -hd' | ring)
  refine ⟨k, ⟨(mem_KU_iff h2 k).2 fun i j => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp [hp, hr, hu, hw, hs _ hp, hs _ hr, hs _ hu, hs _ hw]
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [unitaryFourUpperLeftBlock, hk]

/- English proof (translation)
Establish `mem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1` using `fun x => Iff.rfl`. Distinguish the cases in `h1 : ξ ∈ intL L`. Use `⟨-ξ, neg_mem h1, 1, one_mem _, 1, one_mem _, 0, zero_mem _, by ring, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring`.

Distinguish the cases in `h2 : A * ξ / D ∈ intL L`. Use `⟨0, zero_mem _, 1, one_mem _, 1, one_mem _, -(A * ξ / D), neg_mem h2, by ring, ?_⟩` and prove the remaining obligations. Take `⟨ζ, hζ⟩ : ∃ ζ, A * ξ = D * ζ` from `⟨A * ξ / D, by field_simp⟩`. Rewrite using `[hζ, mul_div_cancel_left₀ _ hD]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]`. Establish `hξ : ξ ≠ 0` using `fun e => h1 (e ▸ zero_mem _)`. Establish `inv : ∀ x : L, x ∉ intL L → x⁻¹ ∈ intL L` using `fun x hx => by`. Rewrite `hx`, the goal using `[mem]`. Rewrite using `[map_inv₀]`.

Conclude with `inv_le_one_of_one_le₀ (not_le.1 hx).le`. Use `⟨1, one_mem _, 0, zero_mem _, -(ξ⁻¹ - (A * ξ / D)⁻¹), neg_mem (sub_mem (inv _ h1) (inv _ h2)), -1, neg_mem (one_mem _), by ring, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring`.
-/
theorem exists_conj {A D ξ : L} (hA : A ≠ 0) (hD : D ≠ 0) :
    ∃ p ∈ intL L, ∃ r ∈ intL L, ∃ u ∈ intL L, ∃ w ∈ intL L, p * w - r * u = -1 ∧
      !![D, -(A * ξ); 0, A] = !![p, r; u, w] * !![A, A * ξ; 0, D] * !![p, r; u, w] := by
  have mem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  by_cases h1 : ξ ∈ intL L
  · refine ⟨-ξ, neg_mem h1, 1, one_mem _, 1, one_mem _, 0, zero_mem _, by ring, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  by_cases h2 : A * ξ / D ∈ intL L
  · refine ⟨0, zero_mem _, 1, one_mem _, 1, one_mem _, -(A * ξ / D), neg_mem h2, by ring, ?_⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ, A * ξ = D * ζ := ⟨A * ξ / D, by field_simp⟩
    rw [hζ, mul_div_cancel_left₀ _ hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have hξ : ξ ≠ 0 := fun e => h1 (e ▸ zero_mem _)
  have inv : ∀ x : L, x ∉ intL L → x⁻¹ ∈ intL L := fun x hx => by
    rw [mem] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (not_le.1 hx).le
  refine ⟨1, one_mem _, 0, zero_mem _, -(ξ⁻¹ - (A * ξ / D)⁻¹), neg_mem (sub_mem (inv _ h1) (inv _ h2)),
    -1, neg_mem (one_mem _), by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU x y s s' hs hs' a ha`. Take `⟨h1, h2, -, h4, -⟩` from `hU`. Establish `hϖ : ϖ ≠ 0` using `fun e => by rw [e, map_zero] at h4; exact WithZero.zero_ne_coe h4`. Establish `dl : ∀ (t : GU σ 4) (d : Fin 4 → L), mat t = Matrix.diagonal d → t ∈ leviU σ ![0, 0, 1, 1]` using `fun t d e i j hij => by rw [e]; exact Matrix.diagonal_apply_ne _ fun e => hij (e ▸ rfl)`. Establish `hsl` using `dl _ _ hs`.

Establish `hsl'` using `dl _ _ hs'`. Establish `us : unitaryFourUpperLeftBlock s = !![ϖ ^ x, 0; 0, ϖ ^ y]` using `by simp [unitaryFourUpperLeftBlock, hs]`. Establish `us' : unitaryFourUpperLeftBlock s' = !![ϖ ^ y, 0; 0, ϖ ^ x]` using `by simp [unitaryFourUpperLeftBlock, hs']`. Establish `ua : unitaryFourUpperLeftBlock a = !![1, mat a 0 1; 0, 1]`. Simplify using `[unitaryFourUpperLeftBlock, ha.1 0 0 (by decide), ha.1 1 0 (by decide), ha.1 1 1 (by decide)]`.

Take `⟨p, hp, r, hr, u, hu, w, hw, hd, e⟩` from `exists_conj (ξ := mat a 0 1) (zpow_ne_zero x hϖ) (zpow_ne_zero y hϖ)`. Take `⟨k, hk, uk⟩` from `exists_lift h1 h2 hp hr hu hw hd`. Use `⟨k, hk.1, k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_mul_eq_iff_eq_mul]`. Use `unitaryFourUpperLeftBlock_injective_on_levi hsl' (mul_mem ha.2 (mul_mem (mul_mem hk.2 (mul_mem hsl ha.2)) hk.2)) ?_` and prove the remaining obligations.

Establish `usa : unitaryFourUpperLeftBlock (s * a) = !![ϖ ^ x, ϖ ^ x * mat a 0 1; 0, ϖ ^ y]`. Rewrite using `[unitaryFourUpperLeftBlock_mul_of_mem_levi _ hsl, us, ua]`. Simplify using the standard rewrite rules. Rewrite using `[unitaryFourUpperLeftBlock_mul_of_mem_levi _ ha.2, unitaryFourUpperLeftBlock_mul_of_mem_levi _ (mul_mem hk.2 (mul_mem hsl ha.2)), unitaryFourUpperLeftBlock_mul_of_mem_levi _ hk.2, usa, uk, ← e, us', ua]`. Simplify using `[mul_comm]`.
-/
theorem cartanFour : GlobalTheory.SatakeWeyl.CartanFour := by
  intro L _ _ ϖ σ q hU x y s s' hs hs' a ha
  obtain ⟨h1, h2, -, h4, -⟩ := hU
  have hϖ : ϖ ≠ 0 := fun e => by rw [e, map_zero] at h4; exact WithZero.zero_ne_coe h4
  have dl : ∀ (t : GU σ 4) (d : Fin 4 → L), mat t = Matrix.diagonal d → t ∈ leviU σ ![0, 0, 1, 1] :=
    fun t d e i j hij => by rw [e]; exact Matrix.diagonal_apply_ne _ fun e => hij (e ▸ rfl)
  have hsl := dl _ _ hs
  have hsl' := dl _ _ hs'
  have us : unitaryFourUpperLeftBlock s = !![ϖ ^ x, 0; 0, ϖ ^ y] := by simp [unitaryFourUpperLeftBlock, hs]
  have us' : unitaryFourUpperLeftBlock s' = !![ϖ ^ y, 0; 0, ϖ ^ x] := by simp [unitaryFourUpperLeftBlock, hs']
  have ua : unitaryFourUpperLeftBlock a = !![1, mat a 0 1; 0, 1] := by
    simp [unitaryFourUpperLeftBlock, ha.1 0 0 (by decide), ha.1 1 0 (by decide), ha.1 1 1 (by decide)]
  obtain ⟨p, hp, r, hr, u, hu, w, hw, hd, e⟩ :=
    exists_conj (ξ := mat a 0 1) (zpow_ne_zero x hϖ) (zpow_ne_zero y hϖ)
  obtain ⟨k, hk, uk⟩ := exists_lift h1 h2 hp hr hu hw hd
  refine ⟨k, hk.1, k, hk, ?_⟩
  rw [inv_mul_eq_iff_eq_mul]
  refine unitaryFourUpperLeftBlock_injective_on_levi hsl' (mul_mem ha.2 (mul_mem (mul_mem hk.2 (mul_mem hsl ha.2)) hk.2)) ?_
  have usa : unitaryFourUpperLeftBlock (s * a) = !![ϖ ^ x, ϖ ^ x * mat a 0 1; 0, ϖ ^ y] := by
    rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ hsl, us, ua]; simp
  rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ ha.2, unitaryFourUpperLeftBlock_mul_of_mem_levi _ (mul_mem hk.2 (mul_mem hsl ha.2)), unitaryFourUpperLeftBlock_mul_of_mem_levi _ hk.2, usa, uk, ← e, us', ua]
  simp [mul_comm]

end GlobalTheory.SatakeWeyl.Four

end
