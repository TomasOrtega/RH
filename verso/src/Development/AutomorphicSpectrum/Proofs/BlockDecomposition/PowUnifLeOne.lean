import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialOfConjTorus

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial (stdBlocks_ones)

namespace GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `: i = j`. Apply `Fin.ext` to reduce the goal to its premises. Establish `h1` using `i.2`. Establish `h2` using `j.2`. Simplify using `only [ones] at h1 h2`.

Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality. Conclude with `Matrix.one_apply_eq i`.
-/
theorem one_block {N : ℕ} {a : Fin N} (i j : Fin (ones N a)) :
    (1 : Matrix (Fin (ones N a)) (Fin (ones N a)) k) i j = 1 := by
  have : i = j := by
    apply Fin.ext
    have h1 := i.2
    have h2 := j.2
    simp only [ones] at h1 h2
    omega
  subst this
  exact Matrix.one_apply_eq i

/- English proof (translation)
Use `mem_unipRad.2 ⟨mem_parab_iff.2 ?_, ?_⟩` and prove the remaining obligations. Introduce `a b i j hab`. Rewrite using `[stdBlocks_ones, stdBlocks_ones]`. Conclude with `h0 a b hab`. Introduce `a i j`.

Rewrite using `[stdBlocks_ones, stdBlocks_ones, h1, one_block]`.
-/
theorem mem_Nup_of {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ Nup k N := by
  refine mem_unipRad.2 ⟨mem_parab_iff.2 ?_, ?_⟩
  · intro a b i j hab
    rw [stdBlocks_ones, stdBlocks_ones]
    exact h0 a b hab
  · intro a i j
    rw [stdBlocks_ones, stdBlocks_ones, h1, one_block]

/- English proof (translation)
Use `(mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 ?_, ?_⟩` and prove the remaining obligations. Introduce `a b i j hab`. Rewrite using `[stdBlocks_ones, stdBlocks_ones]`. Conclude with `h0 a b hab`. Introduce `a i j`.

Rewrite using `[stdBlocks_ones, stdBlocks_ones, h1, one_block]`.
-/
theorem mem_Nlo_of {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, i < j → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ Nlo k N := by
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 ?_, ?_⟩
  · intro a b i j hab
    rw [stdBlocks_ones, stdBlocks_ones]
    exact h0 a b hab
  · intro a i j
    rw [stdBlocks_ones, stdBlocks_ones, h1, one_block]

def Uni {N : ℕ} (R : Fin N → Fin N → Prop) (m : ℕ) (A : Matrix (Fin N) (Fin N) k) : Prop :=
  (∀ i j, R i j → A i j = 0) ∧ (∀ i, A i i = 1) ∧
    ∀ i j, i ≠ j → valuation k (A i j) ≤ uniformizer k ^ m

/- English proof (translation)
The claim follows from `pow_le_one' (uniformizer_lt_one (R := k)).le m`.
-/
theorem pow_unif_le_one (m : ℕ) : uniformizer k ^ m ≤ 1 :=
  pow_le_one' (uniformizer_lt_one (R := k)).le m

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i => Matrix.one_apply_eq i, fun i j h => ?_⟩` and prove the remaining obligations. Conclude with `Matrix.one_apply_ne fun e => hR j (e ▸ h)`. Rewrite using `[Matrix.one_apply_ne h, map_zero]`. Conclude with `zero_le'`.
-/
theorem uni_one {N : ℕ} {R : Fin N → Fin N → Prop} (hR : ∀ i, ¬ R i i) (m : ℕ) :
    Uni R m (1 : Matrix (Fin N) (Fin N) k) := by
  refine ⟨fun i j h => ?_, fun i => Matrix.one_apply_eq i, fun i j h => ?_⟩
  · exact Matrix.one_apply_ne fun e => hR j (e ▸ h)
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le'

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i => ?_, fun i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Break down `hR i j l h with h | h` into its components or cases. Rewrite using `[hA.1 _ _ h, zero_mul]`.

Rewrite using `[hB.1 _ _ h, mul_zero]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[hA.2.1, hB.2.1, one_mul]`. Introduce `l _ hl`. Break down `hT i l hl.symm with h | h` into its components or cases.

Rewrite using `[hA.1 _ _ h, zero_mul]`. Rewrite using `[hB.1 _ _ h, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hli : l = i`. Substitute `hli` using the available equality. Rewrite using `[hA.2.1, one_mul]`. Conclude with `hB.2.2 _ _ h`. Distinguish the cases in `hlj : l = j`.

Substitute `hlj` using the available equality. Rewrite using `[hB.2.1, mul_one]`. Conclude with `hA.2.2 _ _ h`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uni_mul {N : ℕ} {R : Fin N → Fin N → Prop} (hR : ∀ i j l, R i j → R i l ∨ R l j)
    (hT : ∀ i l, i ≠ l → R i l ∨ R l i) {m : ℕ} {A B : Matrix (Fin N) (Fin N) k}
    (hA : Uni R m A) (hB : Uni R m B) : Uni R m (A * B) := by
  refine ⟨fun i j h => ?_, fun i => ?_, fun i j h => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases hR i j l h with h | h
    · rw [hA.1 _ _ h, zero_mul]
    · rw [hB.1 _ _ h, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2.1, hB.2.1, one_mul]
    · intro l _ hl
      rcases hT i l hl.symm with h | h
      · rw [hA.1 _ _ h, zero_mul]
      · rw [hB.1 _ _ h, mul_zero]
    · simp
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    by_cases hli : l = i
    · subst hli
      rw [hA.2.1, one_mul]
      exact hB.2.2 _ _ h
    by_cases hlj : l = j
    · subst hlj
      rw [hB.2.1, mul_one]
      exact hA.2.2 _ _ h
    rw [map_mul]
    calc valuation k (A i l) * valuation k (B l j) ≤ uniformizer k ^ m * 1 :=
          mul_le_mul' (hA.2.2 _ _ (Ne.symm hli)) ((hB.2.2 _ _ hlj).trans (pow_unif_le_one m))
      _ = uniformizer k ^ m := mul_one _

def Red {N : ℕ} (K : Fin N → Subgroup kˣ) (m r : ℕ) (H : Matrix (Fin N) (Fin N) k) : Prop :=
  (∀ i, ∃ x ∈ K i, H i i = x) ∧ (∀ i j, i ≠ j → valuation k (H i j) ≤ uniformizer k ^ m) ∧
    ∀ i j : Fin N, i ≠ j → ((i : ℕ) < r ∨ (j : ℕ) < r) → H i j = 0

/- English proof (translation)
Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]`. Simplify using the standard rewrite rules.
-/
theorem add_col_mul {N : ℕ} (p : Fin N) (c : Fin N → k) (A : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    ((1 + Matrix.of fun i j => if j = p then c i else 0) * A) i j = A i j + c i * A p j := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
  simp

/- English proof (translation)
Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]`. Simplify using the standard rewrite rules.
-/
theorem mul_add_row {N : ℕ} (p : Fin N) (w : Fin N → k) (A : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    (A * (1 + Matrix.of fun i j => if i = p then w j else 0)) i j = A i j + A i p * w j := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  simp

/- English proof (translation)
Take `⟨hm, -, hv, hc⟩` from `hK`. Establish `hx1` using `hv i x hx`. Establish `hx0 : (x : k) ≠ 0` using `x.ne_zero`. Establish `hlt : uniformizer k ^ (2 * m) < 1` using `pow_lt_one₀ zero_le' uniformizer_lt_one (by omega)`. Establish `hy0 : (1 - t / x : k) ≠ 0`.

Introduce `h0`. Establish `h2 : t / (x : k) = 1` using `(sub_eq_zero.1 h0).symm`. Establish `h1 : valuation k t = 1`. Establish `h3` using `congrArg (valuation k) h2`. Rewrite `h3` using `[map_div₀, hx1, div_one, map_one]`. Then use the resulting hypothesis.

Rewrite `ht` using `[h1]`. Conclude with `absurd ht (not_le.2 hlt)`. Use `⟨x * Units.mk0 _ hy0, mul_mem hx (hc i _ ?_), ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_mk0]`. Rewrite using `[show (1 - t / (x : k) - 1) = -(t / x) by ring, Valuation.map_neg, map_div₀, hx1, div_one]`.

Conclude with `ht`. Simplify using `only [Units.val_mul, Units.val_mk0]`. Clear the denominators using the available nonvanishing facts.
-/
theorem diag_step {N m : ℕ} {K : Fin N → Subgroup kˣ} (hK : KHyp k N m K) (i : Fin N) {x : kˣ}
    (hx : x ∈ K i) {t : k} (ht : valuation k t ≤ uniformizer k ^ (2 * m)) :
    ∃ z ∈ K i, (x : k) - t = z := by
  obtain ⟨hm, -, hv, hc⟩ := hK
  have hx1 := hv i x hx
  have hx0 : (x : k) ≠ 0 := x.ne_zero
  have hlt : uniformizer k ^ (2 * m) < 1 :=
    pow_lt_one₀ zero_le' uniformizer_lt_one (by omega)
  have hy0 : (1 - t / x : k) ≠ 0 := by
    intro h0
    have h2 : t / (x : k) = 1 := (sub_eq_zero.1 h0).symm
    have h1 : valuation k t = 1 := by
      have h3 := congrArg (valuation k) h2
      rwa [map_div₀, hx1, div_one, map_one] at h3
    rw [h1] at ht
    exact absurd ht (not_le.2 hlt)
  refine ⟨x * Units.mk0 _ hy0, mul_mem hx (hc i _ ?_), ?_⟩
  · simp only [Units.val_mk0]
    rw [show (1 - t / (x : k) - 1) = -(t / x) by ring, Valuation.map_neg, map_div₀, hx1, div_one]
    exact ht
  · simp only [Units.val_mul, Units.val_mk0]
    field_simp

/- English proof (translation)
Take `⟨x0, hx0, hd⟩` from `hQ.1 p`. Establish `hv : valuation k (H p p) = 1`. Rewrite using `[hd]`. Conclude with `hK.2.2.1 p x0 hx0`. Establish `hd0 : H p p ≠ 0`.

Rewrite using `[hd]`. Conclude with `x0.ne_zero`. Take `⟨c, hc⟩ : ∃ c : Fin N → k, c = fun i => if p < i then H i p / H p p else 0` from `⟨_, rfl⟩`. Take `⟨w, hw⟩ : ∃ w : Fin N → k, w = fun j => if p < j then H p j / H p p else 0` from `⟨_, rfl⟩`. Establish `hc0 : ∀ i, ¬ p < i → c i = 0` using `fun i h => by simp [hc, h]`.

Establish `hw0 : ∀ i, ¬ p < i → w i = 0` using `fun i h => by simp [hw, h]`. Establish `hcp : c p = 0` using `hc0 p (lt_irrefl p)`. Establish `hwp : w p = 0` using `hw0 p (lt_irrefl p)`. Establish `hcv : ∀ i, valuation k (c i) ≤ uniformizer k ^ m`. Introduce `i`.

Distinguish the cases in `h : p < i`. Simplify using `only [hc, if_pos h]`. Rewrite using `[map_div₀, hv, div_one]`. Conclude with `hQ.2.1 _ _ h.ne'`. Rewrite using `[hc0 i h, map_zero]`.

Conclude with `zero_le'`. Establish `hwv : ∀ i, valuation k (w i) ≤ uniformizer k ^ m`. Introduce `i`. Distinguish the cases in `h : p < i`. Simplify using `only [hw, if_pos h]`.

Rewrite using `[map_div₀, hv, div_one]`. Conclude with `hQ.2.1 _ _ h.ne`. Rewrite using `[hw0 i h, map_zero]`. Conclude with `zero_le'`. Establish `hcH : ∀ i, i ≠ p → H i p = c i * H p p`.

Introduce `i hi`. Distinguish the cases in `h : p < i`. Simplify using `only [hc, if_pos h]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hc0 i h, zero_mul]`.

Conclude with `hQ.2.2 i p hi (Or.inl (Fin.lt_def.1 (lt_of_le_of_ne (not_lt.1 h) hi)))`. Establish `hwH : ∀ j, j ≠ p → H p j = H p p * w j`. Introduce `j hj`. Distinguish the cases in `h : p < j`. Simplify using `only [hw, if_pos h]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hw0 j h, mul_zero]`. Conclude with `hQ.2.2 p j hj.symm (Or.inr (Fin.lt_def.1 (lt_of_le_of_ne (not_lt.1 h) hj)))`. Establish `htv : ∀ i j, valuation k (c i * H p p * w j) ≤ uniformizer k ^ (2 * m)`. Introduce `i j`.

Rewrite using `[map_mul, map_mul, hv, mul_one, two_mul, pow_add]`. Conclude with `mul_le_mul' (hcv i) (hwv j)`. Establish `hle : uniformizer k ^ (2 * m) ≤ uniformizer k ^ m`. Rewrite using `[two_mul, pow_add]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨H', hH'⟩ : ∃ H' : Matrix (Fin N) (Fin N) k, H' = Matrix.of fun i j => if i = p then (if j = p then H p p else 0) else if j = p then 0 else H i j - c i * H p p * w j` from `⟨_, rfl⟩`. Establish `h1 : H' p p = H p p` using `by simp [hH']`. Establish `h2 : ∀ j, j ≠ p → H' p j = 0` using `fun j hj => by simp [hH', hj]`. Establish `h3 : ∀ i, i ≠ p → H' i p = 0` using `fun i hi => by simp [hH', hi]`. Establish `h4 : ∀ i j, i ≠ p → j ≠ p → H' i j = H i j - c i * H p p * w j` using `fun i j hi hj => by simp [hH', hi, hj]`.

Use `⟨1 + Matrix.of fun i j => if j = p then c i else 0, H', 1 + Matrix.of fun i j => if i = p then w j else 0, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hij.ne, Matrix.of_apply, zero_add]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `hc0 i (fun h' => lt_irrefl _ (h'.trans hij))`. Both sides reduce to the same expression. Introduce `i`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]`. Use `split_ifs with h`.

Rewrite using `[h, hcp, add_zero]`. Rewrite using `[add_zero]`. Introduce `i j hij`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.of_apply, zero_add]`. Use `split_ifs with h`.

Conclude with `hcv i`. Rewrite using `[map_zero]`. Conclude with `zero_le'`. Introduce `i j hij`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hij.ne', Matrix.of_apply, zero_add]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hw0 j (fun h' => lt_irrefl _ (h'.trans hij))`. Both sides reduce to the same expression. Introduce `i`.

Rewrite using `[Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]`. Use `split_ifs with h`. Rewrite using `[h, hwp, add_zero]`. Rewrite using `[add_zero]`. Introduce `i j hij`.

Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.of_apply, zero_add]`. Use `split_ifs with h`. Conclude with `hwv j`. Rewrite using `[map_zero]`. Conclude with `zero_le'`.

Introduce `i`. Distinguish the cases in `hi : i = p`. Substitute `hi` using the available equality. Rewrite using `[h1]`. Conclude with `hQ.1 i`.

Take `⟨x, hx, hxe⟩` from `hQ.1 i`. Rewrite using `[h4 i i hi hi, hxe]`. Conclude with `diag_step hK i hx (htv i i)`. Introduce `i j hij`. Distinguish the cases in `hi : i = p`.

Substitute `hi` using the available equality. Rewrite using `[h2 j hij.symm, map_zero]`. Conclude with `zero_le'`. Distinguish the cases in `hj : j = p`. Substitute `hj` using the available equality.

Rewrite using `[h3 i hi, map_zero]`. Conclude with `zero_le'`. Rewrite using `[h4 i j hi hj]`. Conclude with `Valuation.map_sub_le _ (hQ.2.1 i j hij) ((htv i j).trans hle)`. Introduce `i j hij hr`.

Distinguish the cases in `hi : i = p`. Substitute `hi` using the available equality. Establish `hj : j ≠ i` using `hij.symm`. Conclude with `h2 j hj`. Distinguish the cases in `hj : j = p`.

Substitute `hj` using the available equality. Conclude with `h3 i hi`. Establish `hip : (i : ℕ) ≠ p` using `fun e => hi (Fin.ext e)`. Establish `hjp : (j : ℕ) ≠ p` using `fun e => hj (Fin.ext e)`. Rewrite using `[h4 i j hi hj]`.

Break down `hr with hr | hr` into its components or cases. Establish `hr' : (i : ℕ) < p` using `by omega`. Rewrite using `[hQ.2.2 i j hij (Or.inl hr'), hc0 i (fun h => by have := Fin.lt_def.1 h; omega)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr' : (j : ℕ) < p` using `by omega`.

Rewrite using `[hQ.2.2 i j hij (Or.inr hr'), hw0 j (fun h => by have := Fin.lt_def.1 h; omega)]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `i j`. Rewrite using `[mul_add_row, add_col_mul, add_col_mul]`. Distinguish the cases in `hi : i = p`.

Substitute `hi` using the available equality. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[h1, hcp, hwp]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2 j hj, h1, hcp, hwH j hj]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hj : j = p`. Substitute `hj` using the available equality. Rewrite using `[h3 i hi, h1, hwp, hcH i hi]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4 i j hi hj, h2 j hj, h3 i hi, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem step {N m : ℕ} {K : Fin N → Subgroup kˣ} (hK : KHyp k N m K) {H : Matrix (Fin N) (Fin N) k}
    (p : Fin N) (hQ : Red K m p H) :
    ∃ L H' U : Matrix (Fin N) (Fin N) k, Uni (fun i j => i < j) m L ∧ Uni (fun i j => j < i) m U ∧
      Red K m (p + 1) H' ∧ H = L * H' * U := by
  obtain ⟨x0, hx0, hd⟩ := hQ.1 p
  have hv : valuation k (H p p) = 1 := by
    rw [hd]
    exact hK.2.2.1 p x0 hx0
  have hd0 : H p p ≠ 0 := by
    rw [hd]
    exact x0.ne_zero
  obtain ⟨c, hc⟩ : ∃ c : Fin N → k, c = fun i => if p < i then H i p / H p p else 0 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin N → k, w = fun j => if p < j then H p j / H p p else 0 := ⟨_, rfl⟩
  have hc0 : ∀ i, ¬ p < i → c i = 0 := fun i h => by simp [hc, h]
  have hw0 : ∀ i, ¬ p < i → w i = 0 := fun i h => by simp [hw, h]
  have hcp : c p = 0 := hc0 p (lt_irrefl p)
  have hwp : w p = 0 := hw0 p (lt_irrefl p)
  have hcv : ∀ i, valuation k (c i) ≤ uniformizer k ^ m := by
    intro i
    by_cases h : p < i
    · simp only [hc, if_pos h]
      rw [map_div₀, hv, div_one]
      exact hQ.2.1 _ _ h.ne'
    · rw [hc0 i h, map_zero]
      exact zero_le'
  have hwv : ∀ i, valuation k (w i) ≤ uniformizer k ^ m := by
    intro i
    by_cases h : p < i
    · simp only [hw, if_pos h]
      rw [map_div₀, hv, div_one]
      exact hQ.2.1 _ _ h.ne
    · rw [hw0 i h, map_zero]
      exact zero_le'
  have hcH : ∀ i, i ≠ p → H i p = c i * H p p := by
    intro i hi
    by_cases h : p < i
    · simp only [hc, if_pos h]
      field_simp
    · rw [hc0 i h, zero_mul]
      exact hQ.2.2 i p hi (Or.inl (Fin.lt_def.1 (lt_of_le_of_ne (not_lt.1 h) hi)))
  have hwH : ∀ j, j ≠ p → H p j = H p p * w j := by
    intro j hj
    by_cases h : p < j
    · simp only [hw, if_pos h]
      field_simp
    · rw [hw0 j h, mul_zero]
      exact hQ.2.2 p j hj.symm (Or.inr (Fin.lt_def.1 (lt_of_le_of_ne (not_lt.1 h) hj)))
  have htv : ∀ i j, valuation k (c i * H p p * w j) ≤ uniformizer k ^ (2 * m) := by
    intro i j
    rw [map_mul, map_mul, hv, mul_one, two_mul, pow_add]
    exact mul_le_mul' (hcv i) (hwv j)
  have hle : uniformizer k ^ (2 * m) ≤ uniformizer k ^ m := by
    rw [two_mul, pow_add]
    calc uniformizer k ^ m * uniformizer k ^ m ≤ uniformizer k ^ m * 1 :=
          mul_le_mul' le_rfl (pow_unif_le_one m)
      _ = uniformizer k ^ m := mul_one _
  obtain ⟨H', hH'⟩ : ∃ H' : Matrix (Fin N) (Fin N) k, H' = Matrix.of fun i j =>
      if i = p then (if j = p then H p p else 0) else
        if j = p then 0 else H i j - c i * H p p * w j := ⟨_, rfl⟩
  have h1 : H' p p = H p p := by simp [hH']
  have h2 : ∀ j, j ≠ p → H' p j = 0 := fun j hj => by simp [hH', hj]
  have h3 : ∀ i, i ≠ p → H' i p = 0 := fun i hi => by simp [hH', hi]
  have h4 : ∀ i j, i ≠ p → j ≠ p → H' i j = H i j - c i * H p p * w j :=
    fun i j hi hj => by simp [hH', hi, hj]
  refine ⟨1 + Matrix.of fun i j => if j = p then c i else 0, H',
    1 + Matrix.of fun i j => if i = p then w j else 0, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne hij.ne, Matrix.of_apply, zero_add]
    split_ifs with h
    · subst h
      exact hc0 i (fun h' => lt_irrefl _ (h'.trans hij))
    · rfl
  · intro i
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    split_ifs with h
    · rw [h, hcp, add_zero]
    · rw [add_zero]
  · intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.of_apply, zero_add]
    split_ifs with h
    · exact hcv i
    · rw [map_zero]
      exact zero_le'
  · intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne hij.ne', Matrix.of_apply, zero_add]
    split_ifs with h
    · subst h
      exact hw0 j (fun h' => lt_irrefl _ (h'.trans hij))
    · rfl
  · intro i
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    split_ifs with h
    · rw [h, hwp, add_zero]
    · rw [add_zero]
  · intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.of_apply, zero_add]
    split_ifs with h
    · exact hwv j
    · rw [map_zero]
      exact zero_le'
  · intro i
    by_cases hi : i = p
    · subst hi
      rw [h1]
      exact hQ.1 i
    · obtain ⟨x, hx, hxe⟩ := hQ.1 i
      rw [h4 i i hi hi, hxe]
      exact diag_step hK i hx (htv i i)
  · intro i j hij
    by_cases hi : i = p
    · subst hi
      rw [h2 j hij.symm, map_zero]
      exact zero_le'
    by_cases hj : j = p
    · subst hj
      rw [h3 i hi, map_zero]
      exact zero_le'
    rw [h4 i j hi hj]
    exact Valuation.map_sub_le _ (hQ.2.1 i j hij) ((htv i j).trans hle)
  · intro i j hij hr
    by_cases hi : i = p
    · subst hi
      have hj : j ≠ i := hij.symm
      exact h2 j hj
    by_cases hj : j = p
    · subst hj
      exact h3 i hi
    have hip : (i : ℕ) ≠ p := fun e => hi (Fin.ext e)
    have hjp : (j : ℕ) ≠ p := fun e => hj (Fin.ext e)
    rw [h4 i j hi hj]
    rcases hr with hr | hr
    · have hr' : (i : ℕ) < p := by omega
      rw [hQ.2.2 i j hij (Or.inl hr'), hc0 i (fun h => by have := Fin.lt_def.1 h; omega)]
      ring
    · have hr' : (j : ℕ) < p := by omega
      rw [hQ.2.2 i j hij (Or.inr hr'), hw0 j (fun h => by have := Fin.lt_def.1 h; omega)]
      ring
  · ext i j
    rw [mul_add_row, add_col_mul, add_col_mul]
    by_cases hi : i = p
    · subst hi
      by_cases hj : j = i
      · subst hj
        rw [h1, hcp, hwp]
        ring
      · rw [h2 j hj, h1, hcp, hwH j hj]
        ring
    · by_cases hj : j = p
      · subst hj
        rw [h3 i hi, h1, hwp, hcH i hi]
        ring
      · rw [h4 i j hi hj, h2 j hj, h3 i hi, h1]
        ring

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Conclude with `⟨1, g, 1, uni_one (fun i => lt_irrefl i) m, uni_one (R := fun i j => j < i) (fun i => lt_irrefl i) m, hg, by simp⟩`. Consider the case `succ r ih`. Take `⟨L, H, U, hL, hU, hH, e⟩` from `ih (by omega)`.

Take `⟨L', H', U', hL', hU', hH', e'⟩` from `step hK (H := H) ⟨r, by omega⟩ hH`. Use `⟨L * L', H', U' * U, uni_mul ?_ ?_ hL hL', uni_mul ?_ ?_ hU' hU, hH', ?_⟩` and prove the remaining obligations. Introduce `i j l h`. Conclude with `(lt_or_ge i l).imp id fun h' => lt_of_le_of_lt h' h`. Introduce `i l h`.

Conclude with `lt_or_gt_of_ne h`. Introduce `i j l h`. Conclude with `(lt_or_ge l i).imp id fun h' => lt_of_lt_of_le h h'`. Introduce `i l h`. Conclude with `(lt_or_gt_of_ne h).symm`.

Rewrite using `[e, e']`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem elim {N m : ℕ} {K : Fin N → Subgroup kˣ} (hK : KHyp k N m K) {g : Matrix (Fin N) (Fin N) k}
    (hg : Red K m 0 g) (r : ℕ) (hr : r ≤ N) :
    ∃ L H U : Matrix (Fin N) (Fin N) k, Uni (fun i j => i < j) m L ∧ Uni (fun i j => j < i) m U ∧
      Red K m r H ∧ g = L * H * U := by
  induction r with
  | zero =>
    exact ⟨1, g, 1, uni_one (fun i => lt_irrefl i) m,
      uni_one (R := fun i j => j < i) (fun i => lt_irrefl i) m, hg, by simp⟩
  | succ r ih =>
    obtain ⟨L, H, U, hL, hU, hH, e⟩ := ih (by omega)
    obtain ⟨L', H', U', hL', hU', hH', e'⟩ := step hK (H := H) ⟨r, by omega⟩ hH
    refine ⟨L * L', H', U' * U, uni_mul ?_ ?_ hL hL', uni_mul ?_ ?_ hU' hU, hH', ?_⟩
    · intro i j l h
      exact (lt_or_ge i l).imp id fun h' => lt_of_le_of_lt h' h
    · intro i l h
      exact lt_or_gt_of_ne h
    · intro i j l h
      exact (lt_or_ge l i).imp id fun h' => lt_of_lt_of_le h h'
    · intro i l h
      exact (lt_or_gt_of_ne h).symm
    · rw [e, e']
      simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `k _ _ _ _ N m K hK g hg`. Take `⟨L, H, U, hL, hU, hH, e⟩` from `elim hK (g := (g : Matrix (Fin N) (Fin N) k)) ⟨hg.1, hg.2, fun i j _ h => by omega⟩ N le_rfl`. Establish `dL : L.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular L (fun i j h => hL.1 i j h)]`. Simplify using `[hL.2.1]`.

Establish `dU : U.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (M := U) (fun i j h => hU.1 i j h)]`. Simplify using `[hU.2.1]`. Establish `dH : IsUnit H.det`. Establish `h1 : IsUnit (g : Matrix (Fin N) (Fin N) k).det` using `(Matrix.isUnit_iff_isUnit_det _).1 g.isUnit`.

Rewrite `h1` using `[e, Matrix.det_mul, Matrix.det_mul, dL, dU, one_mul, mul_one]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `(Matrix.isUnit_iff_isUnit_det L).2 (by rw [dL]; exact isUnit_one)`. Take `⟨b, hb⟩` from `(Matrix.isUnit_iff_isUnit_det H).2 dH`. Take `⟨c, hc⟩` from `(Matrix.isUnit_iff_isUnit_det U).2 (by rw [dU]; exact isUnit_one)`. Use `⟨a, b, c, mem_Nlo_of a ?_ ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, mem_Nup_of c ?_ ?_, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `i j h`. Rewrite using `[ha]`. Conclude with `hL.1 i j h`. Introduce `i`. Rewrite using `[ha]`.

Conclude with `hL.2.1 i`. Introduce `i`. Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, hL.2.1, Units.val_one]`. Introduce `i j h`.

Rewrite using `[ha]`. Conclude with `hL.2.2 i j h`. Use `GlobalTheory.CompanionTheory.LbElem.ConjMonomial.mem_tor_of_offDiag b fun i j h => ?_` and prove the remaining obligations. Rewrite using `[hb]`. Conclude with `hH.2.2 i j h (Or.inl i.2)`.

Introduce `i`. Rewrite using `[hb]`. Conclude with `hH.1 i`. Introduce `i j h`. Rewrite using `[hb]`.

Conclude with `hH.2.1 i j h`. Introduce `i j h`. Rewrite using `[hc]`. Conclude with `hU.1 i j h`. Introduce `i`.

Rewrite using `[hc]`. Conclude with `hU.2.1 i`. Introduce `i`. Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, hU.2.1, Units.val_one]`.

Introduce `i j h`. Rewrite using `[hc]`. Conclude with `hU.2.2 i j h`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, ha, hb, hc]`.

Conclude with `e`.
-/
theorem jpred_ldu : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N m : ℕ) (K : Fin N → Subgroup kˣ), PositivityTheory.Lbc.KHyp k N m K → ∀ g : GL (Fin N) k, PositivityTheory.Lbc.JPred k N m K g → ∃ a b c : GL (Fin N) k, a ∈ PositivityTheory.Lbc.Nlo k N ∧ PositivityTheory.Lbc.JPred k N m K a ∧ b ∈ PositivityTheory.Lbc.Tor k N ∧ PositivityTheory.Lbc.JPred k N m K b ∧ c ∈ PositivityTheory.Lbc.Nup k N ∧ PositivityTheory.Lbc.JPred k N m K c ∧ g = a * b * c := by
  intro k _ _ _ _ N m K hK g hg
  obtain ⟨L, H, U, hL, hU, hH, e⟩ := elim hK (g := (g : Matrix (Fin N) (Fin N) k))
    ⟨hg.1, hg.2, fun i j _ h => by omega⟩ N le_rfl
  have dL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L (fun i j h => hL.1 i j h)]
    simp [hL.2.1]
  have dU : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := U) (fun i j h => hU.1 i j h)]
    simp [hU.2.1]
  have dH : IsUnit H.det := by
    have h1 : IsUnit (g : Matrix (Fin N) (Fin N) k).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    rwa [e, Matrix.det_mul, Matrix.det_mul, dL, dU, one_mul, mul_one] at h1
  obtain ⟨a, ha⟩ := (Matrix.isUnit_iff_isUnit_det L).2 (by rw [dL]; exact isUnit_one)
  obtain ⟨b, hb⟩ := (Matrix.isUnit_iff_isUnit_det H).2 dH
  obtain ⟨c, hc⟩ := (Matrix.isUnit_iff_isUnit_det U).2 (by rw [dU]; exact isUnit_one)
  refine ⟨a, b, c, mem_Nlo_of a ?_ ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, mem_Nup_of c ?_ ?_, ⟨?_, ?_⟩, ?_⟩
  · intro i j h
    rw [ha]
    exact hL.1 i j h
  · intro i
    rw [ha]
    exact hL.2.1 i
  · intro i
    refine ⟨1, one_mem _, ?_⟩
    rw [ha, hL.2.1, Units.val_one]
  · intro i j h
    rw [ha]
    exact hL.2.2 i j h
  · refine GlobalTheory.CompanionTheory.LbElem.ConjMonomial.mem_tor_of_offDiag b fun i j h => ?_
    rw [hb]
    exact hH.2.2 i j h (Or.inl i.2)
  · intro i
    rw [hb]
    exact hH.1 i
  · intro i j h
    rw [hb]
    exact hH.2.1 i j h
  · intro i j h
    rw [hc]
    exact hU.1 i j h
  · intro i
    rw [hc]
    exact hU.2.1 i
  · intro i
    refine ⟨1, one_mem _, ?_⟩
    rw [hc, hU.2.1, Units.val_one]
  · intro i j h
    rw [hc]
    exact hU.2.2 i j h
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, ha, hb, hc]
    exact e

end GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

end
