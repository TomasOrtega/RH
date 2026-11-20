import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, w j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Conclude with `hw (funext fun i => by_contra fun hi => h ⟨i, hi⟩)`. Take `⟨k, -, hk⟩` from `Finset.exists_max_image Finset.univ (fun i => W.valuation (w i)) ⟨j, Finset.mem_univ j⟩`. Establish `hwk : w k ≠ 0`.

Introduce `h0`. Establish `hle` using `hk j (Finset.mem_univ j)`. Rewrite `hle` using `[h0, map_zero]`. Conclude with `hj ((Valuation.zero_iff _).1 (le_antisymm hle zero_le))`. Use `⟨k, hwk, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[← W.valuation_le_one_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ (hk i (Finset.mem_univ i)) zero_le`.
-/
theorem exists_pivot_entry {L : Type} [Field L] (W : ValuationSubring L) {n : ℕ}
    (w : Fin n → L) (hw : w ≠ 0) : ∃ k, w k ≠ 0 ∧ ∀ i, w i / w k ∈ W := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    exact hw (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun i => W.valuation (w i)) ⟨j, Finset.mem_univ j⟩
  have hwk : w k ≠ 0 := by
    intro h0
    have hle := hk j (Finset.mem_univ j)
    rw [h0, map_zero] at hle
    exact hj ((Valuation.zero_iff _).1 (le_antisymm hle zero_le))
  refine ⟨k, hwk, fun i => ?_⟩
  rw [← W.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hk i (Finset.mem_univ i)) zero_le

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `g _`. Use `⟨⟨Fin.elim0, fun a => Fin.elim0 a⟩, 0, 0, fun _ j => Fin.elim0 j, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩` and prove the remaining obligations.

Use extensionality with `_ j`. Conclude with `Fin.elim0 j`. Consider the case `succ r ih`. Introduce `g hg`. Set `cols' : Fin r → Fin n → L` to `fun i a => g a i.castSucc`.

Set `g' : Matrix (Fin n) (Fin r) L` to `Matrix.of fun a i => cols' i a`. Set `x : Fin n → L` to `fun a => g a (Fin.last r)`. Establish `hsplit : (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) = fun i a => g a i`. Use function extensionality and compare the values at `i a`. Consider the cases of `i using Fin.lastCases with`.

Consider the case `last => simp [x]`. Consider the case `cast i => simp [cols']`. Establish `hg2 : LinearIndependent L (Fin.snoc cols' x : Fin (r + 1) → Fin n → L)`. Rewrite using `[hsplit]`. Conclude with `hg`.

Rewrite `hg2` using `[linearIndependent_finSnoc]`. Take `⟨hg'ind, hxspan⟩` from `hg2`. Take `⟨ι', u', b', hu'W, hu'zero, hu'one, hb'tri, hb'diag, hgub⟩` from `ih g' hg'ind`. Establish `hb'det : IsUnit b'.det`. Rewrite using `[Matrix.det_of_isUpperTriangular hb'tri]`.

Conclude with `(Finset.prod_ne_zero_iff.2 fun i _ => hb'diag i).isUnit`. Set `M : Matrix (Fin r) (Fin r) L` to `Matrix.of fun l i => u' (ι' l) i`. Establish `hMtri : M.BlockTriangular OrderDual.toDual`. Introduce `l i hli`. Simplify `hu'zero l i (OrderDual.toDual_lt_toDual.1 hli)` using `[M]`.

Establish `hMdet : IsUnit M.det`. Rewrite using `[Matrix.det_of_isLowerTriangular M hMtri]`. Simplify using `[M, hu'one]`. Set `c : Fin r → L` to `M⁻¹ *ᵥ (fun l => x (ι' l))`. Set `v : Fin n → L` to `x - u' *ᵥ c`.

Establish `hvpiv : ∀ l, v (ι' l) = 0`. Introduce `l`. Establish `h1 : (u' *ᵥ c) (ι' l) = (M *ᵥ c) l` using `rfl`. Establish `h2 : M *ᵥ c = fun l => x (ι' l)`. Simplify using `only [c]`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMdet, Matrix.one_mulVec]`. Use `show x (ι' l) - (u' *ᵥ c) (ι' l) = 0`. Rewrite using `[h1, h2, sub_self]`. Establish `hv0 : v ≠ 0`. Introduce `h0`.

Apply `hxspan` to reduce the goal to its premises. Establish `hxv : x - u' *ᵥ c = 0` using `h0`. Establish `hu' : u' = g' * b'⁻¹`. Rewrite using `[hgub]`. Conclude with `(Matrix.mul_nonsing_inv_cancel_right (B := u') (h := hb'det)).symm`.

Establish `hxe : x = g' *ᵥ (b'⁻¹ *ᵥ c)`. Rewrite using `[Matrix.mulVec_mulVec, ← hu']`. Conclude with `sub_eq_zero.1 hxv`. Establish `hmem` using `LinearMap.mem_range_self g'.mulVecLin (b'⁻¹ *ᵥ c)`. Rewrite `hmem` using `[Matrix.range_mulVecLin]`.

Rewrite using `[hxe]`. Conclude with `hmem`. Apply the tactic sequence `obtain ⟨k, hvk, hkW⟩ := exists_pivot_entry W v hv0`. Establish `hk : ∀ l, ι' l ≠ k` using `fun l hl => hvk (hl ▸ hvpiv l)`. Set `ιf : Fin (r + 1) → Fin n` to `Fin.lastCases (motive := fun _ => Fin n) k (fun i => ι' i)`.

Establish `hιf : Function.Injective ιf`. Introduce `i j hij`. Consider the cases of `i using Fin.lastCases with`. Consider the case `last`. Consider the cases of `j using Fin.lastCases with`.

Consider the case `last => rfl`. Consider the case `cast j`. Simplify using `only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij`. Conclude with `absurd hij.symm (hk j)`. Consider the case `cast i`.

Consider the cases of `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij`. Conclude with `absurd hij (hk i)`. Consider the case `cast j`.

Simplify using `only [ιf, Fin.lastCases_castSucc] at hij`. Rewrite using `[ι'.injective hij]`. Set `u : Matrix (Fin n) (Fin (r + 1)) L` to `Matrix.of fun a => Fin.snoc (α := fun _ => L) (u' a) (v a / v k)`. Set `b : Matrix (Fin (r + 1)) (Fin (r + 1)) L` to `Matrix.of fun i j => Fin.lastCases (motive := fun _ => L) (Fin.lastCases (motive := fun _ => L) (v k) (fun i' => c i') i) (fun j' => Fin.lastCases (motive := fun _ => L) 0 (fun i' => b' i' j') i) j`. Use `⟨⟨ιf, hιf⟩, u, b, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a j`. Consider the cases of `j using Fin.lastCases with`. Consider the case `last => simpa [u] using hkW a`. Consider the case `cast j => simpa [u] using hu'W a j`. Introduce `i j hij`.

Consider the cases of `i using Fin.lastCases with`. Consider the case `last => exact absurd hij (not_lt.2 (Fin.le_last j))`. Consider the case `cast i`. Consider the cases of `j using Fin.lastCases with`. Consider the case `last`.

Simplify using `only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc, Fin.snoc_last]`. Rewrite using `[hvpiv i, zero_div]`. Consider the case `cast j`. Simplify using `only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc, Fin.snoc_castSucc]`. Conclude with `hu'zero i j (Fin.castSucc_lt_castSucc_iff.1 hij)`.

Introduce `i`. Consider the cases of `i using Fin.lastCases with`. Consider the case `last`. Simplify using `only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_last, Fin.snoc_last]`. Conclude with `div_self hvk`.

Consider the case `cast i`. Simplify using `only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc, Fin.snoc_castSucc]`. Conclude with `hu'one i`. Introduce `i j hji`. Consider the cases of `i using Fin.lastCases with`.

Consider the case `last`. Consider the cases of `j using Fin.lastCases with`. Consider the case `last => exact absurd hji (lt_irrefl _)`. Consider the case `cast j => simp [b]`. Consider the case `cast i`.

Consider the cases of `j using Fin.lastCases with`. Consider the case `last => exact absurd hji (not_lt.2 (Fin.le_last _))`. Consider the case `cast j`. Simplify using `only [b, Matrix.of_apply, Fin.lastCases_castSucc]`. Conclude with `hb'tri (Fin.castSucc_lt_castSucc_iff.1 hji)`.

Introduce `i`. Consider the cases of `i using Fin.lastCases with`. Consider the case `last => simpa [b] using hvk`. Consider the case `cast i => simpa [b] using hb'diag i`. Use extensionality with `a j`.

Rewrite using `[Matrix.mul_apply, Fin.sum_univ_castSucc]`. Consider the cases of `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last, Fin.lastCases_last, Fin.lastCases_castSucc]`. Rewrite using `[div_mul_cancel₀ _ hvk]`.

Use `show x a = _ + (x a - (u' *ᵥ c) a)`. Simplify using `only [Matrix.mulVec, dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `cast j`. Simplify using `only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero, add_zero]`.

Apply the tactic sequence `have hentry := congrFun (congrFun hgub a) j`. Simplify `hentry` using `[g', cols', Matrix.mul_apply]`.
-/
private theorem exists_pivot_unipotent_mul_triangular {L : Type} [Field L] (W : ValuationSubring L) {n : ℕ} :
    ∀ (r : ℕ) (g : Matrix (Fin n) (Fin r) L), LinearIndependent L g.transpose →
      ∃ (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
        (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
        (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  intro r
  induction r with
  | zero =>
    intro g _
    refine ⟨⟨Fin.elim0, fun a => Fin.elim0 a⟩, 0, 0, fun _ j => Fin.elim0 j, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    ext _ j
    exact Fin.elim0 j
  | succ r ih =>
    intro g hg
    let cols' : Fin r → Fin n → L := fun i a => g a i.castSucc
    let g' : Matrix (Fin n) (Fin r) L := Matrix.of fun a i => cols' i a
    let x : Fin n → L := fun a => g a (Fin.last r)
    have hsplit : (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) = fun i a => g a i := by
      funext i a
      cases i using Fin.lastCases with
      | last => simp [x]
      | cast i => simp [cols']
    have hg2 : LinearIndependent L (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) := by
      rw [hsplit]
      exact hg
    rw [linearIndependent_finSnoc] at hg2
    obtain ⟨hg'ind, hxspan⟩ := hg2
    obtain ⟨ι', u', b', hu'W, hu'zero, hu'one, hb'tri, hb'diag, hgub⟩ := ih g' hg'ind
    have hb'det : IsUnit b'.det := by
      rw [Matrix.det_of_isUpperTriangular hb'tri]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hb'diag i).isUnit
    let M : Matrix (Fin r) (Fin r) L := Matrix.of fun l i => u' (ι' l) i
    have hMtri : M.BlockTriangular OrderDual.toDual := by
      intro l i hli
      simpa [M] using hu'zero l i (OrderDual.toDual_lt_toDual.1 hli)
    have hMdet : IsUnit M.det := by
      rw [Matrix.det_of_isLowerTriangular M hMtri]
      simp [M, hu'one]
    let c : Fin r → L := M⁻¹ *ᵥ (fun l => x (ι' l))
    let v : Fin n → L := x - u' *ᵥ c
    have hvpiv : ∀ l, v (ι' l) = 0 := by
      intro l
      have h1 : (u' *ᵥ c) (ι' l) = (M *ᵥ c) l := rfl
      have h2 : M *ᵥ c = fun l => x (ι' l) := by
        simp only [c]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMdet, Matrix.one_mulVec]
      show x (ι' l) - (u' *ᵥ c) (ι' l) = 0
      rw [h1, h2, sub_self]
    have hv0 : v ≠ 0 := by
      intro h0
      apply hxspan
      have hxv : x - u' *ᵥ c = 0 := h0
      have hu' : u' = g' * b'⁻¹ := by
        rw [hgub]
        exact (Matrix.mul_nonsing_inv_cancel_right (B := u') (h := hb'det)).symm
      have hxe : x = g' *ᵥ (b'⁻¹ *ᵥ c) := by
        rw [Matrix.mulVec_mulVec, ← hu']
        exact sub_eq_zero.1 hxv
      have hmem := LinearMap.mem_range_self g'.mulVecLin (b'⁻¹ *ᵥ c)
      rw [Matrix.range_mulVecLin] at hmem
      rw [hxe]
      exact hmem
    obtain ⟨k, hvk, hkW⟩ := exists_pivot_entry W v hv0
    have hk : ∀ l, ι' l ≠ k := fun l hl => hvk (hl ▸ hvpiv l)
    let ιf : Fin (r + 1) → Fin n := Fin.lastCases (motive := fun _ => Fin n) k (fun i => ι' i)
    have hιf : Function.Injective ιf := by
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => rfl
        | cast j =>
          simp only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact absurd hij.symm (hk j)
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          simp only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact absurd hij (hk i)
        | cast j =>
          simp only [ιf, Fin.lastCases_castSucc] at hij
          rw [ι'.injective hij]
    let u : Matrix (Fin n) (Fin (r + 1)) L :=
      Matrix.of fun a => Fin.snoc (α := fun _ => L) (u' a) (v a / v k)
    let b : Matrix (Fin (r + 1)) (Fin (r + 1)) L := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) (v k) (fun i' => c i') i)
        (fun j' => Fin.lastCases (motive := fun _ => L) 0 (fun i' => b' i' j') i) j
    refine ⟨⟨ιf, hιf⟩, u, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a j
      cases j using Fin.lastCases with
      | last => simpa [u] using hkW a
      | cast j => simpa [u] using hu'W a j
    · intro i j hij
      cases i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
            Fin.snoc_last]
          rw [hvpiv i, zero_div]
        | cast j =>
          simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
            Fin.snoc_castSucc]
          exact hu'zero i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_last,
          Fin.snoc_last]
        exact div_self hvk
      | cast i =>
        simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
          Fin.snoc_castSucc]
        exact hu'one i
    · intro i j hji
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => exact absurd hji (lt_irrefl _)
        | cast j => simp [b]
      | cast i =>
        cases j using Fin.lastCases with
        | last => exact absurd hji (not_lt.2 (Fin.le_last _))
        | cast j =>
          simp only [b, Matrix.of_apply, Fin.lastCases_castSucc]
          exact hb'tri (Fin.castSucc_lt_castSucc_iff.1 hji)
    · intro i
      cases i using Fin.lastCases with
      | last => simpa [b] using hvk
      | cast i => simpa [b] using hb'diag i
    · ext a j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      cases j using Fin.lastCases with
      | last =>
        simp only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last, Fin.lastCases_last,
          Fin.lastCases_castSucc]
        rw [div_mul_cancel₀ _ hvk]
        show x a = _ + (x a - (u' *ᵥ c) a)
        simp only [Matrix.mulVec, dotProduct]
        ring
      | cast j =>
        simp only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.lastCases_last,
          Fin.lastCases_castSucc, mul_zero, add_zero]
        have hentry := congrFun (congrFun hgub a) j
        simpa [g', cols', Matrix.mul_apply] using hentry

/- English proof (translation)
Introduce `L _ W n r g hg`. Conclude with `exists_pivot_unipotent_mul_triangular W r g hg`.
-/
theorem exists_integral_pivot_decomposition :
    ∀ (L : Type) [Field L] (W : ValuationSubring L) (n r : ℕ) (g : Matrix (Fin n) (Fin r) L),
      LinearIndependent L g.transpose →
      ∃ (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
        (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
        (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  intro L _ W n r g hg
  exact exists_pivot_unipotent_mul_triangular W r g hg

end GlobalTheory
