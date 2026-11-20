import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVec

noncomputable section

namespace RootFieldNumerics

open NumberField Filter Topology Matrix
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PM

/- English proof (translation)
Set `S : Matrix (Fin (p + q)) (Fin (p + q)) ℂ` to `diagonal (fun a => (sigForm (p + q) p a : ℂ))`. Establish `hS : S * S = 1`. Simplify using `only [S, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Unfold `sigForm`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h1 : fromCols (S * Mᴴ * Γ) (-(S * Qᵀ * Γ'ᵀ)) * fromRows M (Q.map (starRingEnd ℂ)) = 1`. Rewrite using `[fromCols_mul_fromRows, ← hS]`. Use `nth_rewrite 4 [show S = Mᴴ * Γ * M - Qᵀ * Γ'ᵀ * Q.map (starRingEnd ℂ) from h.symm]`.

Simplify using `only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, sub_eq_add_neg, Matrix.mul_add, Matrix.mul_neg]`. Establish `h2` using `(Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv (m := p) (n := q)).symm).1 h1`. Rewrite `h2` using `[fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj]`. Conclude with `⟨_, h2.1⟩`.
-/
theorem exists_rightInv {p q : ℕ} (Γ : Matrix (Fin p) (Fin p) ℂ) (Γ' : Matrix (Fin q) (Fin q) ℂ)
    (M : Matrix (Fin p) (Fin (p + q)) ℂ) (Q : Matrix (Fin q) (Fin (p + q)) ℂ)
    (h : Mᴴ * Γ * M - Qᵀ * Γ'ᵀ * Q.map (starRingEnd ℂ) = diagonal (fun a => (sigForm (p + q) p a : ℂ))) :
    ∃ L : Matrix (Fin (p + q)) (Fin p) ℂ, M * L = 1 := by
  let S : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := diagonal (fun a => (sigForm (p + q) p a : ℂ))
  have hS : S * S = 1 := by
    simp only [S, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    unfold sigForm
    split_ifs <;> simp
  have h1 : fromCols (S * Mᴴ * Γ) (-(S * Qᵀ * Γ'ᵀ)) * fromRows M (Q.map (starRingEnd ℂ)) = 1 := by
    rw [fromCols_mul_fromRows, ← hS]
    nth_rewrite 4 [show S = Mᴴ * Γ * M - Qᵀ * Γ'ᵀ * Q.map (starRingEnd ℂ) from h.symm]
    simp only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, sub_eq_add_neg, Matrix.mul_add, Matrix.mul_neg]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv (m := p) (n := q)).symm).1 h1
  rw [fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at h2
  exact ⟨_, h2.1⟩

/- English proof (translation)
Establish `hH : R.Hmᵀ.PosDef`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos R.herm.transpose fun z hz => ?_` and prove the remaining obligations. Establish `e : star z ⬝ᵥ R.Hmᵀ *ᵥ z = z ⬝ᵥ R.Hm *ᵥ star z`. Rewrite using `[Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]`. Establish `him : (star z ⬝ᵥ R.Hmᵀ *ᵥ z).im = 0` using `R.herm.transpose.im_star_dotProduct_mulVec_self z`.

Rewrite using `[Complex.pos_iff]`. Conclude with `⟨by rw [e]; exact R.pos z hz, him.symm⟩`. Establish `e : R.gram u = ((Matrix.of u)ᵀ)ᴴ * R.Hmᵀ * (Matrix.of u)ᵀ`. Use extensionality with `a b`. Simplify using `only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.conjTranspose_apply, Pi.star_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Rewrite using `[e]`.

Conclude with `hH.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff.2 hu)`.
-/
theorem gram_posDef {E : Type} [Field E] [NumberField E] [IsCMField E] {g m : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (u : Fin m → Fin g → ℂ) (hu : LinearIndependent ℂ u) : (R.gram u).PosDef := by
  have hH : R.Hmᵀ.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos R.herm.transpose fun z hz => ?_
    have e : star z ⬝ᵥ R.Hmᵀ *ᵥ z = z ⬝ᵥ R.Hm *ᵥ star z := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    have him : (star z ⬝ᵥ R.Hmᵀ *ᵥ z).im = 0 := R.herm.transpose.im_star_dotProduct_mulVec_self z
    rw [Complex.pos_iff]
    exact ⟨by rw [e]; exact R.pos z hz, him.symm⟩
  have e : R.gram u = ((Matrix.of u)ᵀ)ᴴ * R.Hmᵀ * (Matrix.of u)ᵀ := by
    ext a b
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.transpose_apply, Matrix.conjTranspose_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  exact hH.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff.2 hu)

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j < i`. Rewrite using `[hU h, zero_smul]`.

Conclude with `Submodule.zero_mem _`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_, rfl⟩)` and prove the remaining obligations. Establish `h1 : (i : ℕ) ≤ j` using `not_lt.1 h`. Establish `h2 : (j : ℕ) < k` using `hj`. Use `show (i : ℕ) < k`.

Use linear arithmetic over natural numbers and integers.
-/
theorem flagStep_le {W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (x : Fin m → W) (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U.BlockTriangular id) (k : ℕ) : flagStep ℂ (fun j => ∑ i, U i j • x i) k ≤ flagStep ℂ x k := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases h : j < i
  · rw [hU h, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_, rfl⟩)
    have h1 : (i : ℕ) ≤ j := not_lt.1 h
    have h2 : (j : ℕ) < k := hj
    show (i : ℕ) < k
    omega

/- English proof (translation)
Use `le_antisymm (flagStep_le x U hU k) ?_` and prove the remaining obligations. Use `letI := U.invertibleOfIsUnitDet hd`. Establish `h` using `flagStep_le (fun j => ∑ i, U i j • x i) U⁻¹ (blockTriangular_inv_of_blockTriangular hU) k`. Establish `e : (fun j => ∑ i, U⁻¹ i j • ∑ l, U l i • x l) = x`. Use function extensionality and compare the values at `j`.

Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`. Establish `: ∀ l, ∑ i, U⁻¹ i j * U l i = (1 : Matrix (Fin m) (Fin m) ℂ) l j` using `fun l => by`. Rewrite using `[← Matrix.mul_nonsing_inv U hd, Matrix.mul_apply]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Simplify using `[this, Matrix.one_apply]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem flagStep_eq {W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (x : Fin m → W) (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U.BlockTriangular id) (hd : IsUnit U.det) (k : ℕ) :
    flagStep ℂ (fun j => ∑ i, U i j • x i) k = flagStep ℂ x k := by
  refine le_antisymm (flagStep_le x U hU k) ?_
  letI := U.invertibleOfIsUnitDet hd
  have h := flagStep_le (fun j => ∑ i, U i j • x i) U⁻¹ (blockTriangular_inv_of_blockTriangular hU) k
  have e : (fun j => ∑ i, U⁻¹ i j • ∑ l, U l i • x l) = x := by
    funext j
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ l, ∑ i, U⁻¹ i j * U l i = (1 : Matrix (Fin m) (Fin m) ℂ) l j := fun l => by
      rw [← Matrix.mul_nonsing_inv U hd, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp [this, Matrix.one_apply]
  rwa [e] at h

/- English proof (translation)
Establish `h` using `hd.ne_zero`. Rewrite `h` using `[det_of_upperTriangular hT]`. Conclude with `Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)`.
-/
theorem diag_ne {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.BlockTriangular id) (hd : IsUnit T.det) (a : Fin N) :
    T a a ≠ 0 := by
  have h := hd.ne_zero
  rw [det_of_upperTriangular hT] at h
  exact Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)

/- English proof (translation)
Rewrite using `[det_of_upperTriangular hT]`. Conclude with `(Finset.prod_ne_zero_iff.2 fun a _ => hd a).isUnit`.
-/
theorem unit_of_diag {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.BlockTriangular id) (hd : ∀ a, T a a ≠ 0) :
    IsUnit T.det := by
  rw [det_of_upperTriangular hT]
  exact (Finset.prod_ne_zero_iff.2 fun a _ => hd a).isUnit

/- English proof (translation)
Set `ι : Fin p → Fin (p + q)` to `fun a => ⟨q + a, by have := a.2; omega⟩`. Establish `hι : ∀ (a : Fin p) (b : Fin (p + q)), (b : ℕ) = q + a ↔ b = ι a` using `fun a b => ⟨fun h => Fin.ext h, fun h => by rw [h]⟩`. Set `U : Matrix (Fin p) (Fin p) ℂ` to `T.submatrix ι ι`. Establish `hU : U.BlockTriangular id` using `fun a b h => hT (show ι b < ι a from by`. Establish `: (b : ℕ) < a` using `h`.

Use `show q + (b : ℕ) < q + a`. Use the proof step `omega)`. Use `⟨U, hU, unit_of_diag hU fun a => diag_ne hT hd _, ?_⟩` and prove the remaining obligations. Establish `key : M * g' = U * M' * g'`. Use extensionality with `a c`.

Establish `e1 : (M * g') a c = T (ι a) c`. Rewrite using `[e, ← Matrix.mul_assoc, Matrix.mul_apply]`. Simplify using `[hM, hι]`. Rewrite using `[e1, Matrix.mul_assoc, Matrix.mul_apply]`. Simplify using `only [hM', mul_ite, mul_one, mul_zero]`.

Distinguish the cases in `hc : (c : ℕ) < q`. Rewrite using `[hT (show c < ι a from by show (c : ℕ) < q + a; omega)]`. Conclude with `(Finset.sum_eq_zero fun b _ => if_neg (by omega)).symm`. Set `b : Fin p` to `⟨c - q, by have := c.2; omega⟩`. Establish `hb : c = ι b` using `Fin.ext (by show (c : ℕ) = q + (c - q); omega)`.

Rewrite using `[Finset.sum_eq_single b (fun b' _ hb' => if_neg fun h => hb' (Fin.ext (by show (b' : ℕ) = c - q; omega))) (fun h => absurd (Finset.mem_univ _) h), if_pos (by show (c : ℕ) = q + (c - q); omega)]`. Use `show T (ι a) c = T (ι a) (ι b)`. Rewrite using `[← hb]`. Use `congrArg (· * g'⁻¹) key` as an intermediate fact. Simplify `this` using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv g' hg', Matrix.mul_one]`.
-/
theorem tri_M {p q : ℕ} {M M' : Matrix (Fin p) (Fin (p + q)) ℂ} {g g' T : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}
    (hM : ∀ a b, (M * g) a b = if (b : ℕ) = q + a then 1 else 0)
    (hM' : ∀ a b, (M' * g') a b = if (b : ℕ) = q + a then 1 else 0) (hg' : IsUnit g'.det)
    (hT : T.BlockTriangular id) (hd : IsUnit T.det) (e : g' = g * T) :
    ∃ U : Matrix (Fin p) (Fin p) ℂ, U.BlockTriangular id ∧ IsUnit U.det ∧ M = U * M' := by
  let ι : Fin p → Fin (p + q) := fun a => ⟨q + a, by have := a.2; omega⟩
  have hι : ∀ (a : Fin p) (b : Fin (p + q)), (b : ℕ) = q + a ↔ b = ι a := fun a b => ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  let U : Matrix (Fin p) (Fin p) ℂ := T.submatrix ι ι
  have hU : U.BlockTriangular id := fun a b h => hT (show ι b < ι a from by
    have : (b : ℕ) < a := h
    show q + (b : ℕ) < q + a
    omega)
  refine ⟨U, hU, unit_of_diag hU fun a => diag_ne hT hd _, ?_⟩
  have key : M * g' = U * M' * g' := by
    ext a c
    have e1 : (M * g') a c = T (ι a) c := by
      rw [e, ← Matrix.mul_assoc, Matrix.mul_apply]
      simp [hM, hι]
    rw [e1, Matrix.mul_assoc, Matrix.mul_apply]
    simp only [hM', mul_ite, mul_one, mul_zero]
    by_cases hc : (c : ℕ) < q
    · rw [hT (show c < ι a from by show (c : ℕ) < q + a; omega)]
      exact (Finset.sum_eq_zero fun b _ => if_neg (by omega)).symm
    · let b : Fin p := ⟨c - q, by have := c.2; omega⟩
      have hb : c = ι b := Fin.ext (by show (c : ℕ) = q + (c - q); omega)
      rw [Finset.sum_eq_single b (fun b' _ hb' => if_neg fun h => hb' (Fin.ext (by show (b' : ℕ) = c - q; omega)))
        (fun h => absurd (Finset.mem_univ _) h), if_pos (by show (c : ℕ) = q + (c - q); omega)]
      show T (ι a) c = T (ι a) (ι b)
      rw [← hb]
  have := congrArg (· * g'⁻¹) key
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv g' hg', Matrix.mul_one] using this

/- English proof (translation)
Set `ι : Fin q → Fin (p + q)` to `fun a => ⟨q - 1 - a, by have := a.2; omega⟩`. Set `U : Matrix (Fin q) (Fin q) ℂ` to `Matrix.of fun i j => T (ι j) (ι i)`. Establish `hU : U.BlockTriangular id` using `fun a b h => hT (show ι a < ι b from by`. Establish `h1 : (b : ℕ) < a` using `h`. Use `a.2` as an intermediate fact.

Use `show q - 1 - (a : ℕ) < q - 1 - b`. Use the proof step `omega)`. Use `⟨U, hU, unit_of_diag hU fun a => diag_ne hT hd _, ?_⟩` and prove the remaining obligations. Establish `hp : ∀ (Q : Matrix (Fin q) (Fin (p + q)) ℂ) (L : Matrix (Fin (p + q)) (Fin p) ℂ) a i, perMat Q L a (ι i) = (sigForm (p + q) p a : ℂ) * Q i a` using `fun Q L a i => by`. Establish `hi` using `i.2`.

Establish `h1 : ((ι i : Fin (p + q)) : ℕ) < q` using `by show q - 1 - (i : ℕ) < q; omega`. Simplify using `only [perMat, Matrix.of_apply, dif_pos h1]`. Use `congr 2`. Conclude with `Fin.ext (by show q - 1 - (q - 1 - (i : ℕ)) = i; omega)`. Establish `hinj : Function.Injective ι` using `fun a b h => by`.

Establish `h1 : q - 1 - (a : ℕ) = q - 1 - b` using `congrArg Fin.val h`. Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Conclude with `Fin.ext (by omega)`. Use extensionality with `i a`.

Establish `hs : (sigForm (p + q) p a : ℂ) ≠ 0`. Unfold `sigForm`. Apply the tactic sequence `split_ifs <;> simp`. Use `mul_left_cancel₀ hs ?_` and prove the remaining obligations. Rewrite using `[← hp Q L, e, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]`.

Use `symm`. Use `Finset.sum_of_injOn ι hinj.injOn (fun _ _ => Finset.mem_univ _) (fun c _ hc => ?_) fun j _ => ?_` and prove the remaining obligations. Establish `hq : q ≤ (c : ℕ)`. Assume the negation of the conclusion as `h`. Use `hc ⟨⟨q - 1 - c, by omega⟩, by simp, Fin.ext ?_⟩` and prove the remaining obligations.

Use `show q - 1 - (q - 1 - (c : ℕ)) = c`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hT (show ι i < c from by have := i.2; show q - 1 - (i : ℕ) < c; omega), mul_zero]`. Rewrite using `[hp]`. Simplify using `only [U, Matrix.of_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tri_Q {p q : ℕ} {Q Q' : Matrix (Fin q) (Fin (p + q)) ℂ} {L L' : Matrix (Fin (p + q)) (Fin p) ℂ}
    {T : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hT : T.BlockTriangular id) (hd : IsUnit T.det)
    (e : perMat Q L = perMat Q' L' * T) :
    ∃ U : Matrix (Fin q) (Fin q) ℂ, U.BlockTriangular id ∧ IsUnit U.det ∧ Q = U * Q' := by
  let ι : Fin q → Fin (p + q) := fun a => ⟨q - 1 - a, by have := a.2; omega⟩
  let U : Matrix (Fin q) (Fin q) ℂ := Matrix.of fun i j => T (ι j) (ι i)
  have hU : U.BlockTriangular id := fun a b h => hT (show ι a < ι b from by
    have h1 : (b : ℕ) < a := h
    have := a.2
    show q - 1 - (a : ℕ) < q - 1 - b
    omega)
  refine ⟨U, hU, unit_of_diag hU fun a => diag_ne hT hd _, ?_⟩
  have hp : ∀ (Q : Matrix (Fin q) (Fin (p + q)) ℂ) (L : Matrix (Fin (p + q)) (Fin p) ℂ) a i,
      perMat Q L a (ι i) = (sigForm (p + q) p a : ℂ) * Q i a := fun Q L a i => by
    have hi := i.2
    have h1 : ((ι i : Fin (p + q)) : ℕ) < q := by show q - 1 - (i : ℕ) < q; omega
    simp only [perMat, Matrix.of_apply, dif_pos h1]
    congr 2
    exact Fin.ext (by show q - 1 - (q - 1 - (i : ℕ)) = i; omega)
  have hinj : Function.Injective ι := fun a b h => by
    have h1 : q - 1 - (a : ℕ) = q - 1 - b := congrArg Fin.val h
    have := a.2
    have := b.2
    exact Fin.ext (by omega)
  ext i a
  have hs : (sigForm (p + q) p a : ℂ) ≠ 0 := by
    unfold sigForm
    split_ifs <;> simp
  refine mul_left_cancel₀ hs ?_
  rw [← hp Q L, e, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
  symm
  refine Finset.sum_of_injOn ι hinj.injOn (fun _ _ => Finset.mem_univ _) (fun c _ hc => ?_) fun j _ => ?_
  · have hq : q ≤ (c : ℕ) := by
      by_contra h
      refine hc ⟨⟨q - 1 - c, by omega⟩, by simp, Fin.ext ?_⟩
      show q - 1 - (q - 1 - (c : ℕ)) = c
      omega
    rw [hT (show ι i < c from by have := i.2; show q - 1 - (i : ℕ) < c; omega), mul_zero]
  · rw [hp]
    simp only [U, Matrix.of_apply]
    ring

/- English proof (translation)
Simplify using `only [Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]`.
-/
theorem sum_frame {W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (x : Fin m → W) (U : Matrix (Fin m) (Fin m) ℂ)
    (c : Fin m → ℂ) : ∑ j, c j • ∑ i, U i j • x i = ∑ i, (U *ᵥ c) i • x i := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨i, i.2, rfl⟩`.
-/
theorem mem_step {W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (x : Fin m → W) (i : Fin m) : x i ∈ flagStep ℂ x m :=
  Submodule.subset_span ⟨i, i.2, rfl⟩

end PM

open PM

/- English proof (translation)
Introduce `hC hS E _ _ _ Ψ _ g n p q Λ _ _ V R σ x x' hV hR hσ hF t₀ ht₀`. Take `⟨M, Q, cc, hMa, hQa, hall⟩` from `hC E Ψ g n p q Λ V R σ x x' hV hR hσ hF`. Use `choose L₀ hL₀ using fun τ => exists_rightInv _ _ _ _ ((hall t₀ ht₀).1 τ)`. Establish `hA : ∀ τ, ∀ t ∈ V, ∀ a b, AnalyticAt ℂ (fun t => (M τ t * L₀ τ) a b) t` using `fun τ t ht a b => by`. Simplify using `only [Matrix.mul_apply]`.

Conclude with `Finset.analyticAt_fun_sum _ fun i _ => (hMa τ a i t ht).mul analyticAt_const`. Set `V' : Set (Fin n → ℂ)` to `{t ∈ V | ∀ τ, (M τ t * L₀ τ).det ≠ 0}`. Establish `hV' : IsOpen V'`. Use `isOpen_iff_mem_nhds.2 fun t ht => ?_` and prove the remaining obligations. Use `filter_upwards [hV.mem_nhds ht.1, Filter.eventually_all.2 fun τ => (SheetDecomposition.vecDetAn (hA τ t ht.1)).continuousAt.eventually_ne (ht.2 τ)] with s h1 h2`.

Conclude with `⟨h1, h2⟩`. Set `L : Ψ → (Fin n → ℂ) → Matrix (Fin (p + q)) (Fin p) ℂ` to `fun τ t => L₀ τ * (M τ t * L₀ τ)⁻¹`. Establish `hML : ∀ τ, ∀ t ∈ V', M τ t * L τ t = 1` using `fun τ t ht => by`. Simplify using `only [L]`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ht.2 τ).isUnit]`.

Establish `hLa : ∀ τ, ∀ t ∈ V', ∀ a b, AnalyticAt ℂ (fun t => L τ t a b) t` using `fun τ t ht a b => by`. Simplify using `only [L, Matrix.mul_apply (M := L₀ τ)]`. Use `Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ?_` and prove the remaining obligations. Establish `h` using `SheetDecomposition.vecInvAn (w := fun _ => Pi.single b 1) (hA τ t ht.1) (ht.2 τ) analyticAt_const`. Establish `h2` using `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p => ℂ) i).analyticAt _).comp h`.

Simplify `h2` using `[Function.comp_def]`. Establish `hst` using `fun τ t (ht : t ∈ V') => hS p q _ _ (M τ t) (Q τ t) (L τ t) (gram_posDef (R t) _ (hF.2.2 t ht.1 τ).1.1) (gram_posDef (R t) _ (hF.2.2 t ht.1 τ).2.1) ((hall t ht.1).1 τ) (hML τ t ht)`. Use `⟨V', fun τ t => perMat (Q τ t) (L τ t), hV', ⟨ht₀, fun τ => by rw [hL₀]; simp⟩, fun _ h => h.1, fun τ a b t ht => ?_, fun t ht τ => ⟨(hst τ t ht).1, (hst τ t ht).2.1⟩, fun t ht t' ht' hfl => ?_⟩` and prove the remaining obligations. Simplify using `only [perMat, Matrix.of_apply] split_ifs`. Conclude with `analyticAt_const.mul (hQa τ _ _ t ht.1)`.

Conclude with `hLa τ t ht _ _`. Use `choose T hT hTe using hfl`. Establish `hTd : ∀ τ, IsUnit (T τ).det` using `fun τ => by`. Establish `h` using `(hst τ t' ht').1.1`. Rewrite `h` using `[show perMat (Q τ t') (L τ t') = _ from hTe τ, Matrix.det_mul]`.

Conclude with `isUnit_of_mul_isUnit_right h`. Use `choose U hU hUd hUe using fun τ => tri_M (hst τ t ht).2.2 (hst τ t' ht').2.2 (hst τ t' ht').1.1 (hT τ) (hTd τ) (hTe τ)`. Use `choose U' hU' hUd' hUe' using fun τ => tri_Q (Q := Q τ t) (Q' := Q τ t') (L := L τ t) (L' := L τ t') (T := (T τ)⁻¹) (by letI := (T τ).invertibleOfIsUnitDet (hTd τ); exact blockTriangular_inv_of_blockTriangular (hT τ)) (Matrix.isUnit_nonsing_inv_det _ (hTd τ)) (by rw [show perMat …`. Set `B` to `Module.Basis.mk (hall t' ht'.1).2.2.1 (hall t' ht'.1).2.2.2.ge`. Set `k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `B.constr ℂ (Sum.elim (fun a : Ψ × Fin p => ∑ i, U a.1 i a.2 • x a.1 i t) fun a : Ψ × Fin q => ∑ i, U' a.1 i a.2 • x' a.1 i t)`.

Establish `hk : ∀ τ j, k (x τ j t') = ∑ i, U τ i j • x τ i t` using `fun τ j => by`. Establish `h` using `B.constr_basis ℂ (Sum.elim (fun a : Ψ × Fin p => ∑ i, U a.1 i a.2 • x a.1 i t) fun a : Ψ × Fin q => ∑ i, U' a.1 i a.2 • x' a.1 i t) (.inl (τ, j))`. Rewrite `h` using `[Module.Basis.mk_apply]`. Conclude with `h`. Establish `hk' : ∀ τ j, k (x' τ j t') = ∑ i, U' τ i j • x' τ i t` using `fun τ j => by`.

Establish `h` using `B.constr_basis ℂ (Sum.elim (fun a : Ψ × Fin p => ∑ i, U a.1 i a.2 • x a.1 i t) fun a : Ψ × Fin q => ∑ i, U' a.1 i a.2 • x' a.1 i t) (.inr (τ, j))`. Rewrite `h` using `[Module.Basis.mk_apply]`. Conclude with `h`. Establish `hf : ∀ τ m, flagStep ℂ (fun i => k (x τ i t')) m = flagStep ℂ (fun i => x τ i t) m` using `fun τ m => by`. Simplify using `only [hk]`.

Conclude with `flagStep_eq _ _ (hU τ) (hUd τ) m`. Establish `hf' : ∀ τ m, flagStep ℂ (fun i => k (x' τ i t')) m = flagStep ℂ (fun i => x' τ i t) m` using `fun τ m => by`. Simplify using `only [hk']`. Conclude with `flagStep_eq _ _ (hU' τ) (hUd' τ) m`. Establish `hsurj : Function.Surjective k`.

Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← (hall t ht.1).2.2.2, Submodule.span_le]`. Establish `hr : ∀ {m : ℕ} (y : Fin m → Fin g → ℂ), flagStep ℂ (fun i => k (y i)) m ≤ LinearMap.range k` using `fun y => Submodule.span_le.2 (by rintro _ ⟨i, -, rfl⟩; exact ⟨_, rfl⟩)`. Introduce and unpack `_ ⟨a | a, rfl⟩`. Conclude with `hr _ ((hf a.1 p).ge (mem_step (fun i => x a.1 i t) a.2))`. Conclude with `hr _ ((hf' a.1 q).ge (mem_step (fun i => x' a.1 i t) a.2))`.

Set `ke` to `LinearEquiv.ofBijective k ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩`. Use `⟨ke.symm, fun a => ?_, fun τ m => ⟨hf τ m, hf' τ m⟩⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.eq_symm_apply]`. Use `show k _ = _`. Rewrite using `[(hall t' ht'.1).2.1 a, (hall t ht.1).2.1 a]`.

Simplify using `only [map_sum, map_add, map_smul, hk, hk']`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[sum_frame, sum_frame, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hUe, ← hUe']`.
-/
theorem perMat_of : PerCoord → MatStep → PerMat := by
  intro hC hS E _ _ _ Ψ _ g n p q Λ _ _ V R σ x x' hV hR hσ hF t₀ ht₀
  classical
  obtain ⟨M, Q, cc, hMa, hQa, hall⟩ := hC E Ψ g n p q Λ V R σ x x' hV hR hσ hF
  choose L₀ hL₀ using fun τ => exists_rightInv _ _ _ _ ((hall t₀ ht₀).1 τ)
  have hA : ∀ τ, ∀ t ∈ V, ∀ a b, AnalyticAt ℂ (fun t => (M τ t * L₀ τ) a b) t := fun τ t ht a b => by
    simp only [Matrix.mul_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hMa τ a i t ht).mul analyticAt_const
  let V' : Set (Fin n → ℂ) := {t ∈ V | ∀ τ, (M τ t * L₀ τ).det ≠ 0}
  have hV' : IsOpen V' := by
    refine isOpen_iff_mem_nhds.2 fun t ht => ?_
    filter_upwards [hV.mem_nhds ht.1, Filter.eventually_all.2 fun τ =>
      (SheetDecomposition.vecDetAn (hA τ t ht.1)).continuousAt.eventually_ne (ht.2 τ)] with s h1 h2
    exact ⟨h1, h2⟩
  let L : Ψ → (Fin n → ℂ) → Matrix (Fin (p + q)) (Fin p) ℂ := fun τ t => L₀ τ * (M τ t * L₀ τ)⁻¹
  have hML : ∀ τ, ∀ t ∈ V', M τ t * L τ t = 1 := fun τ t ht => by
    simp only [L]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ht.2 τ).isUnit]
  have hLa : ∀ τ, ∀ t ∈ V', ∀ a b, AnalyticAt ℂ (fun t => L τ t a b) t := fun τ t ht a b => by
    simp only [L, Matrix.mul_apply (M := L₀ τ)]
    refine Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ?_
    have h := SheetDecomposition.vecInvAn (w := fun _ => Pi.single b 1) (hA τ t ht.1) (ht.2 τ) analyticAt_const
    have h2 := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p => ℂ) i).analyticAt _).comp h
    simpa [Function.comp_def] using h2
  have hst := fun τ t (ht : t ∈ V') => hS p q _ _ (M τ t) (Q τ t) (L τ t) (gram_posDef (R t) _ (hF.2.2 t ht.1 τ).1.1)
    (gram_posDef (R t) _ (hF.2.2 t ht.1 τ).2.1) ((hall t ht.1).1 τ) (hML τ t ht)
  refine ⟨V', fun τ t => perMat (Q τ t) (L τ t), hV', ⟨ht₀, fun τ => by rw [hL₀]; simp⟩, fun _ h => h.1,
    fun τ a b t ht => ?_, fun t ht τ => ⟨(hst τ t ht).1, (hst τ t ht).2.1⟩, fun t ht t' ht' hfl => ?_⟩
  · simp only [perMat, Matrix.of_apply]
    split_ifs
    · exact analyticAt_const.mul (hQa τ _ _ t ht.1)
    · exact hLa τ t ht _ _
  · choose T hT hTe using hfl
    have hTd : ∀ τ, IsUnit (T τ).det := fun τ => by
      have h := (hst τ t' ht').1.1
      rw [show perMat (Q τ t') (L τ t') = _ from hTe τ, Matrix.det_mul] at h
      exact isUnit_of_mul_isUnit_right h
    choose U hU hUd hUe using fun τ =>
      tri_M (hst τ t ht).2.2 (hst τ t' ht').2.2 (hst τ t' ht').1.1 (hT τ) (hTd τ) (hTe τ)
    choose U' hU' hUd' hUe' using fun τ =>
      tri_Q (Q := Q τ t) (Q' := Q τ t') (L := L τ t) (L' := L τ t') (T := (T τ)⁻¹)
        (by letI := (T τ).invertibleOfIsUnitDet (hTd τ); exact blockTriangular_inv_of_blockTriangular (hT τ))
        (Matrix.isUnit_nonsing_inv_det _ (hTd τ))
        (by rw [show perMat (Q τ t') (L τ t') = _ from hTe τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hTd τ),
          Matrix.mul_one])
    let B := Module.Basis.mk (hall t' ht'.1).2.2.1 (hall t' ht'.1).2.2.2.ge
    let k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := B.constr ℂ (Sum.elim (fun a : Ψ × Fin p => ∑ i, U a.1 i a.2 • x a.1 i t)
      fun a : Ψ × Fin q => ∑ i, U' a.1 i a.2 • x' a.1 i t)
    have hk : ∀ τ j, k (x τ j t') = ∑ i, U τ i j • x τ i t := fun τ j => by
      have h := B.constr_basis ℂ (Sum.elim (fun a : Ψ × Fin p => ∑ i, U a.1 i a.2 • x a.1 i t)
        fun a : Ψ × Fin q => ∑ i, U' a.1 i a.2 • x' a.1 i t) (.inl (τ, j))
      rw [Module.Basis.mk_apply] at h
      exact h
    have hk' : ∀ τ j, k (x' τ j t') = ∑ i, U' τ i j • x' τ i t := fun τ j => by
      have h := B.constr_basis ℂ (Sum.elim (fun a : Ψ × Fin p => ∑ i, U a.1 i a.2 • x a.1 i t)
        fun a : Ψ × Fin q => ∑ i, U' a.1 i a.2 • x' a.1 i t) (.inr (τ, j))
      rw [Module.Basis.mk_apply] at h
      exact h
    have hf : ∀ τ m, flagStep ℂ (fun i => k (x τ i t')) m = flagStep ℂ (fun i => x τ i t) m := fun τ m => by
      simp only [hk]
      exact flagStep_eq _ _ (hU τ) (hUd τ) m
    have hf' : ∀ τ m, flagStep ℂ (fun i => k (x' τ i t')) m = flagStep ℂ (fun i => x' τ i t) m := fun τ m => by
      simp only [hk']
      exact flagStep_eq _ _ (hU' τ) (hUd' τ) m
    have hsurj : Function.Surjective k := by
      rw [← LinearMap.range_eq_top, eq_top_iff, ← (hall t ht.1).2.2.2, Submodule.span_le]
      have hr : ∀ {m : ℕ} (y : Fin m → Fin g → ℂ), flagStep ℂ (fun i => k (y i)) m ≤ LinearMap.range k := fun y =>
        Submodule.span_le.2 (by rintro _ ⟨i, -, rfl⟩; exact ⟨_, rfl⟩)
      rintro _ ⟨a | a, rfl⟩
      · exact hr _ ((hf a.1 p).ge (mem_step (fun i => x a.1 i t) a.2))
      · exact hr _ ((hf' a.1 q).ge (mem_step (fun i => x' a.1 i t) a.2))
    let ke := LinearEquiv.ofBijective k ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
    refine ⟨ke.symm, fun a => ?_, fun τ m => ⟨hf τ m, hf' τ m⟩⟩
    rw [LinearEquiv.eq_symm_apply]
    show k _ = _
    rw [(hall t' ht'.1).2.1 a, (hall t ht.1).2.1 a]
    simp only [map_sum, map_add, map_smul, hk, hk']
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [sum_frame, sum_frame, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hUe, ← hUe']

end RootFieldNumerics
