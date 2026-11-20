import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.LowBlocks

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Unfold `Formalism.UG.ordL`. Distinguish the cases in `hx : Valued.v x = 0`. Establish `hy : Valued.v y = 0` using `h ▸ hx`. Rewrite using `[dif_pos hx, dif_pos hy]`. Establish `hy : Valued.v y ≠ 0` using `h ▸ hx`.

Rewrite using `[dif_neg hx, dif_neg hy]`. Use `congr 2`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[WithZero.coe_unzero, WithZero.coe_unzero, h]`.
-/
theorem ordL_congr_v {x y : L} (h : Valued.v x = Valued.v y) : Formalism.UG.ordL x = Formalism.UG.ordL y := by
  unfold Formalism.UG.ordL
  by_cases hx : Valued.v x = 0
  · have hy : Valued.v y = 0 := h ▸ hx
    rw [dif_pos hx, dif_pos hy]
  · have hy : Valued.v y ≠ 0 := h ▸ hx
    rw [dif_neg hx, dif_neg hy]
    congr 2
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_unzero, h]

/- English proof (translation)
The claim follows from `Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)`.
-/
theorem ordL_one_eq : Formalism.UG.ordL (1 : L) = 0 :=
  Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)

/- English proof (translation)
Establish `hx : x ≠ 0` using `left_ne_zero_of_mul_eq_one h`. Establish `hy : y ≠ 0` using `right_ne_zero_of_mul_eq_one h`. Use `Formalism.UG.P.fIwasawa_ordL_mul x y hx hy` as an intermediate fact. Rewrite `this` using `[h, ordL_one_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ordL_of_mul_eq_one {x y : L} (h : x * y = 1) : Formalism.UG.ordL y = - Formalism.UG.ordL x := by
  have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
  have := Formalism.UG.P.fIwasawa_ordL_mul x y hx hy
  rw [h, ordL_one_eq] at this
  omega

variable {σ : L →+* L} {n : ℕ}

/- English proof (translation)
Rewrite using `[ordL_of_mul_eq_one (Formalism.UG.P.fSatake_unit_diag hb i), ordL_congr_v (hv _)]`.
-/
theorem ordL_rev_diag (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    Formalism.UG.ordL (b.1.1 i.rev i.rev) = - Formalism.UG.ordL (b.1.1 i i) := by
  rw [ordL_of_mul_eq_one (Formalism.UG.P.fSatake_unit_diag hb i), ordL_congr_v (hv _)]

/- English proof (translation)
Introduce `h0` and use `by have := Formalism.UG.P.fSatake_unit_diag hb i rw [show (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 0 from h0, map_zero, zero_mul] at this exact zero_ne_one this`.
-/
theorem diag_ne_zero {b : GU σ n} (hb : IsBorelU b) (i : Fin n) : b.1.1 i i ≠ 0 := fun h0 => by
  have := Formalism.UG.P.fSatake_unit_diag hb i
  rw [show (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 0 from h0, map_zero, zero_mul] at this
  exact zero_ne_one this

/- English proof (translation)
Introduce `i j hij` and use `by apply hM rw [Fin.lt_def] at hij ⊢ simp only [hi, id] at * omega`.
-/
theorem lowBlock_tri {M : Matrix (Fin n) (Fin n) L} (hM : ∀ i j : Fin n, j < i → M i j = 0) :
    (lowBlock M).BlockTriangular id := fun i j hij => by
  apply hM
  rw [Fin.lt_def] at hij ⊢
  simp only [hi, id] at *
  omega

/- English proof (translation)
Use `ext`. Simplify using `only [hi, lo, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem hi_eq_rev_lo (r : Fin (n / 2)) : hi n r = (lo n r.rev).rev := by
  ext; simp only [hi, lo, Fin.val_rev]; omega

end GlobalTheory.SphTheta.LowBlocks

open GlobalTheory.SphTheta.LowBlocks in

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU n n' hn`. Establish `hv : ∀ x, Valued.v (σ x) = Valued.v x` using `hU.2.1`. Use `⟨fun g hg => ?_, fun h hh => ?_⟩` and prove the remaining obligations. Establish `htri : (lowBlock g.1.1).BlockTriangular id` using `lowBlock_tri hg`. Establish `hdet : (lowBlock g.1.1).det ≠ 0`.

Rewrite using `[Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]`. Introduce `r _`. Conclude with `diag_ne_zero hg _`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, htri, fun r => ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.ordL (g.1.1 (hi n r) (hi n r)) = _`.

Rewrite using `[hi_eq_rev_lo, ordL_rev_diag hv hg]`. Establish `hle : n / 2 ≤ n' / 2` using `Nat.div_le_div_right hn`. Establish `hb' : IsBorelU h⁻¹` using `Formalism.UG.P.fSatake_borel_inv hh`. Use `set W := lowBlock (h⁻¹).1.1 with hW`. Establish `hWt : W.BlockTriangular id` using `lowBlock_tri hb'`.

Use `set V0 : Matrix (Fin (n / 2)) (Fin (n / 2)) L := W.submatrix (Fin.castLE hle) (Fin.castLE hle) with hV0`. Establish `htri : V0.BlockTriangular id` using `fun i j hij => hWt (by rw [Fin.lt_def] at hij ⊢; exact hij)`. Establish `hdet : V0.det ≠ 0`. Rewrite using `[Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]`. Introduce `r _`.

Conclude with `diag_ne_zero hb' _`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, htri, fun r => ?_, fun t => ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.ordL ((h⁻¹).1.1 (hi n' (Fin.castLE hle r.rev)) (hi n' (Fin.castLE hle r.rev))) = _`. Establish `e : hi n' (Fin.castLE hle r.rev) = (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev` using `by ext; simp only [hi, lo, Fin.val_rev, Fin.coe_castLE]; omega`. Rewrite using `[e]`.

Establish `a` using `ordL_of_mul_eq_one (Formalism.UG.P.fSatake_borel_diag_inv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev)`. Establish `b` using `ordL_rev_diag hv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩)`. Express the relevant statement in the definitionally equal form `Formalism.UG.ordL (h.1.1 _ _) = - Formalism.UG.ordL ((h⁻¹).1.1 _ _) at a`. Combine the linear equalities and inequalities to obtain the conclusion. Use extensionality with `r c`.

Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `split_ifs with hr`. Establish `hr' : (Fin.castLE hle ⟨r.1, hr⟩ : Fin (n' / 2)) = r` using `Fin.ext rfl`. Set `emb : Fin (n / 2) ↪ Fin (n' / 2)` to `⟨Fin.castLE hle, Fin.castLE_injective hle⟩`. Rewrite using `[← Finset.sum_subset (s₁ := Finset.univ.map emb) (Finset.subset_univ _), Finset.sum_map]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hk : ((emb k : Fin (n' / 2)) : ℕ) < n / 2` using `k.2`. Rewrite using `[dif_pos hk]`. Use `show W r (Fin.castLE hle k) * t ⟨k.1, hk⟩ c = W (Fin.castLE hle ⟨r.1, hr⟩) (Fin.castLE hle k) * t k c`. Rewrite using `[hr']`.

Introduce `k _ hk`. Establish `: ¬ (k : ℕ) < n / 2` using `fun e => hk (Finset.mem_map.2 ⟨⟨k.1, e⟩, Finset.mem_univ _, Fin.ext rfl⟩)`. Rewrite using `[dif_neg this, mul_zero]`. Use `Finset.sum_eq_zero fun k _ => ?_ split_ifs with hk` and prove the remaining obligations. Rewrite using `[hWt (show k < r by rw [Fin.lt_def]; omega), zero_mul]`.

Rewrite using `[mul_zero]`.
-/
theorem GlobalTheory.SphTheta.lowBlocks_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (hn : n ≤ n'), (∀ g : GU σ n, IsBorelU g → ∃ U : GL (Fin (n / 2)) L, U.1 = lowBlock g.1.1 ∧ U.1.BlockTriangular id ∧ ∀ r, ordL (U.1 r r) = -ordL (g.1.1 (lo n r.rev) (lo n r.rev))) ∧ ∀ h : GU σ n', IsBorelU h → ∃ V : GL (Fin (n / 2)) L, V.1.BlockTriangular id ∧ (∀ r : Fin (n / 2), ordL (V.1 r.rev r.rev) = ordL (h.1.1 (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩) (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩))) ∧ ∀ t : Matrix (Fin (n / 2)) (Fin (n / 2)) L, lowBlock (h⁻¹).1.1 * (Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0) = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then (V.1 * t) ⟨r.1, e⟩ c else 0 := by
  intro L _ _ ϖ σ q hU n n' hn
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  refine ⟨fun g hg => ?_, fun h hh => ?_⟩
  · have htri : (lowBlock g.1.1).BlockTriangular id := lowBlock_tri hg
    have hdet : (lowBlock g.1.1).det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
      intro r _
      exact diag_ne_zero hg _
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, htri, fun r => ?_⟩
    show Formalism.UG.ordL (g.1.1 (hi n r) (hi n r)) = _
    rw [hi_eq_rev_lo, ordL_rev_diag hv hg]
  · have hle : n / 2 ≤ n' / 2 := Nat.div_le_div_right hn
    have hb' : IsBorelU h⁻¹ := Formalism.UG.P.fSatake_borel_inv hh
    set W := lowBlock (h⁻¹).1.1 with hW
    have hWt : W.BlockTriangular id := lowBlock_tri hb'
    set V0 : Matrix (Fin (n / 2)) (Fin (n / 2)) L := W.submatrix (Fin.castLE hle) (Fin.castLE hle) with hV0
    have htri : V0.BlockTriangular id := fun i j hij => hWt (by rw [Fin.lt_def] at hij ⊢; exact hij)
    have hdet : V0.det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
      intro r _
      exact diag_ne_zero hb' _
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, htri, fun r => ?_, fun t => ?_⟩
    · show Formalism.UG.ordL ((h⁻¹).1.1 (hi n' (Fin.castLE hle r.rev)) (hi n' (Fin.castLE hle r.rev))) = _
      have e : hi n' (Fin.castLE hle r.rev) = (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev := by
        ext; simp only [hi, lo, Fin.val_rev, Fin.coe_castLE]; omega
      rw [e]
      have a := ordL_of_mul_eq_one (Formalism.UG.P.fSatake_borel_diag_inv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev)
      have b := ordL_rev_diag hv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩)
      change Formalism.UG.ordL (h.1.1 _ _) = - Formalism.UG.ordL ((h⁻¹).1.1 _ _) at a
      linarith
    · ext r c
      simp only [Matrix.mul_apply, Matrix.of_apply]
      split_ifs with hr
      · have hr' : (Fin.castLE hle ⟨r.1, hr⟩ : Fin (n' / 2)) = r := Fin.ext rfl
        let emb : Fin (n / 2) ↪ Fin (n' / 2) := ⟨Fin.castLE hle, Fin.castLE_injective hle⟩
        rw [← Finset.sum_subset (s₁ := Finset.univ.map emb) (Finset.subset_univ _), Finset.sum_map]
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hk : ((emb k : Fin (n' / 2)) : ℕ) < n / 2 := k.2
          rw [dif_pos hk]
          show W r (Fin.castLE hle k) * t ⟨k.1, hk⟩ c = W (Fin.castLE hle ⟨r.1, hr⟩) (Fin.castLE hle k) * t k c
          rw [hr']
        · intro k _ hk
          have : ¬ (k : ℕ) < n / 2 := fun e => hk (Finset.mem_map.2 ⟨⟨k.1, e⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          rw [dif_neg this, mul_zero]
      · refine Finset.sum_eq_zero fun k _ => ?_
        split_ifs with hk
        · rw [hWt (show k < r by rw [Fin.lt_def]; omega), zero_mul]
        · rw [mul_zero]
