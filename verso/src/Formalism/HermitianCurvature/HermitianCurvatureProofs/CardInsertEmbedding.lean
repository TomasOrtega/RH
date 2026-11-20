import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

namespace CardInsertEmbedding

open C2x2

/- English proof (translation)
Establish `hk : k = n` using `by rw [← h, c2x3_iSet_card hn]`. Substitute `hk` using the available equality. Use `Finset.orderEmbOfFin_unique h (f := fun t : Fin k => (⟨t.val, by omega⟩ : Fin m)) (fun t => by simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact t.isLt) (fun x y hxy => hxy)` as an intermediate fact. Rewrite using `[← this]`.
-/
lemma iemb {m n k : ℕ} (hn : n ≤ m) (h : (C2.iSet m n).card = k) (t : Fin k) :
    ((C2.iSet m n).orderEmbOfFin h t).val = t.val := by
  have hk : k = n := by rw [← h, c2x3_iSet_card hn]
  subst hk
  have := Finset.orderEmbOfFin_unique h (f := fun t : Fin k => (⟨t.val, by omega⟩ : Fin m))
    (fun t => by simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact t.isLt)
    (fun x y hxy => hxy)
  rw [← this]

/- English proof (translation)
Rewrite using `[Finset.card_insert_of_notMem, c2x3_iSet_card hn]`. Simplify using `[C2.iSet]`. Use linear arithmetic over natural numbers and integers.
-/
lemma card_ins {m n : ℕ} (b : Fin m) (hb : n < b.val) (hn : n ≤ m) :
    (insert b (C2.iSet m n)).card = n + 1 := by
  rw [Finset.card_insert_of_notMem, c2x3_iSet_card hn]
  simp [C2.iSet]; omega

/- English proof (translation)
Establish `hk : k = n + 1` using `by rw [← h, card_ins b hb (by omega)]`. Substitute `hk` using the available equality. Use `Finset.orderEmbOfFin_unique h (f := fun t : Fin (n + 1) => if ht : t.val < n then (⟨t.val, by omega⟩ : Fin m) else b) (fun t => by beta_reduce split_ifs with ht` as an intermediate fact. Conclude with `Finset.mem_insert_of_mem (by simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht)`. Conclude with `Finset.mem_insert_self _ _)`.

Use the proof step `(fun x y hxy => by beta_reduce`. Rewrite `hxy` using `[Fin.lt_def]`. Use `split_ifs with h1 h2 h2`. Rewrite using `[Fin.lt_def]`. Conclude with `hxy`.

Rewrite using `[Fin.lt_def]`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use the proof step `omega)`.

Rewrite using `[← this]`.
-/
lemma cemb {m n k : ℕ} (b : Fin m) (hb : n < b.val) (h : (insert b (C2.iSet m n)).card = k) (t : Fin k) :
    (insert b (C2.iSet m n)).orderEmbOfFin h t = if ht : t.val < n then ⟨t.val, by omega⟩ else b := by
  have hk : k = n + 1 := by rw [← h, card_ins b hb (by omega)]
  subst hk
  have := Finset.orderEmbOfFin_unique h
    (f := fun t : Fin (n + 1) => if ht : t.val < n then (⟨t.val, by omega⟩ : Fin m) else b)
    (fun t => by
      beta_reduce
      split_ifs with ht
      · exact Finset.mem_insert_of_mem (by simp only [C2.iSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht)
      · exact Finset.mem_insert_self _ _)
    (fun x y hxy => by
      beta_reduce
      rw [Fin.lt_def] at hxy
      split_ifs with h1 h2 h2
      · rw [Fin.lt_def]; exact hxy
      · rw [Fin.lt_def]; simp only; omega
      · omega
      · omega)
  rw [← this]

/- English proof (translation)
Rewrite using `[sum_fin_castLE hkm g hg]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Use `congr 1`. Conclude with `Fin.ext (he t).symm`.
-/
lemma sum_emb {m k : ℕ} (hkm : k ≤ m) (e : Fin k → Fin m) (he : ∀ t, (e t).val = t.val) (g : Fin m → ℂ)
    (hg : ∀ j : Fin m, k ≤ j.val → g j = 0) : ∑ j, g j = ∑ t, g (e t) := by
  rw [sum_fin_castLE hkm g hg]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  congr 1; exact Fin.ext (he t).symm

/- English proof (translation)
Use extensionality with `t s`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Take `⟨j0, hj0, hw⟩` from `hR t`. Rewrite using `[sum_emb (by omega) eI hI]`. Introduce `j hj`.

Simplify using `only [C2.monoP, Matrix.of_apply]`. Rewrite using `[if_neg, zero_mul]`. Introduce `e`. Rewrite `e` using `[← hw]`. Use `w.injective e` as an intermediate fact.

Rewrite `hj` using `[← this]`. Use linear arithmetic over natural numbers and integers.
-/
lemma submatrix_monomialMatrix_mul {m k n : ℕ} (hkn : k = n) (hnm : n ≤ m) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) (eR eI f : Fin k → Fin m) (hI : ∀ t, (eI t).val = t.val)
    (hR : ∀ t, ∃ j0 : Fin m, j0.val < n ∧ w j0 = eR t) :
    (C2.monoP w d * M).submatrix eR f = (C2.monoP w d).submatrix eR eI * M.submatrix eI f := by
  ext t s
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  obtain ⟨j0, hj0, hw⟩ := hR t
  rw [sum_emb (by omega) eI hI]
  intro j hj
  simp only [C2.monoP, Matrix.of_apply]
  rw [if_neg, zero_mul]
  intro e; rw [← hw] at e; have := w.injective e; rw [← this] at hj; omega

/- English proof (translation)
Use extensionality with `t s`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Rewrite using `[sum_emb hkm eI hI]`. Introduce `j hj`. Rewrite using `[hL _ _ (by rw [Fin.lt_def, hI]; omega), zero_mul]`.
-/
lemma L_mul_sub {m k : ℕ} (hkm : k ≤ m) (L U : Matrix (Fin m) (Fin m) ℂ) (hL : ∀ i j, i < j → L i j = 0)
    (eI f : Fin k → Fin m) (hI : ∀ t, (eI t).val = t.val) :
    (L * U).submatrix eI f = L.submatrix eI eI * U.submatrix eI f := by
  ext t s
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_emb hkm eI hI]
  intro j hj
  rw [hL _ _ (by rw [Fin.lt_def, hI]; omega), zero_mul]

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Simplify using `only [Matrix.submatrix_apply, hl.2, Finset.prod_const_one]`. Introduce `t t' h`. Simplify using `only [Matrix.submatrix_apply]`. Apply `hl.1` to reduce the goal to its premises.

Rewrite using `[Fin.lt_def, hI, hI]`. Conclude with `OrderDual.toDual_lt_toDual.mp h`.
-/
lemma det_lt_sub {m k : ℕ} (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) (eI : Fin k → Fin m)
    (hI : ∀ t, (eI t).val = t.val) : (l.submatrix eI eI).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp only [Matrix.submatrix_apply, hl.2, Finset.prod_const_one]
  · intro t t' h
    simp only [Matrix.submatrix_apply]
    apply hl.1
    rw [Fin.lt_def, hI, hI]
    exact OrderDual.toDual_lt_toDual.mp h

end CardInsertEmbedding

end Formalism.FourierDecayAlt.P
