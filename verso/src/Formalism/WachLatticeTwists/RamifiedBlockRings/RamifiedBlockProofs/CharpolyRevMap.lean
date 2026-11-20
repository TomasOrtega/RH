import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdempotentImageSurjective

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cornerIdem : CornerIdempotentInSubalgebra := by
  unfold CornerIdempotentInSubalgebra
  intro k _ n ι _ _ B hn hsurj A
  classical
  obtain ⟨p, q, hpq⟩ : ∃ p q : n, p ≠ q := Fintype.exists_pair_of_one_lt_card hn
  have hc : ((Matrix.single p p (1 : k) - Matrix.single q q 1 : Matrix n n k), (0 : ι → k)) ∈ B := by
    obtain ⟨z1, hz1B, hz1⟩ := hsurj (Matrix.single p q 1)
    obtain ⟨z2, hz2B, hz2⟩ := hsurj (Matrix.single q p 1)
    have := B.sub_mem (B.mul_mem hz1B hz2B) (B.mul_mem hz2B hz1B)
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [hz1, hz2, Matrix.single_mul_single_same]
    · simp [mul_comm]
  have hij : ∀ i j, ((Matrix.single i j (1 : k) : Matrix n n k), (0 : ι → k)) ∈ B := by
    intro i j
    obtain ⟨w1, hw1B, hw1⟩ := hsurj (Matrix.single i p 1)
    obtain ⟨w2, hw2B, hw2⟩ := hsurj (Matrix.single p j 1)
    have := B.mul_mem (B.mul_mem hw1B hc) hw2B
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [hw1, hw2, Matrix.mul_sub, Matrix.sub_mul, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne, hpq]
    · simp
  have hA : (A, (0 : ι → k)) = ∑ i, ∑ j, A i j • ((Matrix.single i j (1 : k) : Matrix n n k), (0 : ι → k)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.smul_fst, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single A
    · simp [Prod.snd_sum]
  rw [hA]
  exact B.sum_mem fun i _ => B.sum_mem fun j _ => B.smul_mem (hij i j) _

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem charpolyRev_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*} [Fintype d]
    [DecidableEq d] (M : Matrix d d A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem nilConst : StatNilConst := by
  intro O _ _ X T d _ _ hT a ha y hy x
  have hrev : Matrix.charpolyRev ((a x).map (IsLocalRing.residue O)) = 1 := by
    have h1 : Matrix.charpolyRev ((a x).map (IsLocalRing.residue O)) =
        Matrix.charpolyRev ((a y).map (IsLocalRing.residue O)) := by
      rw [← charpolyRev_map, ← charpolyRev_map]
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      exact resConst O X T hT _ (ha k) x y
    rw [h1, hy]
    simp [Matrix.charpolyRev]
  set M := (a x).map (IsLocalRing.residue O) with hM
  have hcp : M.charpoly = Polynomial.X ^ Fintype.card d := by
    have hdeg : M.charpoly.natDegree = Fintype.card d := Matrix.charpoly_natDegree_eq_dim M
    ext k
    rw [Polynomial.coeff_X_pow]
    by_cases hk : k ≤ Fintype.card d
    · have h2 : M.charpoly.reverse.coeff (Fintype.card d - k) = M.charpoly.coeff k := by
        rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le (Nat.sub_le _ _)]
        congr 1; omega
      rw [← h2, Matrix.reverse_charpoly, hrev, Polynomial.coeff_one]
      by_cases hk2 : k = Fintype.card d
      · simp [hk2]
      · rw [if_neg (by omega), if_neg hk2]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), if_neg (by omega)]
  have hch := Matrix.aeval_self_charpoly M
  rw [hcp] at hch
  have h5 : ((a x) ^ Fintype.card d).map (IsLocalRing.residue O) = M ^ Fintype.card d := by
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  rw [h5]
  simpa using hch

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Use linear arithmetic over natural numbers and integers. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tailProd {M : Type*} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ((List.range t).tail.map f).prod = ∏ i ∈ Finset.Ioo 0 t, f i := by
  cases t with
  | zero => simp
  | succ n =>
    rw [List.range_succ_eq_map, List.tail_cons, List.map_map, ← List.prod_toFinset _ List.nodup_range,
      List.toFinset_range]
    have hI : Finset.Ioo 0 (n + 1) = (Finset.range n).map ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext i
      simp only [Finset.mem_Ioo, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨i - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩
        omega
    (rw [hI, Finset.prod_map]) <;> rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem listDiag {A : Type*} [CommRing A] {d : Type*} [Fintype d] [DecidableEq d] (f : ℕ → d → A)
    (l : List ℕ) :
    (l.map fun i => (Matrix.diagonal (f i) : Matrix d d A)).prod =
      Matrix.diagonal fun a => (l.map fun i => f i a).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, Matrix.diagonal_mul_diagonal]

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Simplify by unfolding definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eDiag : StatEDiag := by
  unfold StatEDiag
  intro A _ d _ _ S β t α
  dsimp only
  have hfac : ∀ i, (Matrix.diagonal (fun a => if S a then β a else 0) -
      α i • Matrix.diagonal (fun a => if S a then (1 : A) else 0)) =
      Matrix.diagonal (fun a => if S a then β a - α i else 0) := by
    intro i
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hS : S a <;> simp [hS]
    · simp [Matrix.diagonal_apply_ne _ hab]
  simp_rw [hfac]
  rw [listDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases hS : S a
  · simp only [hS, ↓reduceIte, one_mul]
    exact tailProd _ t
  · simp [hS]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
