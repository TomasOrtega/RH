import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DerivativeRepresentation

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Unfold `midOf`. Rewrite using `[dif_neg]`. Simplify using the standard rewrite rules.
-/
theorem qc_midOf_zero (r : ℕ) : midOf (0 : Fin (r + 1 + 1)) = none := by
  unfold midOf
  rw [dif_neg]
  simp

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_add]`. Distinguish the cases in `h : coeff u f = 0`. Rewrite `hu` using `[h, zero_add]`. Conclude with `hg u hu`.

Conclude with `hf u h`.
-/
theorem qc_rowA_add {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (f g : MvPolynomial (Fin k × Fin n) K) (d : ℕ)
    (hf : RowA a f d) (hg : RowA a g d) : RowA a (f + g) d := by
  intro u hu
  rw [coeff_add] at hu
  by_cases h : coeff u f = 0
  · rw [h, zero_add] at hu
    exact hg u hu
  · exact hf u h

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_smul]`. Conclude with `hf u (fun h => hu (by rw [h, smul_zero]))`.
-/
theorem qc_rowA_smul {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin n) K) (d : ℕ)
    (hf : RowA a f d) : RowA a (c • f) d := by
  intro u hu
  rw [coeff_smul] at hu
  exact hf u (fun h => hu (by rw [h, smul_zero]))

/- English proof (translation)
Introduce `u hu`. Conclude with `absurd (coeff_zero u) hu`.
-/
theorem qc_rowA_zero {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (d : ℕ) :
    RowA a (0 : MvPolynomial (Fin k × Fin n) K) d := by
  intro u hu
  exact absurd (coeff_zero u) hu

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_one]`. Use `split_ifs at hu with h`. Rewrite using `[← h]`. Simplify using `[rowDeg]`.

Conclude with `absurd rfl hu`.
-/
theorem qc_rowA_one {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) : RowA a (1 : MvPolynomial (Fin k × Fin n) K) 0 := by
  classical
  intro u hu
  rw [coeff_one] at hu
  split_ifs at hu with h
  · rw [← h]
    simp [rowDeg]
  · exact absurd rfl hu

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[coeff_X']`. Use `split_ifs at hu with h`. Substitute `h` using the available equality. Break down `v with ⟨b, q⟩` into its components or cases.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `[rowDeg, Finsupp.single_apply]`. Simplify using `[rowDeg, Finsupp.single_apply, Prod.ext_iff, hb]`. Conclude with `absurd rfl hu`.
-/
private theorem rowA_X {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (v : Fin k × Fin n) :
    RowA a (X v : MvPolynomial (Fin k × Fin n) K) (if v.1 = a then 1 else 0) := by
  intro u hu
  rw [coeff_X'] at hu
  split_ifs at hu with h
  · subst h
    rcases v with ⟨b, q⟩
    by_cases hb : b = a
    · subst hb
      simp [rowDeg, Finsupp.single_apply]
    · simp [rowDeg, Finsupp.single_apply, Prod.ext_iff, hb]
  · exact absurd rfl hu

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using qc_rowA_one (K := K) (n := n) a`. Consider the case `insert j S hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj]`. Conclude with `rowA_mul a _ _ _ _ (rowA_X a (g j)) ih`.
-/
private theorem degA_prod_X_eq_card_first_coord_eq {K : Type} [CommRing K] {k n m : ℕ} (a : Fin k) (g : Fin m → Fin k × Fin n)
    (S : Finset (Fin m)) :
    RowA a (∏ i ∈ S, (X (g i) : MvPolynomial (Fin k × Fin n) K)) (∑ i ∈ S, if (g i).1 = a then 1 else 0) := by
  induction S using Finset.induction_on with
  | empty => simpa using qc_rowA_one (K := K) (n := n) a
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact rowA_mul a _ _ _ _ (rowA_X a (g j)) ih

/- English proof (translation)
Introduce `u hu` and use `hf u (h u hu)`.
-/
private theorem rowA_of_support_subset {K : Type} [CommRing K] {k n : ℕ} (a : Fin k)
    (f g : MvPolynomial (Fin k × Fin n) K) (d : ℕ)
    (h : ∀ u, coeff u g ≠ 0 → coeff u f ≠ 0) (hf : RowA a f d) : RowA a g d :=
  fun u hu => hf u (h u hu)

/- English proof (translation)
Unfold `initMinor`. Rewrite using `[Matrix.det_apply]`. Use `Finset.sum_induction _ (fun f => RowA a f d) (fun f g hf hg => qc_rowA_add a f g d hf hg) (qc_rowA_zero a d) ?_` and prove the remaining obligations. Introduce `σ _`. Establish `key` using `degA_prod_X_eq_card_first_coord_eq (K := A) a (fun i => (I (σ i), Fin.castLE hs i)) Finset.univ`.

Establish `hdeg : (∑ i ∈ Finset.univ, if ((fun i => (I (σ i), Fin.castLE hs i)) i).1 = a then 1 else 0) = d`. Rewrite using `[← hd, Finset.sum_apply]`. Simplify using `only [Pi.single_apply, eq_comm (a := a)]`. Conclude with `Equiv.sum_comp σ (fun p => if I p = a then (1 : ℕ) else 0)`. Rewrite `key` using `[hdeg]`.

Use `rowA_of_support_subset a _ _ d ?_ key` and prove the remaining obligations. Introduce `u hu h`. Apply `hu` to reduce the goal to its premises. Simplify using `only [Matrix.of_apply] at h ⊢`. Rewrite using `[Units.smul_def, coeff_smul, h, smul_zero]`.
-/
theorem qc_rowA_minor (A : Type) [CommRing A] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) (a : Fin r) (d : ℕ)
    (hd : (∑ p : Fin s, (Pi.single (I p) 1 : Fin r → ℕ)) a = d) : RowA a (initMinor A (n := n) I hs) d := by
  unfold initMinor
  rw [Matrix.det_apply]
  refine Finset.sum_induction _ (fun f => RowA a f d) (fun f g hf hg => qc_rowA_add a f g d hf hg) (qc_rowA_zero a d) ?_
  intro σ _
  have key := degA_prod_X_eq_card_first_coord_eq (K := A) a (fun i => (I (σ i), Fin.castLE hs i)) Finset.univ
  have hdeg : (∑ i ∈ Finset.univ, if ((fun i => (I (σ i), Fin.castLE hs i)) i).1 = a then 1 else 0) = d := by
    rw [← hd, Finset.sum_apply]
    simp only [Pi.single_apply, eq_comm (a := a)]
    exact Equiv.sum_comp σ (fun p => if I p = a then (1 : ℕ) else 0)
  rw [hdeg] at key
  refine rowA_of_support_subset a _ _ d ?_ key
  intro u hu h
  apply hu
  simp only [Matrix.of_apply] at h ⊢
  rw [Units.smul_def, coeff_smul, h, smul_zero]

def qcRes (A : Type) [CommRing A] (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A →+* MvPolynomial (Fin r × Fin r) A :=
  (eval (idPoint (MvPolynomial (Fin r × Fin r) A) (r + 1 + 1) (r + 1 + 1))).comp (subY A r).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qcRes_apply (A : Type) [CommRing A] (r : ℕ) (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    qcRes A r s = resY A r s := rfl

/- English proof (translation)
Rewrite using `[← qcRes_apply, map_one]`.
-/
theorem qc_resY_one (A : Type) [CommRing A] (r : ℕ) : resY A r 1 = 1 := by
  rw [← qcRes_apply, map_one]

/- English proof (translation)
Rewrite using `[← qcRes_apply, map_zero]`.
-/
theorem qc_resY_zero (A : Type) [CommRing A] (r : ℕ) : resY A r 0 = 0 := by
  rw [← qcRes_apply, map_zero]

/- English proof (translation)
Simplify using `only [resY, map_add]`.
-/
theorem qc_resY_add (A : Type) [CommRing A] (r : ℕ) (s t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    resY A r (s + t) = resY A r s + resY A r t := by
  simp only [resY, map_add]

/- English proof (translation)
Rewrite using `[smul_eq_C_mul, smul_eq_C_mul, resY_mul]`. Simplify using `[resY, subY]`.
-/
theorem qc_resY_smul (A : Type) [CommRing A] (r : ℕ) (c : A) (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    resY A r (c • s) = c • resY A r s := by
  rw [smul_eq_C_mul, smul_eq_C_mul, resY_mul]
  simp [resY, subY]

/- English proof (translation)
Simplify using `[resY, subY, qc_midOf_zero, idPoint]`.
-/
theorem qc_resY_X_zero (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) :
    resY A r (X (a, 0)) = if a.val = 0 then 1 else 0 := by
  simp [resY, subY, qc_midOf_zero, idPoint]

/- English proof (translation)
Simplify using `[resY, subY, midOf_midI, idPoint, map_sum]`.
-/
theorem qc_resY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    resY A r (X (a, midI r j)) = ∑ i : Fin r, X (i, j) * (if a.val = (midI r i).val then 1 else 0) := by
  simp [resY, subY, midOf_midI, idPoint, map_sum]

/- English proof (translation)
Rewrite using `[qc_resY_X_mid]`. Simplify using `[midI_val, Fin.val_inj]`.
-/
theorem qc_resY_X_mid_mid (A : Type) [CommRing A] (r : ℕ) (i j : Fin r) :
    resY A r (X (midI r i, midI r j)) = X (i, j) := by
  rw [qc_resY_X_mid]
  simp [midI_val, Fin.val_inj]

def qcLiftI {r s : ℕ} (I : Fin s → Fin r) : Fin (s + 1) → Fin (r + 1 + 1) := Fin.cons 0 (fun p => midI r (I p))

/- English proof (translation)
Use `ext`. Simplify using `[midI_val]`.
-/
private theorem castLE_succ_eq_midI_castLE {r s : ℕ} (hs : s ≤ r) (hs' : s + 1 ≤ r + 1 + 1) (q : Fin s) :
    Fin.castLE hs' q.succ = midI r (Fin.castLE hs q) := by
  ext
  simp [midI_val]

/- English proof (translation)
Establish `h0 : Fin.castLE hs' (0 : Fin (s + 1)) = 0`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[← qcRes_apply, initMinor, RingHom.map_det, Matrix.det_succ_row_zero, Fin.sum_univ_succ]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, qcRes_apply, qcLiftI, Fin.cons_zero, h0, castLE_succ_eq_midI_castLE hs hs', qc_resY_X_zero, qc_resY_X_mid]`.

Simplify using `[midI_val]`. Unfold `initMinor`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[Matrix.submatrix_apply, Fin.cons_succ, castLE_succ_eq_midI_castLE hs hs', qc_resY_X_mid_mid, qcRes_apply]`.
-/
theorem qc_res_minor (A : Type) [CommRing A] (r s : ℕ) (hs : s ≤ r) (hs' : s + 1 ≤ r + 1 + 1) (I : Fin s → Fin r) :
    resY A r (initMinor A (qcLiftI I) hs') = initMinor A I hs := by
  have h0 : Fin.castLE hs' (0 : Fin (s + 1)) = 0 := by
    ext
    simp
  rw [← qcRes_apply, initMinor, RingHom.map_det, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, qcRes_apply, qcLiftI, Fin.cons_zero,
    h0, castLE_succ_eq_midI_castLE hs hs', qc_resY_X_zero, qc_resY_X_mid]
  simp [midI_val]
  unfold initMinor
  congr 1
  ext p q
  simp [Matrix.submatrix_apply, Fin.cons_succ, castLE_succ_eq_midI_castLE hs hs', qc_resY_X_mid_mid, qcRes_apply]

/- English proof (translation)
Establish `hne : ∀ j : Fin r, (0 : Fin (r + 1 + 1)) ≠ midI r j` using `fun j => (midI_ne_zero r j).symm`. Apply `qc_rowA_minor` to reduce the goal to its premises. Rewrite using `[Finset.sum_apply, Fin.sum_univ_succ]`. Simplify using `[qcLiftI, Pi.single_apply, hne]`.
-/
theorem initial_minor_lift_first_entry (A : Type) [CommRing A] (r s : ℕ) (hs' : s + 1 ≤ r + 1 + 1) (I : Fin s → Fin r) :
    RowA 0 (initMinor A (qcLiftI I) hs') 1 := by
  have hne : ∀ j : Fin r, (0 : Fin (r + 1 + 1)) ≠ midI r j := fun j => (midI_ne_zero r j).symm
  apply qc_rowA_minor
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp [qcLiftI, Pi.single_apply, hne]

/- English proof (translation)
Establish `hl : Fin.last (r + 1) ≠ 0`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Establish `hne : ∀ j : Fin r, Fin.last (r + 1) ≠ midI r j` using `fun j => (midI_ne_last r j).symm`.

Apply `qc_rowA_minor` to reduce the goal to its premises. Rewrite using `[Finset.sum_apply, Fin.sum_univ_succ]`. Simplify using `[qcLiftI, Pi.single_apply, hne, hl]`.
-/
theorem qc_rowL_lift (A : Type) [CommRing A] (r s : ℕ) (hs' : s + 1 ≤ r + 1 + 1) (I : Fin s → Fin r) :
    RowA (Fin.last (r + 1)) (initMinor A (qcLiftI I) hs') 0 := by
  have hl : Fin.last (r + 1) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hne : ∀ j : Fin r, Fin.last (r + 1) ≠ midI r j := fun j => (midI_ne_last r j).symm
  apply qc_rowA_minor
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp [qcLiftI, Pi.single_apply, hne, hl]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `shapeC`. Simplify using `only [Pi.add_apply]`. Use `split_ifs`. Both sides reduce to the same expression.

Apply the tactic sequence `cases h : midOf t <;> simp`.
-/
theorem qc_shapeC_add {r : ℕ} (c c' : ℕ) (β β' : Fin r → ℕ) :
    shapeC c β + shapeC c' β' = shapeC (c + c') (β + β') := by
  funext t
  unfold shapeC
  simp only [Pi.add_apply]
  split_ifs
  · rfl
  · cases h : midOf t <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `shapeC`. Use `split_ifs`. Both sides reduce to the same expression. Apply the tactic sequence `cases h : midOf t <;> rfl`.
-/
theorem qc_shapeC_zero (r : ℕ) : shapeC 0 (0 : Fin r → ℕ) = 0 := by
  funext t
  unfold shapeC
  split_ifs
  · rfl
  · cases h : midOf t <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `ht` using `t.isLt`. Unfold `shapeC qcOm`. Distinguish the cases in `h0 : t = 0`. Substitute `h0` using the available equality.

Simplify using the standard rewrite rules. Establish `h0' : t.val ≠ 0` using `fun h => h0 (Fin.ext h)`. Rewrite using `[if_neg h0]`. Unfold `midOf`. Distinguish the cases in `h1 : 0 < t.val ∧ t.val < r + 1`.

Rewrite using `[dif_pos h1]`. Simplify using `only [Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[dif_neg h1]`. Simplify using `only`.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem qc_shapeC_om (r s : ℕ) (hs : s ≤ r) : shapeC 1 (qcOm r s) = qcOm (r + 1 + 1) (s + 1) := by
  funext t
  have ht := t.isLt
  unfold shapeC qcOm
  by_cases h0 : t = 0
  · subst h0
    simp
  · have h0' : t.val ≠ 0 := fun h => h0 (Fin.ext h)
    rw [if_neg h0]
    unfold midOf
    by_cases h1 : 0 < t.val ∧ t.val < r + 1
    · rw [dif_pos h1]
      simp only [Fin.val_mk]
      split_ifs <;> omega
    · rw [dif_neg h1]
      simp only
      split_ifs <;> omega

/- English proof (translation)
Rewrite using `[qc_shapeC_om r s hs]`. Conclude with `qc_initMinor_mem A (qcLiftI I) hs'`.
-/
theorem qc_lift_mem (A : Type) [CommRing A] (r s : ℕ) (hs : s ≤ r) (hs' : s + 1 ≤ r + 1 + 1) (I : Fin s → Fin r) :
    initMinor A (qcLiftI I) hs' ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) (shapeC 1 (qcOm r s)) := by
  rw [qc_shapeC_om r s hs]
  exact qc_initMinor_mem A (qcLiftI I) hs'

/- English proof (translation)
Introduce `K`. Proceed by induction on `K with`. Consider the case `zero`. Introduce `sz hsz I`. Use `⟨0, 1, ?_, fun _ => rfl, ?_, qc_rowA_one _, ?_, ?_⟩` and prove the remaining obligations.

Introduce `t _`. Rewrite using `[qc_shapeDeg_zero]`. Both sides reduce to the same expression. Rewrite using `[qc_shapeDeg_zero, qc_shapeC_zero]`. Use `qc_pow_mem A (r + 1 + 1) (r + 1 + 1) 0 0 (Submodule.zero_mem _) 0` as an intermediate fact.

Simplify using `using this`. Use `qc_rowA_one (K := A) (n := r + 1 + 1) (Fin.last (r + 1))` as an intermediate fact. Conclude with `this`. Rewrite using `[qc_resY_one, qc_bidet_zero]`. Consider the case `succ K ih`.

Introduce `sz hsz I`. Take `⟨d, s, hd, hd0, hs, h0, hl, hres⟩` from `ih (fun k => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ)`. Establish `hs' : sz 0 + 1 ≤ r + 1 + 1`. Use `hsz 0` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[qc_bidet_succ]`. Distinguish the cases in `hz : sz 0 = 0`. Use `⟨d, s, ?_, hd0, ?_, h0, hl, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Rewrite using `[qc_shapeDeg_succ, Pi.add_apply, hd t ht]`.

Simplify using `[qcOm, hz]`. Rewrite using `[qc_shapeDeg_succ, hz, qcOm_zero, zero_add]`. Conclude with `hs`. Rewrite using `[hres, qc_empty_minor A (sz 0) _ (I 0) hz, one_mul]`. Use `⟨d + 1, initMinor A (qcLiftI (I 0)) hs' * s, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `t ht`. Rewrite using `[qc_shapeDeg_succ, Pi.add_apply, hd t ht]`. Simplify using `only [qcOm, ht]`. Rewrite using `[if_pos (Nat.pos_of_ne_zero hz)]`. Use linear arithmetic over natural numbers and integers.

Introduce `hr`. It suffices to derive a contradiction. Use `hsz 0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[qc_shapeDeg_succ, add_comm d 1, ← qc_shapeC_add]`.

Conclude with `Formalism.MainNotions.flipOneThree.Pf.dualWeyl_mul A _ _ _ _ (qc_lift_mem A r (sz 0) (hsz 0) hs' (I 0)) hs`. Rewrite using `[add_comm d 1]`. Apply the tactic sequence `exact rowA_mul _ _ _ _ _ (initial_minor_lift_first_entry A r (sz 0) hs' (I 0)) h0`. Conclude with `rowA_mul _ _ _ _ _ (qc_rowL_lift A r (sz 0) hs' (I 0)) hl`. Rewrite using `[resY_mul, qc_res_minor A r (sz 0) (hsz 0) hs' (I 0), hres]`.
-/
theorem qc_lift_bidet (A : Type) [CommRing A] (r : ℕ) : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r)
    (I : ∀ k, Fin (sz k) → Fin r),
    ∃ (d : ℕ) (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
      (∀ t : Fin r, t.val = 0 → shapeDeg sz t = d) ∧ (r = 0 → d = 0) ∧
      s ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) (shapeC d (shapeDeg sz)) ∧ RowA 0 s d ∧ RowA (Fin.last (r + 1)) s 0 ∧
      resY A r s = bideterminant A sz hsz I := by
  intro K
  induction K with
  | zero =>
    intro sz hsz I
    refine ⟨0, 1, ?_, fun _ => rfl, ?_, qc_rowA_one _, ?_, ?_⟩
    · intro t _
      rw [qc_shapeDeg_zero]
      rfl
    · rw [qc_shapeDeg_zero, qc_shapeC_zero]
      have := qc_pow_mem A (r + 1 + 1) (r + 1 + 1) 0 0 (Submodule.zero_mem _) 0
      simpa using this
    · have := qc_rowA_one (K := A) (n := r + 1 + 1) (Fin.last (r + 1))
      exact this
    · rw [qc_resY_one, qc_bidet_zero]
  | succ K ih =>
    intro sz hsz I
    obtain ⟨d, s, hd, hd0, hs, h0, hl, hres⟩ := ih (fun k => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ)
    have hs' : sz 0 + 1 ≤ r + 1 + 1 := by
      have := hsz 0
      omega
    rw [qc_bidet_succ]
    by_cases hz : sz 0 = 0
    · refine ⟨d, s, ?_, hd0, ?_, h0, hl, ?_⟩
      · intro t ht
        rw [qc_shapeDeg_succ, Pi.add_apply, hd t ht]
        simp [qcOm, hz]
      · rw [qc_shapeDeg_succ, hz, qcOm_zero, zero_add]
        exact hs
      · rw [hres, qc_empty_minor A (sz 0) _ (I 0) hz, one_mul]
    · refine ⟨d + 1, initMinor A (qcLiftI (I 0)) hs' * s, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro t ht
        rw [qc_shapeDeg_succ, Pi.add_apply, hd t ht]
        simp only [qcOm, ht]
        rw [if_pos (Nat.pos_of_ne_zero hz)]
        omega
      · intro hr
        exfalso
        have := hsz 0
        omega
      · rw [qc_shapeDeg_succ, add_comm d 1, ← qc_shapeC_add]
        exact Formalism.MainNotions.flipOneThree.Pf.dualWeyl_mul A _ _ _ _ (qc_lift_mem A r (sz 0) (hsz 0) hs' (I 0)) hs
      · rw [add_comm d 1]
        exact rowA_mul _ _ _ _ _ (initial_minor_lift_first_entry A r (sz 0) hs' (I 0)) h0
      · exact rowA_mul _ _ _ _ _ (qc_rowL_lift A r (sz 0) hs' (I 0)) hl
      · rw [resY_mul, qc_res_minor A r (sz 0) (hsz 0) hs' (I 0), hres]

/- English proof (translation)
Introduce `e`. Establish `hs' : 0 + 1 ≤ r + 1 + 1` using `by omega`. Establish `hmem` using `qc_lift_mem A r 0 (Nat.zero_le r) hs' Fin.elim0`. Rewrite `hmem` using `[qcOm_zero]`. Establish `hres : resY A r (initMinor A (qcLiftI (Fin.elim0 : Fin 0 → Fin r)) hs') = 1`.

Rewrite using `[qc_res_minor A r 0 (Nat.zero_le r) hs' Fin.elim0]`. Conclude with `qc_empty_minor A 0 _ _ rfl`. Use `⟨(initMinor A (qcLiftI (Fin.elim0 : Fin 0 → Fin r)) hs') ^ e, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `qc_pow_mem A (r + 1 + 1) (r + 1 + 1) _ _ hmem e` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Unfold `shapeC`. Use `split_ifs`. Simplify using the standard rewrite rules.

Apply the tactic sequence `cases midOf t <;> simp`. Proceed by induction on `e with`. Consider the case `zero => simpa using qc_rowA_one (K := A) (n := r + 1 + 1) (0 : Fin (r + 1 + 1))`. Consider the case `succ e ih`. Rewrite using `[pow_succ]`.

Apply the tactic sequence `exact rowA_mul _ _ _ _ _ ih (initial_minor_lift_first_entry A r 0 hs' Fin.elim0)`. Proceed by induction on `e with`. Consider the case `zero => simpa using qc_rowA_one (K := A) (n := r + 1 + 1) (Fin.last (r + 1))`. Consider the case `succ e ih`. Rewrite using `[pow_succ]`.

Conclude with `rowA_mul _ _ _ _ _ ih (qc_rowL_lift A r 0 hs' Fin.elim0)`. Rewrite using `[← qcRes_apply, map_pow, qcRes_apply, hres, one_pow]`.
-/
theorem qc_pad (A : Type) [CommRing A] (r : ℕ) : ∀ e : ℕ,
    ∃ z ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) (shapeC e (0 : Fin r → ℕ)), RowA 0 z e ∧ RowA (Fin.last (r + 1)) z 0 ∧
      resY A r z = 1 := by
  intro e
  have hs' : 0 + 1 ≤ r + 1 + 1 := by omega
  have hmem := qc_lift_mem A r 0 (Nat.zero_le r) hs' Fin.elim0
  rw [qcOm_zero] at hmem
  have hres : resY A r (initMinor A (qcLiftI (Fin.elim0 : Fin 0 → Fin r)) hs') = 1 := by
    rw [qc_res_minor A r 0 (Nat.zero_le r) hs' Fin.elim0]
    exact qc_empty_minor A 0 _ _ rfl
  refine ⟨(initMinor A (qcLiftI (Fin.elim0 : Fin 0 → Fin r)) hs') ^ e, ?_, ?_, ?_, ?_⟩
  · have := qc_pow_mem A (r + 1 + 1) (r + 1 + 1) _ _ hmem e
    convert this using 2
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold shapeC
    split_ifs
    · simp
    · cases midOf t <;> simp
  · induction e with
    | zero => simpa using qc_rowA_one (K := A) (n := r + 1 + 1) (0 : Fin (r + 1 + 1))
    | succ e ih =>
      rw [pow_succ]
      exact rowA_mul _ _ _ _ _ ih (initial_minor_lift_first_entry A r 0 hs' Fin.elim0)
  · induction e with
    | zero => simpa using qc_rowA_one (K := A) (n := r + 1 + 1) (Fin.last (r + 1))
    | succ e ih =>
      rw [pow_succ]
      exact rowA_mul _ _ _ _ _ ih (qc_rowL_lift A r 0 hs' Fin.elim0)
  · rw [← qcRes_apply, map_pow, qcRes_apply, hres, one_pow]

/- English proof (translation)
Introduce `A _ _ r c β hβ hc u hu`. Rewrite `hu` using `[standardMonomialSpanDomain A r r β]`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, hsh, rfl⟩` from `hx`.

Take `⟨d, s, hd, hd0, hs, h0, hl, hres⟩` from `qc_lift_bidet A r K sz hsz I`. Establish `hdc : d ≤ c`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Rewrite using `[hd0 hr]`. Conclude with `Nat.zero_le c`.

Rewrite using `[← hd ⟨0, hr⟩ rfl, hsh]`. Conclude with `hc ⟨0, hr⟩`. Take `⟨z, hz, hz0, hzl, hzres⟩` from `qc_pad A r (c - d)`. Use `⟨s * z, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Formalism.MainNotions.flipOneThree.Pf.dualWeyl_mul A _ _ _ _ hs hz` as an intermediate fact.

Rewrite `this` using `[qc_shapeC_add, add_zero, Nat.add_sub_cancel' hdc, hsh]`. Then use the resulting hypothesis. Use `rowA_mul _ _ _ _ _ h0 hz0` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel' hdc]`. Then use the resulting hypothesis. Conclude with `rowA_mul _ _ _ _ _ hl hzl`. Rewrite using `[resY_mul, hres, hzres, mul_one]`.

Consider the case `zero`. Conclude with `⟨0, Submodule.zero_mem _, qc_rowA_zero _ _, qc_rowA_zero _ _, qc_resY_zero A r⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs, h0, hl, hres⟩` from `hx`. Take `⟨t, ht, h0', hl', hres'⟩` from `hy`.

Conclude with `⟨s + t, Submodule.add_mem _ hs ht, qc_rowA_add _ _ _ _ h0 h0', qc_rowA_add _ _ _ _ hl hl', by rw [qc_resY_add, hres, hres']⟩`. Consider the case `smul a x _ hx`. Take `⟨s, hs, h0, hl, hres⟩` from `hx`. Conclude with `⟨a • s, Submodule.smul_mem _ a hs, qc_rowA_smul _ _ _ _ h0, qc_rowA_smul _ _ _ _ hl, by rw [qc_resY_smul, hres]⟩`.
-/
theorem liftP : LiftP := by
  intro A _ _ r c β hβ hc u hu
  rw [standardMonomialSpanDomain A r r β] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
    obtain ⟨d, s, hd, hd0, hs, h0, hl, hres⟩ := qc_lift_bidet A r K sz hsz I
    have hdc : d ≤ c := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · rw [hd0 hr]
        exact Nat.zero_le c
      · rw [← hd ⟨0, hr⟩ rfl, hsh]
        exact hc ⟨0, hr⟩
    obtain ⟨z, hz, hz0, hzl, hzres⟩ := qc_pad A r (c - d)
    refine ⟨s * z, ?_, ?_, ?_, ?_⟩
    · have := Formalism.MainNotions.flipOneThree.Pf.dualWeyl_mul A _ _ _ _ hs hz
      rwa [qc_shapeC_add, add_zero, Nat.add_sub_cancel' hdc, hsh] at this
    · have := rowA_mul _ _ _ _ _ h0 hz0
      rwa [Nat.add_sub_cancel' hdc] at this
    · exact rowA_mul _ _ _ _ _ hl hzl
    · rw [resY_mul, hres, hzres, mul_one]
  | zero =>
    exact ⟨0, Submodule.zero_mem _, qc_rowA_zero _ _, qc_rowA_zero _ _, qc_resY_zero A r⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, h0, hl, hres⟩ := hx
    obtain ⟨t, ht, h0', hl', hres'⟩ := hy
    exact ⟨s + t, Submodule.add_mem _ hs ht, qc_rowA_add _ _ _ _ h0 h0', qc_rowA_add _ _ _ _ hl hl',
      by rw [qc_resY_add, hres, hres']⟩
  | smul a x _ hx =>
    obtain ⟨s, hs, h0, hl, hres⟩ := hx
    exact ⟨a • s, Submodule.smul_mem _ a hs, qc_rowA_smul _ _ _ _ h0, qc_rowA_smul _ _ _ _ hl,
      by rw [qc_resY_smul, hres]⟩

end Formalism.MainNotions.flipOneThree.Pf

end
