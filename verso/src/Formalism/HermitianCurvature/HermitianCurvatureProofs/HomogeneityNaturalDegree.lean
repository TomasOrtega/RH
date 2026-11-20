import Formalism.HermitianCurvature.BigCellVanishingOfCommute

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

/- English proof (translation)
Take `⟨q, hq, hP⟩` from `h`. Conclude with `⟨q, hq.trans hab, hP⟩`.
-/
theorem pd_mono {a b : ℕ} (hab : a ≤ b) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

/- English proof (translation)
Use `⟨MvPolynomial.C c, ?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.totalDegree_C]`. Conclude with `Nat.zero_le _`. Simplify using the standard rewrite rules.
-/
theorem pd_const (c : ℂ) (d : ℕ) : U.IsPolyDeg (N := N) d (fun _ => c) := by
  refine ⟨MvPolynomial.C c, ?_, fun g => ?_⟩
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  · simp

/- English proof (translation)
Use `⟨MvPolynomial.X (Sum.inl (i, j)), ?_, fun g => ?_⟩` and prove the remaining obligations. Conclude with `(MvPolynomial.totalDegree_X _).le`. Simplify using the standard rewrite rules.
-/
theorem pd_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g i j) := by
  refine ⟨MvPolynomial.X (Sum.inl (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

/- English proof (translation)
Use `⟨MvPolynomial.X (Sum.inr (i, j)), ?_, fun g => ?_⟩` and prove the remaining obligations. Conclude with `(MvPolynomial.totalDegree_X _).le`. Simplify using the standard rewrite rules.
-/
theorem pd_star_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g i j)) := by
  refine ⟨MvPolynomial.X (Sum.inr (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

/- English proof (translation)
Take `⟨p, hp, hpP⟩` from `hP`. Take `⟨q, hq, hqQ⟩` from `hQ`. Use `⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hpP g, hqQ g, MvPolynomial.eval_add]`.
-/
theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_add]

/- English proof (translation)
Take `⟨p, hp, hpP⟩` from `hP`. Take `⟨q, hq, hqQ⟩` from `hQ`. Use `⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hpP g, hqQ g, MvPolynomial.eval_mul]`.
-/
theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg b Q) :
    U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_mul]

/- English proof (translation)
Take `⟨p, hp, hpP⟩` from `hP`. Take `⟨q, hq, hqQ⟩` from `hQ`. Use `⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hpP g, hqQ g, MvPolynomial.eval_sub]`.
-/
theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_sub]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using pd_const (N := N) 0 a`. Consider the case `insert x s hx ih`. Establish `h1` using `pd_add (h x (Finset.mem_insert_self x s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`. Simplify `h1` using `[Finset.sum_insert hx]`.
-/
theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 0 a
  | insert x s hx ih =>
    have h1 := pd_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert hx] using h1

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using pd_const (N := N) 1 0`. Consider the case `insert x s hx ih`. Establish `h1` using `pd_mul (h x (Finset.mem_insert_self x s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`. Establish `hc : (insert x s).card * a = a + s.card * a`.

Rewrite using `[Finset.card_insert_of_notMem hx]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc]`. Simplify `h1` using `[Finset.prod_insert hx]`.
-/
theorem pd_prod {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg (s.card * a) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 1 0
  | insert x s hx ih =>
    have h1 := pd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hc : (insert x s).card * a = a + s.card * a := by
      rw [Finset.card_insert_of_notMem hx]; ring
    rw [hc]
    simpa [Finset.prod_insert hx] using h1

/- English proof (translation)
Establish `key : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin l))), U.IsPolyDeg l (fun g => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i)`. Introduce `σ _`. Establish `h1` using `pd_mul (pd_const (N := N) ((Equiv.Perm.sign σ : ℤ) : ℂ) 0) (pd_prod (Finset.univ : Finset (Fin l)) (fun i _ => h (σ i) i))`. Use `pd_mono ?_ h1` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `h2` using `pd_sum _ key`. Simplify `h2` using `[Matrix.det_apply']`.
-/
theorem pd_det {l : ℕ} (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin l) (Fin l) ℂ)
    (h : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) : U.IsPolyDeg l (fun g => (M g).det) := by
  have key : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin l))),
      U.IsPolyDeg l (fun g => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i) := by
    intro σ _
    have h1 := pd_mul (pd_const (N := N) ((Equiv.Perm.sign σ : ℤ) : ℂ) 0)
      (pd_prod (Finset.univ : Finset (Fin l)) (fun i _ => h (σ i) i))
    refine pd_mono ?_ h1
    simp
  have h2 := pd_sum _ key
  simpa [Matrix.det_apply'] using h2

end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

namespace Formalism.FourierDecayAlt.P

open PartialDerivativeAlgebra

/- English proof (translation)
Introduce `m m' E _ _ OO h1 h2 w w' Gv T T' th hGv hT hT' _ _`. Simplify using `only [C6.unitOf]`. Rewrite using `[h1, h2, smul_smul, smul_smul]`. Use `congr 1`. Establish `hc : 0 < Real.sqrt (T * T')` using `Real.sqrt_pos.mpr (mul_pos hT hT')`.

Establish `hab : Real.sqrt (T / Gv) * Real.sqrt (T' / Gv) = Real.sqrt (T * T') / Gv`. Rewrite using `[← Real.sqrt_mul (div_nonneg hT.le hGv.le), show T / Gv * (T' / Gv) = (T * T') / (Gv * Gv) by ring, Real.sqrt_div' _ (mul_self_nonneg Gv), Real.sqrt_mul_self hGv.le]`. Establish `hab' : ((Real.sqrt (T / Gv) : ℝ) : ℂ) * ((Real.sqrt (T' / Gv) : ℝ) : ℂ) = ((Real.sqrt (T * T') : ℝ) : ℂ) / (Gv : ℂ)`. Rewrite using `[← Complex.ofReal_mul, hab, Complex.ofReal_div]`. Establish `hc' : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr hc.ne'`.

Establish `hG' : (Gv : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr hGv.ne'`. Rewrite using `[mul_assoc, hab']`. Clear the denominators using the available nonvanishing facts.
-/
theorem homogeneity_natural_degree : C6.SSNatHomog := by
  intro m m' E _ _ OO h1 h2 w w' Gv T T' th hGv hT hT' _ _
  simp only [C6.unitOf]
  rw [h1, h2, smul_smul, smul_smul]
  congr 1
  have hc : 0 < Real.sqrt (T * T') := Real.sqrt_pos.mpr (mul_pos hT hT')
  have hab : Real.sqrt (T / Gv) * Real.sqrt (T' / Gv) = Real.sqrt (T * T') / Gv := by
    rw [← Real.sqrt_mul (div_nonneg hT.le hGv.le),
      show T / Gv * (T' / Gv) = (T * T') / (Gv * Gv) by ring,
      Real.sqrt_div' _ (mul_self_nonneg Gv), Real.sqrt_mul_self hGv.le]
  have hab' : ((Real.sqrt (T / Gv) : ℝ) : ℂ) * ((Real.sqrt (T' / Gv) : ℝ) : ℂ)
      = ((Real.sqrt (T * T') : ℝ) : ℂ) / (Gv : ℂ) := by
    rw [← Complex.ofReal_mul, hab, Complex.ofReal_div]
  have hc' : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hG' : (Gv : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hGv.ne'
  rw [mul_assoc, hab']
  field_simp

/- English proof (translation)
Introduce `s D' hs hD`. Establish `hs0 : s ≠ 0` using `by omega`. Establish `hprim` using `Complex.isPrimitiveRoot_exp s hs0`. Establish `hnd : (Polynomial.nthRoots s D').Nodup` using `hprim.nthRoots_nodup hD`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `G.rootSet`. Rewrite using `[Multiset.toFinset_card_of_nodup hnd, hprim.card_nthRoots D']`. Rewrite using `[if_pos (IsAlgClosed.exists_pow_nat_eq D' (by omega))]`. Introduce `z hz`. Unfold `G.rootSet at hz`.

Rewrite `hz` using `[Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]`. Rewrite using `[← hz, norm_pow, one_div, Real.pow_rpow_inv_natCast (norm_nonneg z) hs0]`.
-/
theorem polynomial_root_facts : C6.RootFacts := by
  intro s D' hs hD
  have hs0 : s ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp s hs0
  have hnd : (Polynomial.nthRoots s D').Nodup := hprim.nthRoots_nodup hD
  refine ⟨?_, ?_⟩
  · unfold G.rootSet
    rw [Multiset.toFinset_card_of_nodup hnd, hprim.card_nthRoots D']
    rw [if_pos (IsAlgClosed.exists_pow_nat_eq D' (by omega))]
  · intro z hz
    unfold G.rootSet at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
    rw [← hz, norm_pow, one_div, Real.pow_rpow_inv_natCast (norm_nonneg z) hs0]

/- English proof (translation)
Introduce `k r z z' hz hz' g ε hε`. Unfold `Gf at hε`. Establish `h0 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩)` using `mul_nonneg (mul_nonneg hz hz') (Complex.normSq_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gram_function_last_minor : C6.GfDlast := by
  intro k r z z' hz hz' g ε hε
  unfold Gf at hε
  have h0 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hz hz') (Complex.normSq_nonneg _)
  linarith

/- English proof (translation)
Apply the tactic sequence `have h := pd_sum (N := M) (Finset.univ : Finset (Fin M)) (P := fun m g => g j m * v m) (a := 1 + 0) (fun m _ => pd_mul (pd_entry j m) (pd_const (v m) 0))`. Simplify `h` using `[Matrix.mulVec, dotProduct]`.
-/
private theorem isPolyDeg_one_mulVec_apply {M : ℕ} (v : Fin M → ℂ) (j : Fin M) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin M) (Fin M) ℂ => Matrix.mulVec g v j) := by
  have h := pd_sum (N := M) (Finset.univ : Finset (Fin M))
    (P := fun m g => g j m * v m) (a := 1 + 0)
    (fun m _ => pd_mul (pd_entry j m) (pd_const (v m) 0))
  simpa [Matrix.mulVec, dotProduct] using h

/- English proof (translation)
Establish `hH : ∀ i, U.IsPolyDeg 1 (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i)`. Introduce `i`. Establish `h` using `pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1))) (P := fun j g => Hpk k r i j * Matrix.mulVec g (fvec k r z' b) j) (a := 0 + 1) (fun j _ => pd_mul (pd_const (Hpk k r i j) 0) (isPolyDeg_one_mulVec_apply _ j))`. Simplify `h` using `[Matrix.mulVec, dotProduct]`. Establish `h` using `pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1))) (P := fun i g => star (fvec k r z a i) * Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) (a := 0 + 1) (fun i _ => pd_mul (pd_const _ 0) (hH i))`.

Simplify `h` using `[Zhat, herm, dotProduct]`.
-/
theorem zhat_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => Zhat k r z z' g a b) := by
  have hH : ∀ i, U.IsPolyDeg 1
      (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) := by
    intro i
    have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
      (P := fun j g => Hpk k r i j * Matrix.mulVec g (fvec k r z' b) j) (a := 0 + 1)
      (fun j _ => pd_mul (pd_const (Hpk k r i j) 0) (isPolyDeg_one_mulVec_apply _ j))
    simpa [Matrix.mulVec, dotProduct] using h
  have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
    (P := fun i g => star (fvec k r z a i) * Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) (a := 0 + 1)
    (fun i _ => pd_mul (pd_const _ 0) (hH i))
  simpa [Zhat, herm, dotProduct] using h

/- English proof (translation)
Take `⟨q, hq, hP⟩` from `h`. Use `⟨rename Sum.swap (map (starRingEnd ℂ) q), ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `hm : (map (starRingEnd ℂ) q).totalDegree ≤ q.totalDegree`. Unfold `totalDegree`. Conclude with `Finset.sup_mono (support_map_subset _ _)`.

Conclude with `(totalDegree_rename_le _ _).trans (hm.trans hq)`. Simplify using `only`. Rewrite using `[hP g, eval_rename, eval_map]`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (eval₂ (RingHom.id ℂ) _ q) = _`. Rewrite using `[eval₂_comp_left, RingHom.comp_id]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `rcases x with x | x <;> simp`.
-/
private theorem isPolyDeg_star' {M a : ℕ} {P : Matrix (Fin M) (Fin M) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · have hm : (map (starRingEnd ℂ) q).totalDegree ≤ q.totalDegree := by
      unfold totalDegree; exact Finset.sup_mono (support_map_subset _ _)
    exact (totalDegree_rename_le _ _).trans (hm.trans hq)
  · dsimp only
    rw [hP g, eval_rename, eval_map]
    change starRingEnd ℂ (eval₂ (RingHom.id ℂ) _ q) = _
    rw [eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

/- English proof (translation)
Conclude with `isPolyDeg_star' (zhat_pd k r z z' a b)`.
-/
theorem zhat_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => star (Zhat k r z z' g a b)) := by
  exact isPolyDeg_star' (zhat_pd k r z z' a b)

/- English proof (translation)
Introduce `k r z z' l`. Conclude with `pd_det (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt)) (Fin.castLE (Nat.le_of_lt_succ l.isLt))) (fun a b => zhat_pd k r z z' _ _)`.
-/
theorem minor_polynomial_property : C6.DminPoly := by
  intro k r z z' l
  exact pd_det (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))) (fun a b => zhat_pd k r z z' _ _)

/- English proof (translation)
Conclude with `isPolyDeg_star' (minor_polynomial_property k r z z' l)`.
-/
theorem dmin_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg l.val (fun g => star (Dmin k r z z' g l)) := by
  exact isPolyDeg_star' (minor_polynomial_property k r z z' l)

/- English proof (translation)
Introduce `k r z z'`. Establish `hL` using `pd_mul (minor_polynomial_property k r z z' (Fin.last (r + 1))) (dmin_star_pd k r z z' (Fin.last (r + 1)))`. Establish `hR0` using `pd_mul (minor_polynomial_property k r z z' ⟨r, by omega⟩) (dmin_star_pd k r z z' ⟨r, by omega⟩)`. Establish `hR` using `pd_mul (pd_const (((Tz k r z * Tz k r z' : ℝ)) : ℂ) 0) hR0`. Establish `hL' : U.IsPolyDeg (2 * r + 2) (fun g => Dmin k r z z' g (Fin.last (r + 1)) * star (Dmin k r z z' g (Fin.last (r + 1))))` using `pd_mono (by simp; omega) hL`.

Establish `hR' : U.IsPolyDeg (2 * r + 2) (fun g => ((Tz k r z * Tz k r z' : ℝ) : ℂ) * (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩)))` using `pd_mono (by simp; omega) hR`. Establish `h` using `pd_sub hL' hR'`. Use `h using 2 with g` and compare the differences between its conclusion and the goal. Simplify using `only [Gf, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def, Complex.mul_conj]`.
-/
theorem gram_function_polynomial : C6.GfPoly := by
  intro k r z z'
  have hL := pd_mul (minor_polynomial_property k r z z' (Fin.last (r + 1)))
    (dmin_star_pd k r z z' (Fin.last (r + 1)))
  have hR0 := pd_mul (minor_polynomial_property k r z z' ⟨r, by omega⟩)
    (dmin_star_pd k r z z' ⟨r, by omega⟩)
  have hR := pd_mul (pd_const (((Tz k r z * Tz k r z' : ℝ)) : ℂ) 0) hR0
  have hL' : U.IsPolyDeg (2 * r + 2) (fun g => Dmin k r z z' g (Fin.last (r + 1)) *
      star (Dmin k r z z' g (Fin.last (r + 1)))) :=
    pd_mono (by simp; omega) hL
  have hR' : U.IsPolyDeg (2 * r + 2) (fun g => ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
      (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩))) :=
    pd_mono (by simp; omega) hR
  have h := pd_sub hL' hR'
  convert h using 2 with g
  simp only [Gf, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def, Complex.mul_conj]

end Formalism.FourierDecayAlt.P
