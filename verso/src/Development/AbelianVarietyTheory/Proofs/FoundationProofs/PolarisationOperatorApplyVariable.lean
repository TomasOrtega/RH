import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BottomMinor

open MvPolynomial Matrix Finset

noncomputable section

namespace GlobalTheory.MinorNorm

section Capelli

variable {R : Type} [CommRing R] [Algebra ℂ R]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha, Derivation.leibniz, ih, add_comm, Finset.smul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hne : a ≠ i` using `fun h => ha (h ▸ hi)`. Rewrite using `[Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)), smul_smul]`.
-/
theorem deriv_prod {ι : Type} [DecidableEq ι] (D : Derivation ℂ R R) (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) • D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha, Derivation.leibniz, ih,
      add_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      smul_smul]

/- English proof (translation)
Establish `key : ∀ N : Matrix (Fin m) (Fin m) R, N.det = ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, N i (σ i)`. Introduce `N`. Rewrite using `[← det_transpose, det_apply']`. Both sides reduce to the same expression. Simplify using `only [key, map_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, D.map_intCast, smul_zero, add_zero, smul_eq_mul, ← Finset.mul_sum, deriv_prod]`. Use `congr 1`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ t), updateRow_self, smul_eq_mul, mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[updateRow_ne (Finset.ne_of_mem_erase hi)]`.
-/
theorem deriv_det {m : ℕ} (D : Derivation ℂ R R) (M : Matrix (Fin m) (Fin m) R) :
    D M.det = ∑ t, (M.updateRow t fun u => D (M t u)).det := by
  have key : ∀ N : Matrix (Fin m) (Fin m) R,
      N.det = ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, N i (σ i) := by
    intro N
    rw [← det_transpose, det_apply']
    rfl
  simp only [key, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.leibniz, D.map_intCast, smul_zero, add_zero, smul_eq_mul, ← Finset.mul_sum,
    deriv_prod]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), updateRow_self, smul_eq_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [updateRow_ne (Finset.ne_of_mem_erase hi)]

/- English proof (translation)
Rewrite using `[det_succ_row_zero]`. Both sides reduce to the same expression.
-/
theorem det_cons {m : ℕ} (v : Fin (m + 1) → R) (M : Fin m → Fin (m + 1) → R) :
    (Matrix.of (Fin.cons v M : Fin (m + 1) → Fin (m + 1) → R)).det =
      ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * v s * (Matrix.of fun t u => M t (s.succAbove u)).det := by
  rw [det_succ_row_zero]
  rfl

/- English proof (translation)
The claim follows from `det_zero_of_row_eq (i := 0) (j := t.succ) (Fin.succ_ne_zero t).symm rfl`.
-/
theorem det_cons_self {m : ℕ} (M : Fin m → Fin (m + 1) → R) (t : Fin m) :
    (Matrix.of (Fin.cons (M t) M : Fin (m + 1) → Fin (m + 1) → R)).det = 0 :=
  det_zero_of_row_eq (i := 0) (j := t.succ) (Fin.succ_ne_zero t).symm rfl

/- English proof (translation)
Establish `h` using `det_permute (Equiv.swap (0 : Fin (m + 1)) t.succ) (Matrix.of (Fin.cons e M : Fin (m + 1) → Fin (m + 1) → R))`. Rewrite `h` using `[Equiv.Perm.sign_swap (Fin.succ_ne_zero t).symm]`. Simplify using `only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h`. Rewrite using `[← h]`. Use `congr 1`.

Use extensionality with `i u`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[-Fin.cons_update]`. Distinguish the cases in `hi : i = t`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[submatrix_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) (fun h => hi (Fin.succ_injective _ h))]`. Simplify using `[-Fin.cons_update, Function.update_of_ne hi]`.
-/
theorem det_cons_update {m : ℕ} (M : Fin m → Fin (m + 1) → R) (t : Fin m) (e : Fin (m + 1) → R) :
    (Matrix.of (Fin.cons (M t) (Function.update M t e) : Fin (m + 1) → Fin (m + 1) → R)).det =
      -(Matrix.of (Fin.cons e M : Fin (m + 1) → Fin (m + 1) → R)).det := by
  have h := det_permute (Equiv.swap (0 : Fin (m + 1)) t.succ)
    (Matrix.of (Fin.cons e M : Fin (m + 1) → Fin (m + 1) → R))
  rw [Equiv.Perm.sign_swap (Fin.succ_ne_zero t).symm] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  rw [← h]
  congr 1
  ext i u
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [-Fin.cons_update]
  · by_cases hi : i = t
    · subst hi; simp
    · rw [submatrix_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i)
        (fun h => hi (Fin.succ_injective _ h))]
      simp [-Fin.cons_update, Function.update_of_ne hi]

variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)

def pol (i j : Fin k) : Derivation ℂ R R := ∑ r, x r i • d r j

/- English proof (translation)
Unfold `pol`. Establish `: ∀ s : Finset (Fin k), (∑ r ∈ s, x r i • d r j) P = ∑ r ∈ s, x r i * d r j P`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert a s ha ih => simp [Finset.sum_insert ha, ih]`. Conclude with `this _`.
-/
theorem pol_apply (i j : Fin k) (P : R) : pol x d i j P = ∑ r, x r i * d r j P := by
  unfold pol
  have : ∀ s : Finset (Fin k), (∑ r ∈ s, x r i • d r j) P = ∑ r ∈ s, x r i * d r j P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  exact this _

noncomputable def iterD (m : ℕ) : (Fin m → Fin k) → (Fin m → Fin k) → R → R :=
  Nat.rec (motive := fun m => (Fin m → Fin k) → (Fin m → Fin k) → R → R) (fun _ _ P => P)
    (fun _ f ρ J P => d (ρ 0) (J 0) (f (Fin.tail ρ) (Fin.tail J) P)) m

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iterD_zero (ρ J : Fin 0 → Fin k) (P : R) : iterD d 0 ρ J P = P := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iterD_succ (m : ℕ) (ρ J : Fin (m + 1) → Fin k) (P : R) :
    iterD d (m + 1) ρ J P = d (ρ 0) (J 0) (iterD d m (Fin.tail ρ) (Fin.tail J) P) := rfl

variable {x d}

/- English proof (translation)
Rewrite using `[pol_apply]`. Simplify using `only [hd]`. Distinguish the cases in `h : c = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`.
-/
theorem polarisationOperator_apply_variable (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) (i j s c : Fin k) :
    pol x d i j (x s c) = if c = j then x s i else 0 := by
  rw [pol_apply]
  simp only [hd]
  by_cases h : c = j
  · subst h; simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Rewrite using `[← det_cons (fun s => if I s = j then (1 : R) else 0) (fun t u => x (ρ t) (I u))]`. Simplify using `only [deriv_det, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ t : Fin m, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).updateRow t fun u => pol x d (I s) j ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))) t u)).det = -(Matrix.of (Fin.cons (fun s => if I s = j then (1 : R) else 0) (fun t u => …`. Introduce `t`.

Rewrite using `[← det_cons_update (fun t u => x (ρ t) (I u)) t, det_cons]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `congr 1`. Establish `e : (fun u => pol x d (I s) j ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))) t u)) = x (ρ t) (I s) • fun u => if I (s.succAbove u) = j then (1 : R) else 0`.

Use extensionality with `u`. Simplify using `[polarisationOperator_apply_variable hd]`. Rewrite using `[e, det_updateRow_smul]`. Use `congr 2`. Use extensionality with `t' u`.

Distinguish the cases in `ht : t' = t`. Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Simplify using `[updateRow_ne ht, Function.update_of_ne ht]`. Simplify using `only [this]`.

Simplify using the standard rewrite rules.
-/
theorem sum_pol_det (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) {m : ℕ}
    (ρ : Fin m → Fin k) (I : Fin (m + 1) → Fin k) (j : Fin k) :
    ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
        pol x d (I s) j (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det =
      -(m * ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * (if I s = j then 1 else 0) *
        (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det) := by
  rw [← det_cons (fun s => if I s = j then (1 : R) else 0) (fun t u => x (ρ t) (I u))]
  simp only [deriv_det, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ t : Fin m, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
      ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).updateRow t fun u =>
        pol x d (I s) j ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))) t u)).det =
      -(Matrix.of (Fin.cons (fun s => if I s = j then (1 : R) else 0) (fun t u => x (ρ t) (I u)) :
        Fin (m + 1) → Fin (m + 1) → R)).det := by
    intro t
    rw [← det_cons_update (fun t u => x (ρ t) (I u)) t, det_cons]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_assoc]
    congr 1
    have e : (fun u => pol x d (I s) j ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))) t u)) =
        x (ρ t) (I s) • fun u => if I (s.succAbove u) = j then (1 : R) else 0 := by
      ext u
      simp [polarisationOperator_apply_variable hd]
    rw [e, det_updateRow_smul]
    congr 2
    ext t' u
    by_cases ht : t' = t
    · subst ht; simp
    · simp [updateRow_ne ht, Function.update_of_ne ht]
  simp only [this]
  simp

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro J I _`. Simplify using `[iterD_zero]`. Consider the case `succ m ih`.

Introduce `J I hJ`. Establish `hJ' : ∀ t, (Fin.tail J t : ℕ) + m = k + t`. Introduce `t`. Use `hJ t.succ` as an intermediate fact. Simplify using `only [Fin.val_succ] at this`.

Simplify using `only [Fin.tail]`. Use linear arithmetic over natural numbers and integers. Establish `h0 : k - (J 0 + 1) = m`. Use `hJ 0` as an intermediate fact. Simplify using `only [Fin.val_zero] at this`.

Use linear arithmetic over natural numbers and integers. Use `set j := J 0 with hj`. Use `set c : R := ((∏ t, (a (Fin.tail J t) + (k - (Fin.tail J t + 1))) : ℕ) : R) with hc`. Use `set δ : Fin m → Fin (m + 1) → R := fun t s => if I s = Fin.tail J t then (1 : R) else 0 with hδ`. Establish `ih' : ∀ s : Fin (m + 1), ∑ ρ : Fin m → Fin k, (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * iterD d m ρ (Fin.tail J) P = c * (Matrix.of fun t u => δ t (s.succAbove u)).det * P` using `fun s => ih (Fin.tail J) (fun u => I (s.succAbove u)) hJ'`.

Establish `e1 : ∑ ρ : Fin (m + 1) → Fin k, (Matrix.of fun t s => x (ρ t) (I s)).det * iterD d (m + 1) ρ J P = ∑ ρ : Fin m → Fin k, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * pol x d (I s) j (iterD d m ρ (Fin.tail J) P))`. Rewrite using `[← (Fin.consEquiv fun _ : Fin (m + 1) => Fin k).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Simplify using `only [pol_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[det_succ_row_zero, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `e : ((Matrix.of fun t s => x ((Fin.consEquiv fun _ : Fin (m + 1) => Fin k) (r, ρ) t) (I s)).submatrix Fin.succ s.succAbove) = Matrix.of fun t u => x (ρ t) (I (s.succAbove u))` using `rfl`. Rewrite using `[e]`.

Express the relevant statement in the definitionally equal form `(-1) ^ (s : ℕ) * x r (I s) * _ * d r j (iterD d m ρ (Fin.tail J) P) = _`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ ρ : Fin m → Fin k, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * pol x d (I s) j (iterD d m ρ (Fin.tail J) P)) = ∑ s : Fin (m + 1), ((-1) ^ (s : ℕ) * pol x d (I s) j ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * i …`. Introduce `ρ`. Establish `h` using `congrArg (· * iterD d m ρ (Fin.tail J) P) (sum_pol_det hd ρ I j)`.

Simplify using `only [Finset.sum_mul, Finset.mul_sum, neg_mul] at h`. Simplify using `only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib]`. Rewrite using `[add_assoc, left_eq_add]`. Rewrite `h` using `[eq_neg_iff_add_eq_zero]`. Use `Eq.trans ?_ h` and prove the remaining obligations.

Use `congr 1`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hcst : ∀ (D : Derivation ℂ R R) (s : Fin (m + 1)), D (c * (Matrix.of fun t u => δ t (s.succAbove u)).det * P) = c * (Matrix.of fun t u => δ t (s.succAbove u)).det * D P`. Introduce `D s`. Establish `: D (Matrix.of fun t u => δ t (s.succAbove u)).det = 0`. Rewrite using `[deriv_det]`. Use `Finset.sum_eq_zero fun t _ => det_eq_zero_of_row_eq_zero t fun u => ?_` and prove the remaining obligations.

Simplify using `only [updateRow_self, of_apply, hδ]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [Derivation.leibniz, this, hc, Derivation.map_natCast, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : ∀ s : Fin (m + 1), pol x d (I s) j P = (if I s = j then 1 else 0) * (a j * P) + ∑ t, δ t s * pol x d (Fin.tail J t) j P`.

Introduce `s`. Establish `hgt : ∀ t, j < Fin.tail J t`. Introduce `t`. Use `hJ' t` as an intermediate fact. Use `j.2` as an intermediate fact.

Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Break down `lt_trichotomy (I s) j with h | h | h` into its components or cases. Rewrite using `[hup _ _ h, if_neg h.ne, Finset.sum_eq_zero]`. Simplify using the standard rewrite rules.

Introduce `t _`. Simplify using `only [hδ]`. Rewrite using `[if_neg (h.trans (hgt t)).ne, zero_mul]`. Rewrite using `[h, hwt, if_pos rfl, Finset.sum_eq_zero]`. Simplify using the standard rewrite rules.

Introduce `t _`. Simplify using `only [hδ]`. Rewrite using `[if_neg (h.trans_lt (hgt t)).ne, zero_mul]`. Establish `h1` using `(I s).2`. Establish `h2 : (j : ℕ) < I s` using `h`.

Establish `h3` using `j.2`. Rewrite using `[if_neg h.ne', zero_mul, zero_add, Finset.sum_eq_single (⟨(I s : ℕ) - (j + 1), by omega⟩ : Fin m)]`. Establish `: I s = Fin.tail J ⟨(I s : ℕ) - (j + 1), by omega⟩`. Use `hJ' ⟨(I s : ℕ) - (j + 1), by omega⟩` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [hδ]`. Rewrite using `[if_pos this, one_mul, ← this]`. Introduce `t _ ht`.

Simplify using `only [hδ]`. Rewrite using `[if_neg, zero_mul]`. Introduce `h'`. Apply `ht` to reduce the goal to its premises. Use `hJ' t` as an intermediate fact.

Rewrite `this` using `[← h']`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Establish `hz : ∀ t, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * δ t s * (Matrix.of fun t u => δ t (s.succAbove u)).det = 0`. Introduce `t`. Rewrite using `[← det_cons, det_cons_self]`. Establish `e3 : (Matrix.of fun t s => if I s = J t then (1 : R) else 0).det = ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * (if I s = j then 1 else 0) * (Matrix.of fun t u => δ t (s.succAbove u)).det`. Rewrite using `[det_succ_row_zero]`.

Both sides reduce to the same expression. Rewrite using `[e1]`. Simplify using `only [e2]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, ih', hcst, hv]`.

Rewrite using `[Fin.prod_univ_succ, Nat.cast_mul, ← hj, h0, e3]`. Express the relevant statement in the definitionally equal form `_ = _ * c * _ * _`. Establish `hz' : ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * (c * (Matrix.of fun t u => δ t (s.succAbove u)).det * ∑ t, δ t s * pol x d (Fin.tail J t) j P) = 0`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Use `congrArg (· * (c * pol x d (Fin.tail J t) j P)) (hz t)` as an intermediate fact. Simplify using `only [Finset.sum_mul, zero_mul] at this`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mul_add, Finset.sum_add_distrib, hz', add_zero]`. Rewrite using `[← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem capelli_step (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0)
    (a : Fin k → ℕ) (P : R) (hup : ∀ i j, i < j → pol x d i j P = 0)
    (hwt : ∀ j, pol x d j j P = a j * P) :
    ∀ (m : ℕ) (J I : Fin m → Fin k), (∀ t, (J t : ℕ) + m = k + t) →
      ∑ ρ : Fin m → Fin k, (Matrix.of fun t s => x (ρ t) (I s)).det * iterD d m ρ J P =
        ((∏ t, (a (J t) + (k - (J t + 1))) : ℕ) : R) *
          (Matrix.of fun t s => if I s = J t then (1 : R) else 0).det * P := by
  intro m
  induction m with
  | zero => intro J I _; simp [iterD_zero]
  | succ m ih =>
    intro J I hJ
    have hJ' : ∀ t, (Fin.tail J t : ℕ) + m = k + t := by
      intro t
      have := hJ t.succ
      simp only [Fin.val_succ] at this
      simp only [Fin.tail]
      omega
    have h0 : k - (J 0 + 1) = m := by
      have := hJ 0
      simp only [Fin.val_zero] at this
      omega
    set j := J 0 with hj
    set c : R := ((∏ t, (a (Fin.tail J t) + (k - (Fin.tail J t + 1))) : ℕ) : R) with hc
    set δ : Fin m → Fin (m + 1) → R := fun t s => if I s = Fin.tail J t then (1 : R) else 0 with hδ
    have ih' : ∀ s : Fin (m + 1), ∑ ρ : Fin m → Fin k,
        (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * iterD d m ρ (Fin.tail J) P =
        c * (Matrix.of fun t u => δ t (s.succAbove u)).det * P :=
      fun s => ih (Fin.tail J) (fun u => I (s.succAbove u)) hJ'

    have e1 : ∑ ρ : Fin (m + 1) → Fin k,
        (Matrix.of fun t s => x (ρ t) (I s)).det * iterD d (m + 1) ρ J P =
        ∑ ρ : Fin m → Fin k, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
          ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det *
            pol x d (I s) j (iterD d m ρ (Fin.tail J) P)) := by
      rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin k).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [pol_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [det_succ_row_zero, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      have e : ((Matrix.of fun t s => x ((Fin.consEquiv fun _ : Fin (m + 1) => Fin k) (r, ρ) t)
          (I s)).submatrix Fin.succ s.succAbove) =
          Matrix.of fun t u => x (ρ t) (I (s.succAbove u)) := rfl
      rw [e]
      change (-1) ^ (s : ℕ) * x r (I s) * _ * d r j (iterD d m ρ (Fin.tail J) P) = _
      ring
    have e2 : ∀ ρ : Fin m → Fin k, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
          ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det *
            pol x d (I s) j (iterD d m ρ (Fin.tail J) P)) =
        ∑ s : Fin (m + 1), ((-1) ^ (s : ℕ) * pol x d (I s) j
          ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * iterD d m ρ (Fin.tail J) P) +
          m * ((-1) ^ (s : ℕ) * (if I s = j then 1 else 0)) *
          ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * iterD d m ρ (Fin.tail J) P)) := by
      intro ρ
      have h := congrArg (· * iterD d m ρ (Fin.tail J) P) (sum_pol_det hd ρ I j)
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul] at h
      simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      rw [add_assoc, left_eq_add]
      rw [eq_neg_iff_add_eq_zero] at h
      refine Eq.trans ?_ h
      congr 1
      · refine Finset.sum_congr rfl fun s _ => ?_
        ring
      · refine Finset.sum_congr rfl fun s _ => ?_
        ring
    have hcst : ∀ (D : Derivation ℂ R R) (s : Fin (m + 1)),
        D (c * (Matrix.of fun t u => δ t (s.succAbove u)).det * P) =
          c * (Matrix.of fun t u => δ t (s.succAbove u)).det * D P := by
      intro D s
      have : D (Matrix.of fun t u => δ t (s.succAbove u)).det = 0 := by
        rw [deriv_det]
        refine Finset.sum_eq_zero fun t _ => det_eq_zero_of_row_eq_zero t fun u => ?_
        simp only [updateRow_self, of_apply, hδ]
        split_ifs <;> simp
      simp only [Derivation.leibniz, this, hc, Derivation.map_natCast, smul_eq_mul]
      ring
    have hv : ∀ s : Fin (m + 1), pol x d (I s) j P =
        (if I s = j then 1 else 0) * (a j * P) + ∑ t, δ t s * pol x d (Fin.tail J t) j P := by
      intro s
      have hgt : ∀ t, j < Fin.tail J t := by
        intro t
        have := hJ' t
        have := j.2
        rw [Fin.lt_def]; omega
      rcases lt_trichotomy (I s) j with h | h | h
      · rw [hup _ _ h, if_neg h.ne, Finset.sum_eq_zero]
        · simp
        · intro t _
          simp only [hδ]
          rw [if_neg (h.trans (hgt t)).ne, zero_mul]
      · rw [h, hwt, if_pos rfl, Finset.sum_eq_zero]
        · simp
        · intro t _
          simp only [hδ]
          rw [if_neg (h.trans_lt (hgt t)).ne, zero_mul]
      · have h1 := (I s).2
        have h2 : (j : ℕ) < I s := h
        have h3 := j.2
        rw [if_neg h.ne', zero_mul, zero_add,
          Finset.sum_eq_single (⟨(I s : ℕ) - (j + 1), by omega⟩ : Fin m)]
        · have : I s = Fin.tail J ⟨(I s : ℕ) - (j + 1), by omega⟩ := by
            have := hJ' ⟨(I s : ℕ) - (j + 1), by omega⟩
            apply Fin.ext
            simp only at this
            omega
          simp only [hδ]
          rw [if_pos this, one_mul, ← this]
        · intro t _ ht
          simp only [hδ]
          rw [if_neg, zero_mul]
          intro h'
          apply ht
          have := hJ' t
          rw [← h'] at this
          apply Fin.ext
          simp only
          omega
        · simp
    have hz : ∀ t, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * δ t s *
        (Matrix.of fun t u => δ t (s.succAbove u)).det = 0 := by
      intro t
      rw [← det_cons, det_cons_self]
    have e3 : (Matrix.of fun t s => if I s = J t then (1 : R) else 0).det =
        ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * (if I s = j then 1 else 0) *
          (Matrix.of fun t u => δ t (s.succAbove u)).det := by
      rw [det_succ_row_zero]; rfl
    rw [e1]
    simp only [e2]
    rw [Finset.sum_comm]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, ih', hcst, hv]
    rw [Fin.prod_univ_succ, Nat.cast_mul, ← hj, h0, e3]
    change _ = _ * c * _ * _
    have hz' : ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
        (c * (Matrix.of fun t u => δ t (s.succAbove u)).det *
          ∑ t, δ t s * pol x d (Fin.tail J t) j P) = 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun t _ => ?_
      have := congrArg (· * (c * pol x d (Fin.tail J t) j P)) (hz t)
      simp only [Finset.sum_mul, zero_mul] at this
      rw [← this]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    simp only [mul_add, Finset.sum_add_distrib, hz', add_zero]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast
    ring

def eps (ρ : Fin k → Fin k) : ℤ := (Matrix.of fun t s => if ρ t = s then (1 : ℤ) else 0).det

/- English proof (translation)
Unfold `eps`. Rewrite using `[Int.cast_det]`. Use `congr 1`. Use extensionality with `t s`. Simplify using the standard rewrite rules.
-/
theorem cast_eps (ρ : Fin k → Fin k) :
    ((eps ρ : ℤ) : R) = (Matrix.of fun t s => if ρ t = s then (1 : R) else 0).det := by
  unfold eps
  rw [Int.cast_det]
  congr 1
  ext t s
  simp

/- English proof (translation)
Use `conv_lhs => rw [← Matrix.one_mul (Matrix.of x)]`. Simplify using `only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[cast_eps, ← det_transpose, det_apply', Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, mul_assoc]`. Simplify using `[Matrix.one_apply, eq_comm]`.
-/
theorem det_eq_sum_eps (x : Fin k → Fin k → R) :
    (Matrix.of x).det = ∑ ρ : Fin k → Fin k, (eps ρ : R) * ∏ t, x (ρ t) t := by
  conv_lhs => rw [← Matrix.one_mul (Matrix.of x)]
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [cast_eps, ← det_transpose, det_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]
  simp [Matrix.one_apply, eq_comm]

/- English proof (translation)
Establish `h` using `capelli_step hd a P hup hwt k id id (fun t => by simp [add_comm])`. Establish `e : (Matrix.of fun t s : Fin k => if id s = id t then (1 : R) else 0) = 1`. Use extensionality with `t s`. Simplify using `[Matrix.one_apply, eq_comm]`. Rewrite `h` using `[e, det_one, mul_one]`.

Use `Eq.trans ?_ h` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[cast_eps, ← mul_assoc, mul_comm (Matrix.of x).det, ← det_mul]`. Use `congr 2`.

Use extensionality with `t s`. Simplify using `[Matrix.mul_apply]`.
-/
theorem capelli_hw (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0)
    (a : Fin k → ℕ) (P : R) (hup : ∀ i j, i < j → pol x d i j P = 0)
    (hwt : ∀ j, pol x d j j P = a j * P) :
    (Matrix.of x).det * ∑ ρ : Fin k → Fin k, (eps ρ : R) * iterD d k ρ id P =
      ((∏ t, (a t + (k - (t + 1))) : ℕ) : R) * P := by
  have h := capelli_step hd a P hup hwt k id id (fun t => by simp [add_comm])
  have e : (Matrix.of fun t s : Fin k => if id s = id t then (1 : R) else 0) = 1 := by
    ext t s; simp [Matrix.one_apply, eq_comm]
  rw [e, det_one, mul_one] at h
  refine Eq.trans ?_ h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [cast_eps, ← mul_assoc, mul_comm (Matrix.of x).det, ← det_mul]
  congr 2
  ext t s
  simp [Matrix.mul_apply]

end Capelli

section Weight

variable {R : Type} [CommRing R] [Algebra ℂ R] {k : ℕ} {x : Fin k → Fin k → R}
  {d : Fin k → Fin k → Derivation ℂ R R}

/- English proof (translation)
Rewrite using `[← det_transpose, deriv_det]`. Simplify using `only [transpose_apply, of_apply, polarisationOperator_apply_variable hd]`. Distinguish the cases in `hj : (j : ℕ) < m`. Rewrite using `[Finset.sum_eq_single (⟨j, hj⟩ : Fin m)]`. Establish `e : Fin.castLE hm ⟨j, hj⟩ = j` using `rfl`.

Simplify using `only [e, if_true]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[if_pos ⟨rfl, hj⟩, one_mul]`. Use `congr 1`.

Conclude with `updateRow_eq_self _ _`. Rewrite using `[if_neg (fun h' => h h'.1), zero_mul]`. Establish `hi : (i : ℕ) < j` using `lt_of_le_of_ne hij (fun h' => h (Fin.ext h'))`. Use `det_zero_of_row_eq (i := ⟨j, hj⟩) (j := ⟨i, hi.trans hj⟩) (fun h' => hi.ne' (Fin.mk.inj h')) ?_` and prove the remaining obligations. Rewrite using `[updateRow_self, updateRow_ne (fun h' => hi.ne (Fin.mk.inj h'))]`.

Both sides reduce to the same expression. Introduce `t _ ht`. Use `det_eq_zero_of_row_eq_zero t fun u => ?_` and prove the remaining obligations. Rewrite using `[updateRow_self, if_neg]`. Introduce `h`.

Conclude with `ht (Fin.ext (congrArg Fin.val h :))`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h => hj h.2), zero_mul]`. Use `Finset.sum_eq_zero fun t _ => det_eq_zero_of_row_eq_zero t fun u => ?_` and prove the remaining obligations. Rewrite using `[updateRow_self, if_neg]`.

Introduce `h`. Apply `hj` to reduce the goal to its premises. Rewrite using `[← h]`. Conclude with `t.2`.
-/
theorem pol_minor (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) {m : ℕ}
    (hm : m ≤ k) (i j : Fin k) (hij : i ≤ j) :
    pol x d i j (Matrix.of fun r c : Fin m => x (Fin.castLE hm r) (Fin.castLE hm c)).det =
      (if i = j ∧ (j : ℕ) < m then 1 else 0) *
        (Matrix.of fun r c : Fin m => x (Fin.castLE hm r) (Fin.castLE hm c)).det := by
  rw [← det_transpose, deriv_det]
  simp only [transpose_apply, of_apply, polarisationOperator_apply_variable hd]
  by_cases hj : (j : ℕ) < m
  · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin m)]
    · have e : Fin.castLE hm ⟨j, hj⟩ = j := rfl
      simp only [e, if_true]
      by_cases h : i = j
      · subst h
        rw [if_pos ⟨rfl, hj⟩, one_mul]
        congr 1
        exact updateRow_eq_self _ _
      · rw [if_neg (fun h' => h h'.1), zero_mul]
        have hi : (i : ℕ) < j := lt_of_le_of_ne hij (fun h' => h (Fin.ext h'))
        refine det_zero_of_row_eq (i := ⟨j, hj⟩) (j := ⟨i, hi.trans hj⟩)
          (fun h' => hi.ne' (Fin.mk.inj h')) ?_
        rw [updateRow_self, updateRow_ne (fun h' => hi.ne (Fin.mk.inj h'))]
        rfl
    · intro t _ ht
      refine det_eq_zero_of_row_eq_zero t fun u => ?_
      rw [updateRow_self, if_neg]
      intro h
      exact ht (Fin.ext (congrArg Fin.val h :))
    · simp
  · rw [if_neg (fun h => hj h.2), zero_mul]
    refine Finset.sum_eq_zero fun t _ => det_eq_zero_of_row_eq_zero t fun u => ?_
    rw [updateRow_self, if_neg]
    intro h
    apply hj
    rw [← h]
    exact t.2

end Weight

section Fock

variable {σ : Type}

/- English proof (translation)
Unfold `Formalism.E.fock`. Use `Finset.sum_subset hs fun m _ hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.notMem_support_iff.mp hm]`. Simplify using the standard rewrite rules.
-/
theorem fock_eq_sum (P Q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hs : P.support ⊆ s) :
    Formalism.E.fock P Q = ∑ m ∈ s, P.coeff m * star (Q.coeff m) * (Formalism.A.mfact m : ℂ) := by
  unfold Formalism.E.fock
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm]; simp

/- English proof (translation)
Rewrite using `[fock_eq_sum (P + P') Q (P.support ∪ P'.support) support_add, fock_eq_sum P Q (P.support ∪ P'.support) Finset.subset_union_left, fock_eq_sum P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_add_left (P P' Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (P + P') Q = Formalism.E.fock P Q + Formalism.E.fock P' Q := by
  classical
  rw [fock_eq_sum (P + P') Q (P.support ∪ P'.support) support_add,
    fock_eq_sum P Q (P.support ∪ P'.support) Finset.subset_union_left,
    fock_eq_sum P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Formalism.E.fock]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left, ih]`.
-/
theorem fock_sum_left {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (∑ i ∈ s, P i) Q = ∑ i ∈ s, Formalism.E.fock (P i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.E.fock]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left, ih]

/- English proof (translation)
Unfold `Formalism.E.fock`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_sum, star_sum, Finset.mul_sum, Finset.sum_mul]`.
-/
theorem fock_sum_right {ι : Type} (s : Finset ι) (P : MvPolynomial σ ℂ) (Q : ι → MvPolynomial σ ℂ) :
    Formalism.E.fock P (∑ i ∈ s, Q i) = ∑ i ∈ s, Formalism.E.fock P (Q i) := by
  unfold Formalism.E.fock
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_sum, star_sum, Finset.mul_sum, Finset.sum_mul]

/- English proof (translation)
Establish `e : (z : MvPolynomial σ ℂ) = C (z : ℂ)` using `by simp`. Rewrite using `[e, C_mul', fock_eq_sum _ Q P.support support_smul, Formalism.E.fock, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_int_left (z : ℤ) (P Q : MvPolynomial σ ℂ) :
    Formalism.E.fock ((z : MvPolynomial σ ℂ) * P) Q = z * Formalism.E.fock P Q := by
  have e : (z : MvPolynomial σ ℂ) = C (z : ℂ) := by simp
  rw [e, C_mul', fock_eq_sum _ Q P.support support_smul, Formalism.E.fock, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring

/- English proof (translation)
Establish `e : (z : MvPolynomial σ ℂ) = C (z : ℂ)` using `by simp`. Rewrite using `[e, Formalism.E.fock, Formalism.E.fock, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_C_mul, star_mul', star_intCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_int_right (z : ℤ) (P Q : MvPolynomial σ ℂ) :
    Formalism.E.fock P ((z : MvPolynomial σ ℂ) * Q) = z * Formalism.E.fock P Q := by
  have e : (z : MvPolynomial σ ℂ) = C (z : ℂ) := by simp
  rw [e, Formalism.E.fock, Formalism.E.fock, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_C_mul, star_mul', star_intCast]; ring

/- English proof (translation)
Establish `h : ∀ (g : σ →₀ ℕ) (s : Finset σ), g.support ⊆ s → Formalism.A.mfact g = ∏ i ∈ s, (g i).factorial`. Introduce `g s hs`. Unfold `Formalism.A.mfact`. Conclude with `Finset.prod_subset hs fun i _ hi => by`. Rewrite using `[Finsupp.notMem_support_iff.mp hi]`.

Both sides reduce to the same expression. Establish `h1 : (m + Finsupp.single v 1).support ⊆ insert v m.support`. Introduce `i hi`. Distinguish the cases in `hv : i = v`. Simplify using `[hv]`.

Simplify `hi` using `[hv, Finsupp.single_apply, Ne.symm hv]`. Rewrite using `[h _ _ h1, h m (insert v m.support) (Finset.subset_insert _ _), ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v _), ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v _), ← mul_assoc]`. Use `congr 1`. Simplify using `[Nat.factorial_succ]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Use `Finset.ne_of_mem_erase hi` as an intermediate fact. Simplify using `[Finsupp.single_apply, Ne.symm this]`.
-/
theorem mfact_add_single (m : σ →₀ ℕ) (v : σ) :
    Formalism.A.mfact (m + Finsupp.single v 1) = (m v + 1) * Formalism.A.mfact m := by
  classical
  have h : ∀ (g : σ →₀ ℕ) (s : Finset σ), g.support ⊆ s →
      Formalism.A.mfact g = ∏ i ∈ s, (g i).factorial := by
    intro g s hs
    unfold Formalism.A.mfact
    exact Finset.prod_subset hs fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi]; rfl
  have h1 : (m + Finsupp.single v 1).support ⊆ insert v m.support := by
    intro i hi
    by_cases hv : i = v
    · simp [hv]
    · simpa [hv, Finsupp.single_apply, Ne.symm hv] using hi
  rw [h _ _ h1, h m (insert v m.support) (Finset.subset_insert _ _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v _), ← mul_assoc]
  congr 1
  · simp [Nat.factorial_succ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, Ne.symm this]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `add P₁ P₂ h₁ h₂ => simp only [map_add, coeff_add, h₁, h₂, add_mul]`. Consider the case `monomial b c`. Rewrite using `[pderiv_monomial, coeff_monomial, coeff_monomial]`. Distinguish the cases in `h : b = m + Finsupp.single v 1`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, zero_mul] split_ifs with h'`. Establish `: b v = 0`. Assume the negation of the conclusion as `hb`.

Apply `h` to reduce the goal to its premises. Rewrite using `[← h', tsub_add_cancel_of_le]`. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`.

Both sides reduce to the same expression.
-/
theorem coeff_pderiv' (v : σ) (m : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    (pderiv v Q).coeff m = Q.coeff (m + Finsupp.single v 1) * (m v + 1) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ => simp only [map_add, coeff_add, h₁, h₂, add_mul]
  | monomial b c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : b = m + Finsupp.single v 1
    · subst h; simp
    · rw [if_neg h, zero_mul]
      split_ifs with h'
      · have : b v = 0 := by
          by_contra hb
          apply h
          rw [← h', tsub_add_cancel_of_le]
          rw [Finsupp.single_le_iff]; omega
        simp [this]
      · rfl

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `add P₁ P₂ h₁ h₂ => simp only [mul_add, fock_add_left, h₁, h₂]`. Consider the case `monomial a c`. Rewrite using `[mul_comm, X, monomial_mul, mul_one, fock_eq_sum _ _ {a + Finsupp.single v 1} support_monomial_subset, fock_eq_sum _ _ {a} support_monomial_subset, Finset.sum_singleton, Finset.sum_singleton, coeff_monomial, coeff_monomial, if_pos rfl, if_pos rfl, coeff_pderiv', mfact_add_single]`. Simplify using `only [star_mul', star_add, star_natCast, star_one]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_X_mul (v : σ) (P Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (X v * P) Q = Formalism.E.fock P (pderiv v Q) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ => simp only [mul_add, fock_add_left, h₁, h₂]
  | monomial a c =>
    rw [mul_comm, X, monomial_mul, mul_one,
      fock_eq_sum _ _ {a + Finsupp.single v 1} support_monomial_subset,
      fock_eq_sum _ _ {a} support_monomial_subset, Finset.sum_singleton, Finset.sum_singleton,
      coeff_monomial, coeff_monomial, if_pos rfl, if_pos rfl, coeff_pderiv', mfact_add_single]
    simp only [star_mul', star_add, star_natCast, star_one]
    push_cast
    ring

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro ρ J P Q`. Simplify using `[iterD_zero]`. Consider the case `succ m ih`.

Introduce `ρ J P Q`. Rewrite using `[iterD_succ, ← fock_X_mul, ← ih, Fin.prod_univ_succ]`. Use `congr 1`. Simplify using `only [Fin.tail]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_prod_mul {k : ℕ} (v : Fin k → Fin k → σ) :
    ∀ (m : ℕ) (ρ J : Fin m → Fin k) (P Q : MvPolynomial σ ℂ),
      Formalism.E.fock ((∏ t, X (v (ρ t) (J t))) * P) Q =
        Formalism.E.fock P (iterD (fun r c => pderiv (v r c)) m ρ J Q) := by
  intro m
  induction m with
  | zero => intro ρ J P Q; simp [iterD_zero]
  | succ m ih =>
    intro ρ J P Q
    rw [iterD_succ, ← fock_X_mul, ← ih, Fin.prod_univ_succ]
    congr 1
    simp only [Fin.tail]
    ring

/- English proof (translation)
Establish `hd : ∀ r j s c, pderiv (v r j) (X (v s c) : MvPolynomial σ ℂ) = if r = s ∧ j = c then 1 else 0`. Introduce `r j s c`. Use `split_ifs with h`. Rewrite using `[h.1, h.2, pderiv_X_self]`. Conclude with `pderiv_X_of_ne fun h' => h (hv _ _ _ _ h'.symm)`.

Establish `h` using `capelli_hw (x := fun r c => X (v r c)) (d := fun r c => pderiv (v r c)) hd a P hup hwt`. Establish `h2 : ∑ ρ : Fin k → Fin k, (eps ρ : MvPolynomial σ ℂ) * iterD (fun r c => pderiv (v r c)) k ρ id P = (((∏ t, (a t + (k - (t + 1))) : ℕ) : ℤ) : MvPolynomial σ ℂ) * P'`. Apply `mul_left_cancel₀ hdet` to reduce the goal to its premises. Rewrite using `[h, Int.cast_natCast]`. Use `conv_lhs => rw [hP]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : Formalism.E.fock P P = Formalism.E.fock P' (∑ ρ : Fin k → Fin k, (eps ρ : MvPolynomial σ ℂ) * iterD (fun r c => pderiv (v r c)) k ρ id P)` using `by conv_lhs => enter [1]; rw [hP, det_eq_sum_eps, Finset.sum_mul]`. Rewrite using `[fock_sum_left, fock_sum_right]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, fock_int_left, fock_int_right, ← fock_prod_mul]`.

Both sides reduce to the same expression. Rewrite using `[h3, h2, fock_int_right, Int.cast_natCast]`.
-/
theorem fock_det_mul {k : ℕ} (v : Fin k → Fin k → σ)
    (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) (a : Fin k → ℕ) (P' P : MvPolynomial σ ℂ)
    (hP : P = (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det * P')
    (hdet : (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det ≠ 0)
    (hup : ∀ i j, i < j → pol (fun r c => X (v r c)) (fun r c => pderiv (v r c)) i j P = 0)
    (hwt : ∀ j, pol (fun r c => X (v r c)) (fun r c => pderiv (v r c)) j j P = a j * P) :
    Formalism.E.fock P P = ((∏ t, (a t + (k - (t + 1))) : ℕ) : ℂ) * Formalism.E.fock P' P' := by
  classical
  have hd : ∀ r j s c, pderiv (v r j) (X (v s c) : MvPolynomial σ ℂ) =
      if r = s ∧ j = c then 1 else 0 := by
    intro r j s c
    split_ifs with h
    · rw [h.1, h.2, pderiv_X_self]
    · exact pderiv_X_of_ne fun h' => h (hv _ _ _ _ h'.symm)
  have h := capelli_hw (x := fun r c => X (v r c)) (d := fun r c => pderiv (v r c)) hd a P hup hwt
  have h2 : ∑ ρ : Fin k → Fin k, (eps ρ : MvPolynomial σ ℂ) *
      iterD (fun r c => pderiv (v r c)) k ρ id P =
      (((∏ t, (a t + (k - (t + 1))) : ℕ) : ℤ) : MvPolynomial σ ℂ) * P' := by
    apply mul_left_cancel₀ hdet
    rw [h, Int.cast_natCast]
    conv_lhs => rw [hP]
    ring
  have h3 : Formalism.E.fock P P = Formalism.E.fock P' (∑ ρ : Fin k → Fin k, (eps ρ : MvPolynomial σ ℂ) *
      iterD (fun r c => pderiv (v r c)) k ρ id P) := by
    conv_lhs => enter [1]; rw [hP, det_eq_sum_eps, Finset.sum_mul]
    rw [fock_sum_left, fock_sum_right]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [mul_assoc, fock_int_left, fock_int_right, ← fock_prod_mul]
    rfl
  rw [h3, h2, fock_int_right, Int.cast_natCast]

/- English proof (translation)
Introduce `h`. Use `congrArg (eval fun w => if ∃ r, w = v r r then (1 : ℂ) else 0) h` as an intermediate fact. Rewrite `this` using `[RingHom.map_det, map_zero]`. Establish `e : (eval fun w => if ∃ r, w = v r r then (1 : ℂ) else 0).mapMatrix (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)) = 1`. Use extensionality with `r c`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, eval_X, Matrix.one_apply]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs⟩`.

Take `⟨h1, h2⟩` from `hv _ _ _ _ hs`. Rewrite using `[h1, h2]`. Introduce and unpack `rfl`. Conclude with `⟨r, rfl⟩`. Rewrite `this` using `[e, det_one]`.

Conclude with `one_ne_zero this`.
-/
theorem det_X_ne_zero {k : ℕ} (v : Fin k → Fin k → σ)
    (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) :
    (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det ≠ 0 := by
  classical
  intro h
  have := congrArg (eval fun w => if ∃ r, w = v r r then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at this
  have e : (eval fun w => if ∃ r, w = v r r then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)) = 1 := by
    ext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, eval_X, Matrix.one_apply]
    congr 1
    apply propext
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨h1, h2⟩ := hv _ _ _ _ hs
      rw [h1, h2]
    · rintro rfl; exact ⟨r, rfl⟩
  rw [e, det_one] at this
  exact one_ne_zero this

end Fock

section Partition

open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors

variable {l : ℕ}

def addCol (a : Fin l → ℕ) (K : Fin l) : Fin l → ℕ := fun i => a i + if i ≤ K then 1 else 0

/- English proof (translation)
Proceed by induction on `hN : ∑ i, a i using Nat.strong_induction_on generalizing a with`. Consider the case `_ N ih`. Distinguish the cases in `h : a = 0`. Conclude with `h ▸ h0`. Establish `hne : (Finset.univ.filter fun i => a i ≠ 0).Nonempty`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp h`. Conclude with `⟨i, by simpa using hi⟩`. Use `set K := (Finset.univ.filter fun i => a i ≠ 0).max' hne with hK`. Establish `hK1 : a K ≠ 0` using `(Finset.mem_filter.mp (Finset.max'_mem _ hne)).2`. Establish `hK2 : ∀ i, K < i → a i = 0`.

Introduce `i hi`. Assume the negation of the conclusion as `h'`. Conclude with `absurd (Finset.le_max' _ i (by simpa using h')) (not_le.mpr hi)`. Establish `hK3 : ∀ i, i ≤ K → 1 ≤ a i` using `fun i hi => (Nat.one_le_iff_ne_zero.mpr hK1).trans (ha hi)`. Establish `e : addCol (fun i => a i - 1) K = a`.

Use extensionality with `i`. Simplify using `only [addCol]`. Use `split_ifs with hi`. Use `hK3 i hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hK2 i (not_le.mp hi)]`. Establish `ha' : Antitone fun i => a i - 1` using `fun i j hij => Nat.sub_le_sub_right (ha hij) 1`. Rewrite using `[← e]`. Use `hs _ K ha' (fun i hi => by simp [hK2 i hi]) (ih _ ?_ _ ha' rfl)` and prove the remaining obligations. Rewrite using `[← hN]`.

Use `Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _) ⟨K, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `hK3 K le_rfl` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem partition_induction (p : (Fin l → ℕ) → Prop) (h0 : p 0)
    (hs : ∀ (a : Fin l → ℕ) (K : Fin l), Antitone a → (∀ i, K < i → a i = 0) → p a →
      p (addCol a K)) (a : Fin l → ℕ) (ha : Antitone a) : p a := by
  induction hN : ∑ i, a i using Nat.strong_induction_on generalizing a with
  | _ N ih =>
  by_cases h : a = 0
  · exact h ▸ h0
  · have hne : (Finset.univ.filter fun i => a i ≠ 0).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact ⟨i, by simpa using hi⟩
    set K := (Finset.univ.filter fun i => a i ≠ 0).max' hne with hK
    have hK1 : a K ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hK2 : ∀ i, K < i → a i = 0 := by
      intro i hi
      by_contra h'
      exact absurd (Finset.le_max' _ i (by simpa using h')) (not_le.mpr hi)
    have hK3 : ∀ i, i ≤ K → 1 ≤ a i := fun i hi => (Nat.one_le_iff_ne_zero.mpr hK1).trans (ha hi)
    have e : addCol (fun i => a i - 1) K = a := by
      ext i
      simp only [addCol]
      split_ifs with hi
      · have := hK3 i hi
        omega
      · rw [hK2 i (not_le.mp hi)]
    have ha' : Antitone fun i => a i - 1 := fun i j hij => Nat.sub_le_sub_right (ha hij) 1
    rw [← e]
    refine hs _ K ha' (fun i hi => by simp [hK2 i hi]) (ih _ ?_ _ ha' rfl)
    rw [← hN]
    refine Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _) ⟨K, Finset.mem_univ _, ?_⟩
    have := hK3 K le_rfl
    omega

/- English proof (translation)
Establish `h` using `nextPart_le ha i`. Establish `hK` using `K.2`. Unfold `nextPart addCol at *`. Simplify using `only [Fin.le_def, Fin.ext_iff]`. Apply the tactic sequence `split_ifs at h ⊢ <;> omega`.
-/
theorem addCol_exp {a : Fin l → ℕ} (ha : Antitone a) (K i : Fin l) :
    addCol a K i - nextPart (addCol a K) i = (a i - nextPart a i) + if i = K then 1 else 0 := by
  have h := nextPart_le ha i
  have hK := K.2
  unfold nextPart addCol at *
  simp only [Fin.le_def, Fin.ext_iff]
  split_ifs at h ⊢ <;> omega

/- English proof (translation)
Use `Finset.prod_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Establish `: K < j` using `Finset.mem_Ioi.mp hj`. Conclude with `Finset.mem_Ico.mpr ⟨this, j.2⟩`. Introduce `j _ j' _ h`.

Conclude with `Fin.ext h`. Introduce `j hj`. Take `⟨h1, h2⟩` from `Finset.mem_Ico.mp hj`. Conclude with `⟨⟨j, h2⟩, Finset.mem_Ioi.mpr h1, rfl⟩`. Introduce `j _`.

Both sides reduce to the same expression.
-/
theorem prod_Ioi_eq (K : Fin l) (g : ℕ → ℚ) :
    ∏ j ∈ Finset.Ioi K, g j = ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, g j := by
  refine Finset.prod_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_ ?_
  · intro j hj
    have : K < j := Finset.mem_Ioi.mp hj
    exact Finset.mem_Ico.mpr ⟨this, j.2⟩
  · intro j _ j' _ h
    exact Fin.ext h
  · intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
    exact ⟨⟨j, h2⟩, Finset.mem_Ioi.mpr h1, rfl⟩
  · intro j _
    rfl

/- English proof (translation)
Proceed by induction on `t, h using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ t ht ih`. Rewrite using `[Finset.prod_Ico_succ_top ht, Finset.prod_Ico_succ_top ht]`. Use `push_cast`.

Take the linear combination `(c + 1 + t) * ih`.
-/
theorem telescope (c : ℚ) (s t : ℕ) (h : s ≤ t) :
    (∏ j ∈ Finset.Ico s t, (c + 1 + j)) * (c + s) = (∏ j ∈ Finset.Ico s t, (c + j)) * (c + t) := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [Finset.prod_Ico_succ_top ht, Finset.prod_Ico_succ_top ht]
    push_cast
    linear_combination (c + 1 + t) * ih

/- English proof (translation)
Proceed by induction on `t, h using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ t ht ih`. Rewrite using `[Finset.prod_Ico_succ_top ht, ih, Nat.succ_sub ht, Nat.factorial_succ]`. Move the coercions through the operations in `[Nat.cast_sub ht]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_sub_eq_factorial (s t : ℕ) (h : s + 1 ≤ t) :
    ∏ j ∈ Finset.Ico (s + 1) t, ((j : ℚ) - s) = (t - (s + 1)).factorial := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [Finset.prod_Ico_succ_top ht, ih, Nat.succ_sub ht, Nat.factorial_succ]
    push_cast [Nat.cast_sub ht]
    ring

/- English proof (translation)
Unfold `hookProd`. Rewrite using `[div_eq_one_iff_eq (hookDen_pos (a := 0) antitone_const).ne']`. Unfold `hookDen`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.zero_apply, zero_add, Nat.cast_zero, sub_self]`.

Rewrite using `[prod_Ioi_eq i fun j => (j : ℚ) - (i : ℕ), prod_sub_eq_factorial _ _ i.2]`.
-/
theorem hookProd_zero : hookProd (0 : Fin l → ℕ) = 1 := by
  unfold hookProd
  rw [div_eq_one_iff_eq (hookDen_pos (a := 0) antitone_const).ne']
  unfold hookDen
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.zero_apply, zero_add, Nat.cast_zero, sub_self]
  rw [prod_Ioi_eq i fun j => (j : ℚ) - (i : ℕ), prod_sub_eq_factorial _ _ i.2]

/- English proof (translation)
Introduce `i j hij`. Use `ha hij` as an intermediate fact. Unfold `addCol`. Distinguish the cases in `h : j ≤ K`. Rewrite using `[if_pos h, if_pos (hij.trans h)]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem addCol_antitone {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) : Antitone (addCol a K) := by
  intro i j hij
  have := ha hij
  unfold addCol
  by_cases h : j ≤ K
  · rw [if_pos h, if_pos (hij.trans h)]; omega
  · rw [if_neg h]; omega

/- English proof (translation)
Unfold `hookProd`. Rewrite using `[← mul_div_assoc, div_eq_div_iff (hookDen_pos (addCol_antitone ha K)).ne' (hookDen_pos ha).ne']`. Unfold `hookDen`. Simplify using `only [← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hi : i ≤ K`. Establish `hsplit : ∀ g : Fin l → ℚ, ∏ j ∈ Finset.Ioi i, g j = (∏ j ∈ Finset.Ioc i K, g j) * ∏ j ∈ Finset.Ioi K, g j`. Introduce `g`. Establish `hu : Finset.Ioi i = Finset.Ioc i K ∪ Finset.Ioi K`. Use extensionality with `j`.

Establish `: (i : ℕ) ≤ K` using `hi`. Simplify using `only [Finset.mem_union, Finset.mem_Ioi, Finset.mem_Ioc, Fin.lt_def, Fin.le_def]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hu, Finset.prod_union]`. Rewrite using `[Finset.disjoint_left]`.

Introduce `j h1 h2`. Conclude with `absurd (Finset.mem_Ioc.mp h1).2 (not_le.mpr (Finset.mem_Ioi.mp h2))`. Establish `e1 : ∏ j ∈ Finset.Ioc i K, ((addCol a K i : ℚ) - addCol a K j + (j : ℕ) - (i : ℕ)) = ∏ j ∈ Finset.Ioc i K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ))`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Simplify using `[addCol, hi, (Finset.mem_Ioc.mp hj).2]`.

Establish `e2 : ∏ j ∈ Finset.Ioi K, ((addCol a K i : ℚ) - addCol a K j + (j : ℕ) - (i : ℕ)) = ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, (((a i : ℚ) - (i : ℕ)) + 1 + j)`. Rewrite using `[← prod_Ioi_eq]`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_Ioi.mp hj`. Simplify using `only [addCol, hi, if_true, not_le.mpr hj', if_false, hK j hj']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : ∏ j ∈ Finset.Ioi K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ)) = ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, (((a i : ℚ) - (i : ℕ)) + j)`. Rewrite using `[← prod_Ioi_eq]`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations.

Establish `hj'` using `Finset.mem_Ioi.mp hj`. Simplify using `only [hK j hj']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : ((addCol a K i + (l - ((i : ℕ) + 1))).factorial : ℚ) = ((a i : ℚ) - (i : ℕ) + l) * (a i + (l - ((i : ℕ) + 1))).factorial`.

Establish `: addCol a K i + (l - ((i : ℕ) + 1)) = (a i + (l - ((i : ℕ) + 1))) + 1`. Simplify using `only [addCol, hi, if_true]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Nat.factorial_succ]`. Move the coercions through the operations in `[Nat.cast_sub (show (i : ℕ) + 1 ≤ l from i.2)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `t` using `telescope ((a i : ℚ) - (i : ℕ)) ((K : ℕ) + 1) l K.2`. Rewrite using `[hsplit, hsplit, e1, e2, e3, e4, if_pos hi]`. Move the coercions through the operations in `at t`. Take the linear combination `(-((a i + (l - ((i : ℕ) + 1))).factorial : ℚ) * ∏ j ∈ Finset.Ioc i K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ))) * t`.

Rewrite using `[if_neg hi, one_mul]`. Establish `e : ∀ j, i ≤ j → addCol a K j = a j` using `fun j hj => by`. Simplify using `[addCol, show ¬ j ≤ K from fun h => hi (hj.trans h)]`. Rewrite using `[e i le_rfl]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[e j (Finset.mem_Ioi.mp hj).le]`.
-/
theorem hookProd_addCol {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) (hK : ∀ i, K < i → a i = 0) :
    hookProd (addCol a K) =
      (∏ i : Fin l, if i ≤ K then ((a i : ℚ) + 1 + (K : ℕ) - (i : ℕ)) else 1) * hookProd a := by
  unfold hookProd
  rw [← mul_div_assoc, div_eq_div_iff (hookDen_pos (addCol_antitone ha K)).ne' (hookDen_pos ha).ne']
  unfold hookDen
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ≤ K
  · have hsplit : ∀ g : Fin l → ℚ, ∏ j ∈ Finset.Ioi i, g j =
        (∏ j ∈ Finset.Ioc i K, g j) * ∏ j ∈ Finset.Ioi K, g j := by
      intro g
      have hu : Finset.Ioi i = Finset.Ioc i K ∪ Finset.Ioi K := by
        ext j
        have : (i : ℕ) ≤ K := hi
        simp only [Finset.mem_union, Finset.mem_Ioi, Finset.mem_Ioc, Fin.lt_def, Fin.le_def]
        omega
      rw [hu, Finset.prod_union]
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact absurd (Finset.mem_Ioc.mp h1).2 (not_le.mpr (Finset.mem_Ioi.mp h2))
    have e1 : ∏ j ∈ Finset.Ioc i K, ((addCol a K i : ℚ) - addCol a K j + (j : ℕ) - (i : ℕ)) =
        ∏ j ∈ Finset.Ioc i K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ)) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      simp [addCol, hi, (Finset.mem_Ioc.mp hj).2]
    have e2 : ∏ j ∈ Finset.Ioi K, ((addCol a K i : ℚ) - addCol a K j + (j : ℕ) - (i : ℕ)) =
        ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, (((a i : ℚ) - (i : ℕ)) + 1 + j) := by
      rw [← prod_Ioi_eq]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' := Finset.mem_Ioi.mp hj
      simp only [addCol, hi, if_true, not_le.mpr hj', if_false, hK j hj']
      push_cast
      ring
    have e3 : ∏ j ∈ Finset.Ioi K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ)) =
        ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, (((a i : ℚ) - (i : ℕ)) + j) := by
      rw [← prod_Ioi_eq]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' := Finset.mem_Ioi.mp hj
      simp only [hK j hj']
      push_cast
      ring
    have e4 : ((addCol a K i + (l - ((i : ℕ) + 1))).factorial : ℚ) =
        ((a i : ℚ) - (i : ℕ) + l) * (a i + (l - ((i : ℕ) + 1))).factorial := by
      have : addCol a K i + (l - ((i : ℕ) + 1)) = (a i + (l - ((i : ℕ) + 1))) + 1 := by
        simp only [addCol, hi, if_true]; omega
      rw [this, Nat.factorial_succ]
      push_cast [Nat.cast_sub (show (i : ℕ) + 1 ≤ l from i.2)]
      ring
    have t := telescope ((a i : ℚ) - (i : ℕ)) ((K : ℕ) + 1) l K.2
    rw [hsplit, hsplit, e1, e2, e3, e4, if_pos hi]
    push_cast at t
    linear_combination (-((a i + (l - ((i : ℕ) + 1))).factorial : ℚ) *
      ∏ j ∈ Finset.Ioc i K, ((a i : ℚ) - a j + (j : ℕ) - (i : ℕ))) * t
  · rw [if_neg hi, one_mul]
    have e : ∀ j, i ≤ j → addCol a K j = a j := fun j hj => by
      simp [addCol, show ¬ j ≤ K from fun h => hi (hj.trans h)]
    rw [e i le_rfl]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [e j (Finset.mem_Ioi.mp hj).le]

/- English proof (translation)
Rewrite using `[← Finset.prod_filter]`. Use `symm`. Use `Finset.prod_bij (fun t _ => Fin.castLE K.2 t) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `t _`. Use `t.2` as an intermediate fact.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers. Introduce `t _ t' _ h`. Conclude with `Fin.castLE_injective _ h`. Introduce `j hj`.

Establish `: (j : ℕ) ≤ K` using `(Finset.mem_filter.mp hj).2`. Conclude with `⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩`. Introduce `t _`. Both sides reduce to the same expression.
-/
theorem prod_ite_le (K : Fin l) (g : Fin l → ℚ) :
    (∏ i : Fin l, if i ≤ K then g i else 1) =
      ∏ t : Fin (K + 1), g (Fin.castLE K.2 t) := by
  rw [← Finset.prod_filter]
  symm
  refine Finset.prod_bij (fun t _ => Fin.castLE K.2 t) ?_ ?_ ?_ ?_
  · intro t _
    have := t.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.val_castLE]
    omega
  · intro t _ t' _ h
    exact Fin.castLE_injective _ h
  · intro j hj
    have : (j : ℕ) ≤ K := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro t _
    rfl

variable {σ : Type} (v : Fin l → Fin l → σ)

def minor (i : Fin l) : MvPolynomial σ ℂ :=
  (Matrix.of fun r c : Fin (i + 1) => X (v (Fin.castLE i.2 r) (Fin.castLE i.2 c))).det

def del (a : Fin l → ℕ) : MvPolynomial σ ℂ := ∏ i, minor v i ^ (a i - nextPart a i)

/- English proof (translation)
Simplify using `[del]`.
-/
theorem del_zero : del v 0 = 1 := by simp [del]

/- English proof (translation)
Unfold `del`. Simplify using `only [addCol_exp ha, pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem del_addCol {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) :
    del v (addCol a K) = minor v K * del v a := by
  unfold del
  simp only [addCol_exp ha, pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]
  ring

variable {v}

/- English proof (translation)
Establish `hd : ∀ r j s c, pderiv (v (Fin.castLE hk r) (Fin.castLE hk j)) (X (v (Fin.castLE hk s) (Fin.castLE hk c)) : MvPolynomial σ ℂ) = if r = s ∧ j = c then 1 else 0`. Introduce `r j s c`. Use `split_ifs with h`. Rewrite using `[h.1, h.2, pderiv_X_self]`. Use `pderiv_X_of_ne fun h' => h ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `hv _ _ _ _ h'.symm`. Conclude with `⟨Fin.castLE_injective _ h1, Fin.castLE_injective _ h2⟩`. Use `partition_induction (fun a => (∀ t : Fin l, k ≤ t → a t = 0) → pol (fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c))) (fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) i j (del v a) = ((if i = j then a (Fin.castLE hk j) else 0 : ℕ) : MvPolynomial σ ℂ) * del v a) ?_ …` and prove the remaining obligations. Introduce `_`. Simplify using `[del_zero]`.

Introduce `a K ha _ ih h0`. Establish `hK : (K : ℕ) + 1 ≤ k`. Assume the negation of the conclusion as `h`. Use `h0 K (by omega)` as an intermediate fact. Simplify using `[addCol] at this`.

Establish `ih'` using `ih fun t ht => by`. Use `h0 t ht` as an intermediate fact. Simplify using `only [addCol] at this`. Use linear arithmetic over natural numbers and integers. Establish `hm` using `pol_minor (x := fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c))) (d := fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) hd hK i j hij`.

Express the relevant statement in the definitionally equal form `pol _ _ i j (minor v K) = _ * minor v K at hm`. Rewrite using `[del_addCol v ha, Derivation.leibniz, ih', hm]`. Simplify using `only [addCol, smul_eq_mul, Fin.le_def, Fin.val_castLE, Nat.lt_succ_iff]`. Distinguish the cases in `h : i = j`. Simplify using `only [h, true_and, if_true]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h]`.
-/
theorem pol_del (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) {k : ℕ} (hk : k ≤ l)
    (i j : Fin k) (hij : i ≤ j) (a : Fin l → ℕ) (ha : Antitone a) :
    (∀ t : Fin l, k ≤ t → a t = 0) →
      pol (fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c)))
        (fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) i j (del v a) =
        ((if i = j then a (Fin.castLE hk j) else 0 : ℕ) : MvPolynomial σ ℂ) * del v a := by
  classical
  have hd : ∀ r j s c, pderiv (v (Fin.castLE hk r) (Fin.castLE hk j))
      (X (v (Fin.castLE hk s) (Fin.castLE hk c)) : MvPolynomial σ ℂ) =
      if r = s ∧ j = c then 1 else 0 := by
    intro r j s c
    split_ifs with h
    · rw [h.1, h.2, pderiv_X_self]
    · refine pderiv_X_of_ne fun h' => h ?_
      obtain ⟨h1, h2⟩ := hv _ _ _ _ h'.symm
      exact ⟨Fin.castLE_injective _ h1, Fin.castLE_injective _ h2⟩
  refine partition_induction (fun a => (∀ t : Fin l, k ≤ t → a t = 0) →
      pol (fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c)))
        (fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) i j (del v a) =
        ((if i = j then a (Fin.castLE hk j) else 0 : ℕ) : MvPolynomial σ ℂ) * del v a) ?_ ?_ a ha
  · intro _
    simp [del_zero]
  · intro a K ha _ ih h0
    have hK : (K : ℕ) + 1 ≤ k := by
      by_contra h
      have := h0 K (by omega)
      simp [addCol] at this
    have ih' := ih fun t ht => by
      have := h0 t ht
      simp only [addCol] at this
      omega
    have hm := pol_minor (x := fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c)))
      (d := fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) hd hK i j hij
    change pol _ _ i j (minor v K) = _ * minor v K at hm
    rw [del_addCol v ha, Derivation.leibniz, ih', hm]
    simp only [addCol, smul_eq_mul, Fin.le_def, Fin.val_castLE, Nat.lt_succ_iff]
    by_cases h : i = j
    · simp only [h, true_and, if_true]
      push_cast
      ring
    · simp [h]

/- English proof (translation)
Use `partition_induction (fun a => Formalism.E.fock (del v a) (del v a) = ((hookProd a : ℚ) : ℂ)) ?_ ?_ a ha` and prove the remaining obligations. Simplify using `only [del_zero, hookProd_zero]`. Rewrite using `[fock_eq_sum _ _ {0} (by rw [← C_1, C_apply]; exact support_monomial_subset)]`. Simplify using `[Formalism.A.mfact]`. Introduce `a K ha hK ih`.

Establish `hv' : ∀ r c s e : Fin (K + 1), v (Fin.castLE K.2 r) (Fin.castLE K.2 c) = v (Fin.castLE K.2 s) (Fin.castLE K.2 e) → r = s ∧ c = e`. Introduce `r c s e h`. Take `⟨h1, h2⟩` from `hv _ _ _ _ h`. Conclude with `⟨Fin.castLE_injective _ h1, Fin.castLE_injective _ h2⟩`. Establish `h0 : ∀ t : Fin l, (K : ℕ) + 1 ≤ t → addCol a K t = 0`.

Introduce `t ht`. Establish `: K < t` using `ht`. Simplify using `[addCol, hK t this, not_le.mpr this]`. Establish `h` using `fock_det_mul (fun r c : Fin (K + 1) => v (Fin.castLE K.2 r) (Fin.castLE K.2 c)) hv' (fun t => addCol a K (Fin.castLE K.2 t)) (del v a) (del v (addCol a K)) (del_addCol v ha K) (det_X_ne_zero _ hv') (fun i j hij => by`. Rewrite using `[pol_del hv K.2 i j hij.le _ (addCol_antitone ha K) h0, if_neg hij.ne]`.

Use the proof step `simp)`. Use the proof step `(fun j => by rw [pol_del hv K.2 j j le_rfl _ (addCol_antitone ha K) h0, if_pos rfl])`. Rewrite using `[h, ih, hookProd_addCol ha K hK, prod_ite_le]`. Use `push_cast`. Use `congr 1`.

Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations. Establish `ht : Fin.castLE K.2 t ≤ K`. Use `t.2` as an intermediate fact. Simplify using `only [Fin.le_def, Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [addCol, ht, if_true, Fin.val_castLE]`. Rewrite using `[Nat.cast_sub (show (t : ℕ) ≤ K from ht)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_del (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) (a : Fin l → ℕ)
    (ha : Antitone a) : Formalism.E.fock (del v a) (del v a) = ((hookProd a : ℚ) : ℂ) := by
  classical
  refine partition_induction (fun a => Formalism.E.fock (del v a) (del v a) = ((hookProd a : ℚ) : ℂ))
    ?_ ?_ a ha
  · simp only [del_zero, hookProd_zero]
    rw [fock_eq_sum _ _ {0} (by rw [← C_1, C_apply]; exact support_monomial_subset)]
    simp [Formalism.A.mfact]
  · intro a K ha hK ih
    have hv' : ∀ r c s e : Fin (K + 1), v (Fin.castLE K.2 r) (Fin.castLE K.2 c) =
        v (Fin.castLE K.2 s) (Fin.castLE K.2 e) → r = s ∧ c = e := by
      intro r c s e h
      obtain ⟨h1, h2⟩ := hv _ _ _ _ h
      exact ⟨Fin.castLE_injective _ h1, Fin.castLE_injective _ h2⟩
    have h0 : ∀ t : Fin l, (K : ℕ) + 1 ≤ t → addCol a K t = 0 := by
      intro t ht
      have : K < t := ht
      simp [addCol, hK t this, not_le.mpr this]
    have h := fock_det_mul (fun r c : Fin (K + 1) => v (Fin.castLE K.2 r) (Fin.castLE K.2 c)) hv'
      (fun t => addCol a K (Fin.castLE K.2 t)) (del v a) (del v (addCol a K)) (del_addCol v ha K)
      (det_X_ne_zero _ hv')
      (fun i j hij => by
        rw [pol_del hv K.2 i j hij.le _ (addCol_antitone ha K) h0, if_neg hij.ne]; simp)
      (fun j => by rw [pol_del hv K.2 j j le_rfl _ (addCol_antitone ha K) h0, if_pos rfl])
    rw [h, ih, hookProd_addCol ha K hK, prod_ite_le]
    push_cast
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    have ht : Fin.castLE K.2 t ≤ K := by
      have := t.2
      simp only [Fin.le_def, Fin.val_castLE]
      omega
    simp only [addCol, ht, if_true, Fin.val_castLE]
    rw [Nat.cast_sub (show (t : ℕ) ≤ K from ht)]
    push_cast
    ring

/- English proof (translation)
Introduce `n l h a ha`. Conclude with `fock_del (v := fun r c => (Fin.castLE h r, c)) (fun r c s e hh => ⟨Fin.castLE_injective _ (Prod.mk.inj hh).1, (Prod.mk.inj hh).2⟩) a ha`.
-/
theorem hookNorm : HookNorm := by
  intro n l h a ha
  exact fock_del (v := fun r c => (Fin.castLE h r, c))
    (fun r c s e hh => ⟨Fin.castLE_injective _ (Prod.mk.inj hh).1, (Prod.mk.inj hh).2⟩) a ha

/- English proof (translation)
Introduce `n l h a ha`. Establish `hf` using `fock_del (v := fun r c => ((Fin.castLE h r).rev, c)) (fun r c s e hh => ⟨Fin.castLE_injective _ (Fin.rev_injective (Prod.mk.inj hh).1), (Prod.mk.inj hh).2⟩) a ha`. Establish `e : ∀ i : Fin l, bottomMinor h i = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i + 1))) : ℤ) : MvPolynomial (Fin n × Fin l) ℂ) * minor (fun r c => ((Fin.castLE h r).rev, c)) i`. Introduce `i`. Unfold `minor bottomMinor`.

Rewrite using `[← det_permute]`. Use `congr 1`. Use `Matrix.ext fun r c => ?_` and prove the remaining obligations. Simplify using `only [of_apply, submatrix_apply, id]`. Use `congrArg X (Prod.ext (Fin.ext ?_) rfl)` and prove the remaining obligations.

Use `r.2` as an intermediate fact. Use `i.2` as an intermediate fact. Simplify using `only [Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]`. Use linear arithmetic over natural numbers and integers. Establish `e2 : delBottom h a = (((∏ i : Fin l, Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i + 1))) ^ (a i - nextPart a i) : ℤˣ) : ℤ) : MvPolynomial (Fin n × Fin l) ℂ) * del (fun r c => ((Fin.castLE h r).rev, c)) a`.

Unfold `delBottom del`. Simplify using `only [e, mul_pow, Finset.prod_mul_distrib]`. Simplify using the standard rewrite rules. Rewrite using `[e2, fock_int_left, fock_int_right, hf, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]`. Simplify using the standard rewrite rules.
-/
theorem hookNormBottom : HookNormBottom := by
  intro n l h a ha
  have hf := fock_del (v := fun r c => ((Fin.castLE h r).rev, c))
    (fun r c s e hh => ⟨Fin.castLE_injective _ (Fin.rev_injective (Prod.mk.inj hh).1),
      (Prod.mk.inj hh).2⟩) a ha
  have e : ∀ i : Fin l, bottomMinor h i =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i + 1))) : ℤ) : MvPolynomial (Fin n × Fin l) ℂ) *
        minor (fun r c => ((Fin.castLE h r).rev, c)) i := by
    intro i
    unfold minor bottomMinor
    rw [← det_permute]
    congr 1
    refine Matrix.ext fun r c => ?_
    simp only [of_apply, submatrix_apply, id]
    refine congrArg X (Prod.ext (Fin.ext ?_) rfl)
    have := r.2
    have := i.2
    simp only [Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
    omega
  have e2 : delBottom h a = (((∏ i : Fin l, Equiv.Perm.sign
      (Fin.revPerm : Equiv.Perm (Fin (i + 1))) ^ (a i - nextPart a i) : ℤˣ) : ℤ) :
        MvPolynomial (Fin n × Fin l) ℂ) * del (fun r c => ((Fin.castLE h r).rev, c)) a := by
    unfold delBottom del
    simp only [e, mul_pow, Finset.prod_mul_distrib]
    simp
  rw [e2, fock_int_left, fock_int_right, hf, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self]
  simp

end Partition

end GlobalTheory.MinorNorm
