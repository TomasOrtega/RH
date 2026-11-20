import Mathlib
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.FockHighestWeight

variable {r n : ℕ}

def diagExp (r : ℕ) (ν : Fin n → ℕ) : Fin r × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v.1.val = v.2.val then ν v.2 else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagExp_apply (ν : Fin n → ℕ) (a : Fin r) (s : Fin n) :
    diagExp r ν (a, s) = if a.val = s.val then ν s else 0 := rfl

/- English proof (translation)
Rewrite using `[Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `[rowW, Pi.single_apply]`.
-/
theorem weight_rowW (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = ∑ s : Fin n, m (a, s) := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [rowW, Pi.single_apply]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Rewrite using `[weight_rowW]`. Simplify using `only [diagExp_apply, rowNu]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨a.val, h⟩]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `e`. Conclude with `hb (Fin.ext e.symm)`.

Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Use `s.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem weight_rowW_diagExp (ν : Fin n → ℕ) :
    Finsupp.weight (rowW r n) (diagExp r ν) = rowNu (r := r) ν := by
  funext a
  rw [weight_rowW]
  simp only [diagExp_apply, rowNu]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Fin.ext e.symm)
    · simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg]
    have := s.2
    omega

/- English proof (translation)
Use extensionality with `⟨a, s⟩`. Rewrite using `[diagExp_apply]`. Use `split_ifs with h`. Rewrite using `[← hcol s, Finset.sum_eq_single a]`. Introduce `b _ hb`.

Apply `hoff` to reduce the goal to its premises. Introduce `e`. Conclude with `hb (Fin.ext (e.trans h.symm))`. Simplify using the standard rewrite rules. Conclude with `hoff a s h`.
-/
theorem eq_diagExp_of_offDiag {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ}
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hoff : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0) : m = diagExp r ν := by
  ext ⟨a, s⟩
  rw [diagExp_apply]
  split_ifs with h
  · rw [← hcol s, Finset.sum_eq_single a]
    · intro b _ hb
      apply hoff
      intro e
      exact hb (Fin.ext (e.trans h.symm))
    · simp
  · exact hoff a s h

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro s hs a ha`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ k ih`. Introduce `s hs a ha`. Establish `hk : k < n` using `by have := s.2; omega`. Establish `h` using `hm ⟨k, hk⟩ s hs a`. Establish `h0 : ∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n)) = 0`.

Use `Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations. Establish `hb' : b.val < a.val` using `(Finset.mem_filter.mp hb).2`. Conclude with `ih ⟨k, hk⟩ rfl b (by simp only; omega)`. Rewrite `h` using `[h0]`. Establish `h1 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s)` using `Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _) (by simp)`.

Use linear arithmetic over natural numbers and integers. Introduce `a s h`. Conclude with `key s.val s rfl a h`.
-/
theorem lowerTri_of_interlaced {m : Fin r × Fin n →₀ ℕ} (hm : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 := by
    intro k
    induction k with
    | zero => intro s hs a ha; omega
    | succ k ih =>
      intro s hs a ha
      have hk : k < n := by have := s.2; omega
      have h := hm ⟨k, hk⟩ s hs a
      have h0 : ∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n)) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ?_
        have hb' : b.val < a.val := (Finset.mem_filter.mp hb).2
        exact ih ⟨k, hk⟩ rfl b (by simp only; omega)
      rw [h0] at h
      have h1 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
        Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _) (by simp)
      omega
  intro a s h
  exact key s.val s rfl a h

/- English proof (translation)
Use `eq_diagExp_of_offDiag hcol ?_` and prove the remaining obligations. Establish `key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val ≠ s.val → m (a, s) = 0`. Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`.

Introduce `s hs a ha`. Set `a0 : Fin r` to `⟨s.val, by have := s.2; omega⟩`. Establish `h1 : ∑ t : Fin n, m (a0, t) = ν s`. Rewrite using `[← weight_rowW, hrow]`. Simplify using `[rowNu, a0]`.

Establish `h2 : m (a0, s) = ν s`. Rewrite using `[← h1, Finset.sum_eq_single s]`. Introduce `t _ ht`. Establish `ht' : t.val ≠ s.val` using `fun e => ht (Fin.ext e)`. Break down `lt_or_gt_of_ne ht' with h | h` into its components or cases.

Conclude with `ih t.val (by omega) t rfl a0 (Ne.symm ht')`. Conclude with `hm a0 t h`. Simplify using the standard rewrite rules. Establish `hne : a ≠ a0` using `fun e => ha (by rw [e])`. Establish `h3 : ∑ b ∈ ({a, a0} : Finset (Fin r)), m (b, s) ≤ ∑ b : Fin r, m (b, s)` using `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`.

Rewrite `h3` using `[Finset.sum_pair hne, hcol s]`. Use linear arithmetic over natural numbers and integers. Introduce `a s h`. Conclude with `key s.val s rfl a h`.
-/
theorem eq_diagExp_of_lowerTri (hn : n ≤ r) {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ} (hm : LowerTri m)
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hrow : Finsupp.weight (rowW r n) m = rowNu (r := r) ν) : m = diagExp r ν := by
  refine eq_diagExp_of_offDiag hcol ?_
  have key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val ≠ s.val → m (a, s) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hs a ha
      let a0 : Fin r := ⟨s.val, by have := s.2; omega⟩
      have h1 : ∑ t : Fin n, m (a0, t) = ν s := by
        rw [← weight_rowW, hrow]
        simp [rowNu, a0]
      have h2 : m (a0, s) = ν s := by
        rw [← h1, Finset.sum_eq_single s]
        · intro t _ ht
          have ht' : t.val ≠ s.val := fun e => ht (Fin.ext e)
          rcases lt_or_gt_of_ne ht' with h | h
          · exact ih t.val (by omega) t rfl a0 (Ne.symm ht')
          · exact hm a0 t h
        · simp
      have hne : a ≠ a0 := fun e => ha (by rw [e])
      have h3 : ∑ b ∈ ({a, a0} : Finset (Fin r)), m (b, s) ≤ ∑ b : Fin r, m (b, s) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [Finset.sum_pair hne, hcol s] at h3
      omega
  intro a s h
  exact key s.val s rfl a h

/- English proof (translation)
Rewrite using `[eval_eq', Finset.sum_eq_single (diagExp r ν)]`. Rewrite using `[Finset.prod_eq_one, mul_one]`. Introduce and unpack `⟨a, s⟩ _`. Rewrite using `[diagExp_apply, idFrame]`. Apply the tactic sequence `split_ifs <;> simp`.

Introduce `m hm hne`. Establish `: ¬ ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0` using `fun h => hne (eq_diagExp_of_offDiag (hcol m hm) h)`. Use `push Not at this`. Take `⟨a, s, h1, h2⟩` from `this`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ (a, s)), mul_zero]`.

Simplify using `[idFrame, h1, h2]`. Introduce `h`. Rewrite using `[notMem_support_iff.mp h, zero_mul]`.
-/
theorem eval_idFrame_eq_coeff {R : Type*} [CommRing R] {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) R}
    (hcol : ∀ m ∈ F.support, ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) :
    eval (idFrame R r n) F = coeff (diagExp r ν) F := by
  rw [eval_eq', Finset.sum_eq_single (diagExp r ν)]
  · rw [Finset.prod_eq_one, mul_one]
    rintro ⟨a, s⟩ _
    rw [diagExp_apply, idFrame]
    split_ifs <;> simp
  · intro m hm hne
    have : ¬ ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0 :=
      fun h => hne (eq_diagExp_of_offDiag (hcol m hm) h)
    push Not at this
    obtain ⟨a, s, h1, h2⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ (a, s)), mul_zero]
    simp [idFrame, h1, h2]
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

/- English proof (translation)
Rewrite using `[hw, map_prod]`. Use `Finset.prod_eq_one fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, lpMinor, RingHom.map_det]`. Establish `: ∀ (k : ℕ) (h1 : k ≤ r) (h2 : k ≤ n), (eval (idFrame R r n)).mapMatrix (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin r × Fin n) R)) = 1`. Introduce `k h1 h2`.

Use extensionality with `p q`. Simplify using `[idFrame, Matrix.one_apply, Fin.ext_iff]`. Rewrite using `[this, Matrix.det_one, one_pow]`.
-/
theorem eval_idFrame_hw {R : Type*} [CommRing R] (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  rw [hw, map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, lpMinor, RingHom.map_det]
  have : ∀ (k : ℕ) (h1 : k ≤ r) (h2 : k ≤ n), (eval (idFrame R r n)).mapMatrix
      (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin r × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [idFrame, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one, one_pow]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Assume the negation of the conclusion as `hG`. Use `set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F - eval (idFrame R r n) F • hw R hn ν with hGdef`. Establish `hH` using `hwMem R r n hn ν hν`. Establish `hGm : G ∈ dualWeyl R r n ν` using `Submodule.sub_mem _ (dualWeylRowGraded R r n ν _ F hF) (Submodule.smul_mem _ _ hH)`.

Establish `hGw : G ∈ weightedHomogeneousSubmodule R (rowW r n) (rowNu (r` using `r) ν) := Submodule.sub_mem _ (weightedHomogeneousComponent_mem _ _ _) (Submodule.smul_mem _ _ (hwRowWeight R r n hn ν hν))`. Establish `hd : (colLex r n).degree G ∈ G.support` using `(MonomialOrder.degree_mem_support_iff G).mpr hG`. Establish `he` using `eq_diagExp_of_lowerTri hn (lowerTri_of_interlaced (leadInterlaced R r n ν G hGm hG)) (colSums R r n ν G hGm _ hd) (hGw (mem_support_iff.mp hd))`. Rewrite `hd` using `[he, mem_support_iff]`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[hGdef, coeff_sub, coeff_weightedHomogeneousComponent, if_pos (weight_rowW_diagExp ν), coeff_smul, ← eval_idFrame_eq_coeff (colSums R r n ν F hF), ← eval_idFrame_eq_coeff (colSums R r n ν _ hH), eval_idFrame_hw]`. Simplify using the standard rewrite rules.
-/
theorem component_eq_smul_hw {R : Type} [CommRing R] [IsDomain R] (hn : n ≤ r) {ν : Fin n → ℕ} (hν : Antitone ν)
    {F : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) :
    weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F = eval (idFrame R r n) F • hw R hn ν := by
  classical
  rw [← sub_eq_zero]
  by_contra hG
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F - eval (idFrame R r n) F • hw R hn ν with hGdef
  have hH := hwMem R r n hn ν hν
  have hGm : G ∈ dualWeyl R r n ν :=
    Submodule.sub_mem _ (dualWeylRowGraded R r n ν _ F hF) (Submodule.smul_mem _ _ hH)
  have hGw : G ∈ weightedHomogeneousSubmodule R (rowW r n) (rowNu (r := r) ν) :=
    Submodule.sub_mem _ (weightedHomogeneousComponent_mem _ _ _)
      (Submodule.smul_mem _ _ (hwRowWeight R r n hn ν hν))
  have hd : (colLex r n).degree G ∈ G.support := (MonomialOrder.degree_mem_support_iff G).mpr hG
  have he := eq_diagExp_of_lowerTri hn (lowerTri_of_interlaced (leadInterlaced R r n ν G hGm hG))
    (colSums R r n ν G hGm _ hd) (hGw (mem_support_iff.mp hd))
  rw [he, mem_support_iff] at hd
  apply hd
  rw [hGdef, coeff_sub, coeff_weightedHomogeneousComponent, if_pos (weight_rowW_diagExp ν), coeff_smul,
    ← eval_idFrame_eq_coeff (colSums R r n ν F hF), ← eval_idFrame_eq_coeff (colSums R r n ν _ hH),
    eval_idFrame_hw]
  simp

/- English proof (translation)
Introduce `r n hn ν hν F hF`. Establish `h` using `component_eq_smul_hw hn hν hF`. Unfold `fockQ`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Establish `hw'` using `hwRowWeight ℚ r n hn ν hν (mem_support_iff.mp hm)`. Establish `h2` using `congrArg (coeff m) h`. Rewrite `h2` using `[coeff_weightedHomogeneousComponent, if_pos hw', coeff_smul, smul_eq_mul]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockQ_hw : Formalism.GradedWeylDivisibility.FockQHW := by
  classical
  intro r n hn ν hν F hF
  have h := component_eq_smul_hw hn hν hF
  unfold fockQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' := hwRowWeight ℚ r n hn ν hν (mem_support_iff.mp hm)
  have h2 := congrArg (coeff m) h
  rw [coeff_weightedHomogeneousComponent, if_pos hw', coeff_smul, smul_eq_mul] at h2
  rw [h2]
  ring

end GlobalTheory.FockHighestWeight
