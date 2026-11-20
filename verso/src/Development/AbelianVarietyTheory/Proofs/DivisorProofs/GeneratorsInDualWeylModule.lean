import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.LiftGen

open GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [Fin.eq_zero t, Fin.last]`. Consider the case `succ m ih`. Rewrite using `[Fin.sum_univ_castSucc]`. Proceed by induction on `t using Fin.lastCases with`.

Consider the case `last`. Rewrite using `[Finset.sum_eq_zero, if_neg (by simp)]`. Simplify using the standard rewrite rules. Introduce `i _`. Rewrite using `[if_neg]`.

Use `i.isLt` as an intermediate fact. Simplify using `only [Fin.val_last, Fin.val_castSucc]`. Use linear arithmetic over natural numbers and integers. Consider the case `cast t`. Establish `h` using `ih (fun j => f j.castSucc) t`.

Establish `ht` using `t.isLt`. Simplify using `only [Fin.val_castSucc, Fin.succ_castSucc, Fin.val_last, Fin.succ_last] at h ⊢`. Rewrite using `[h, if_pos (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem telescope {n : ℕ} (f : Fin (n + 1) → ℤ) (t : Fin (n + 1)) :
    ∑ i : Fin n, (if t.val < i.val + 1 then f i.castSucc - f i.succ else 0) = f t - f (Fin.last n) := by
  induction n with
  | zero => simp [Fin.eq_zero t, Fin.last]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    induction t using Fin.lastCases with
    | last =>
      rw [Finset.sum_eq_zero, if_neg (by simp)]
      · simp
      · intro i _
        rw [if_neg]
        have := i.isLt
        simp only [Fin.val_last, Fin.val_castSucc]
        omega
    | cast t =>
      have h := ih (fun j => f j.castSucc) t
      have ht := t.isLt
      simp only [Fin.val_castSucc, Fin.succ_castSucc, Fin.val_last, Fin.succ_last] at h ⊢
      rw [h, if_pos (by omega)]
      simp

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

/- English proof (translation)
The claim follows from `Int.toNat_of_nonneg (sub_nonneg.2 (h i).1)`.
-/
theorem aNum_cast (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (i : Fin n) :
    (aNum lam sg i : ℤ) = sg.w i - lam.w i.succ :=
  Int.toNat_of_nonneg (sub_nonneg.2 (h i).1)

/- English proof (translation)
The claim follows from `Int.toNat_of_nonneg (sub_nonneg.2 (h i).2)`.
-/
theorem bNum_cast (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (i : Fin n) :
    (bNum lam sg i : ℤ) = lam.w i.castSucc - sg.w i :=
  Int.toNat_of_nonneg (sub_nonneg.2 (h i).2)

/- English proof (translation)
Rewrite using `[← telescope lam.w t.castSucc, ← Finset.sum_add_distrib, Nat.cast_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `ha` using `aNum_cast h i`. Establish `hb` using `bNum_cast h i`. Simplify using `only [initW, Fin.val_castSucc]`.

Use `split_ifs`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules.
-/
theorem sum_ab (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (t : Fin n) :
    ((∑ i : Fin n, (aNum lam sg i * initW n (i.val + 1) t) + ∑ i : Fin n, (bNum lam sg i * initW n (i.val + 1) t) : ℕ) : ℤ)
      = lam.w t.castSucc - lam.w (Fin.last n) := by
  rw [← telescope lam.w t.castSucc, ← Finset.sum_add_distrib, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha := aNum_cast h i
  have hb := bNum_cast h i
  simp only [initW, Fin.val_castSucc]
  split_ifs
  · push_cast; linarith
  · simp

/- English proof (translation)
Establish `: b t = ∑ i : Fin n, if i = t then b i else 0` using `by simp`. Rewrite using `[this, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [initW, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem sum_b_succ (b : Fin n → ℕ) (t : Fin n) :
    ∑ i : Fin n, b i * initW n (i.val + 1) t = ∑ i : Fin n, b i * initW n i.val t + b t := by
  have : b t = ∑ i : Fin n, if i = t then b i else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [initW, Fin.ext_iff]
  split_ifs <;> omega

/- English proof (translation)
Simplify using `only [lamN, DomWeight.natW, DomWeight.detShift, Nat.succ_pos, dif_pos]`. Both sides reduce to the same expression.
-/
theorem lamN_eq (t : Fin n) : lamN lam t = (lam.w t.castSucc - lam.w (Fin.last n)).toNat := by
  simp only [lamN, DomWeight.natW, DomWeight.detShift, Nat.succ_pos, dif_pos]
  rfl

/- English proof (translation)
Establish `hn : 0 < n` using `t.pos`. Simplify using `only [DomWeight.natW, DomWeight.detShift, dif_pos hn]`. Rewrite using `[he ⟨n - 1, by omega⟩ (by simp only; omega)]`.
-/
theorem natW_eq (he : EqualLast lam sg) (t : Fin n) : sg.natW t = (sg.w t - lam.w (Fin.last n)).toNat := by
  have hn : 0 < n := t.pos
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  rw [he ⟨n - 1, by omega⟩ (by simp only; omega)]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Use `sum_ab h t` as an intermediate fact. Rewrite using `[lamN_eq, ← this, Int.toNat_natCast]`. Simplify using `[Finset.sum_apply]`.
-/
theorem shape_lam (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), initW n (i.val + 1)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), initW n (i.val + 1)) = lamN lam := by
  funext t
  have := sum_ab h t
  rw [lamN_eq, ← this, Int.toNat_natCast]
  simp [Finset.sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h1` using `sum_ab h t`. Rewrite `h1` using `[sum_b_succ (bNum lam sg)]`. Establish `hb` using `bNum_cast h t`. Rewrite using `[natW_eq he]`.

Simplify using `only [Pi.add_apply, Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Pi.smul_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem shape_sg (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), initW n (i.val + 1)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), initW n i.val) = sg.natW := by
  funext t
  have h1 := sum_ab h t
  rw [sum_b_succ (bNum lam sg)] at h1
  have hb := bNum_cast h t
  rw [natW_eq he]
  simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Pi.smul_apply]
  omega

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h1` using `sum_ab h t`. Rewrite `h1` using `[sum_b_succ (bNum lam sg)]`. Establish `hb` using `bNum_cast h t`. Establish `h2 : ((∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) + (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ))) t = bNum lam sg t`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[h2, natW_eq he, lamN_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem shape_b (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ)) = fun s => lamN lam s - sg.natW s := by
  funext t
  have h1 := sum_ab h t
  rw [sum_b_succ (bNum lam sg)] at h1
  have hb := bNum_cast h t
  have h2 : ((∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ))) t = bNum lam sg t := by
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h2, natW_eq he, lamN_eq]
  omega

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using (dualWeylMul K r n 0 0 0 0).2`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `(dualWeylMul K r n _ _ _ _).1 (hg a) ih`.
-/
theorem prod_mem (K : Type) [Field K] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (hg : ∀ k, g k ∈ dualWeyl K r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl K r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (dualWeylMul K r n 0 0 0 0).2
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (dualWeylMul K r n _ _ _ _).1 (hg a) ih

/- English proof (translation)
Unfold `initMinor`. Rewrite using `[algHom_det_of]`. Simplify using `only [incl, rename_X]`. Both sides reduce to the same expression.
-/
theorem incl_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) (hs' : s ≤ n + 1) :
    incl K n (initMinor K I hs) = initMinor K I hs' := by
  unfold initMinor
  rw [algHom_det_of]
  simp only [incl, rename_X]
  rfl

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← shape_sg h he]`. Conclude with `(dualWeylMul K n n _ _ _ _).1 (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _) (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)`. Establish `h0` using `bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ => bmG_prod (Finset.univ : Finset (Fin (aNum lam sg i))) _ _ _ _ fun k _ => bmLift_minor0 K n (t.1 i k) (Nat.succ_le_of_lt i.isLt)`. Establish `h1` using `bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ => bmG_prod (Finset.univ : Finset (Fin (bNum lam sg i))) _ _ _ _ fun k _ => bmLift_minor1 K n (t.2 i k) (Nat.succ_le_of_lt i.isLt)`.

Use `⟨_, bmG_cast (bmLift_mul h0 h1) (shape_lam h) (shape_b h he) rfl rfl, ?_⟩` and prove the remaining obligations. Unfold `phiGen`. Simplify using `only [map_mul, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Conclude with `(incl_initMinor K _ _ _).symm`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[incl_initMinor K _ _ (Nat.succ_le_succ i.isLt.le)]`. Use `congrArg (fun I => initMinor K I (Nat.succ_le_succ i.isLt.le)) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Proceed by induction on `p using Fin.lastCases with`. Consider the case `last => simp`. Consider the case `cast p => simp`.
-/
theorem piGen_mem_and_lift (K : Type) [Field K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) (t : Gen lam sg) :
    piGen K lam sg t ∈ dualWeyl K n n sg.natW ∧
      ∃ G : BP K n, bmLift K n (lamN lam) (fun s => lamN lam s - sg.natW s) (piGen K lam sg t) G ∧
        phiGen K lam sg t = incl K n G := by
  refine ⟨?_, ?_⟩
  · rw [← shape_sg h he]
    exact (dualWeylMul K n n _ _ _ _).1
      (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)
      (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)
  · have h0 := bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ =>
      bmG_prod (Finset.univ : Finset (Fin (aNum lam sg i))) _ _ _ _ fun k _ =>
        bmLift_minor0 K n (t.1 i k) (Nat.succ_le_of_lt i.isLt)
    have h1 := bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ =>
      bmG_prod (Finset.univ : Finset (Fin (bNum lam sg i))) _ _ _ _ fun k _ =>
        bmLift_minor1 K n (t.2 i k) (Nat.succ_le_of_lt i.isLt)
    refine ⟨_, bmG_cast (bmLift_mul h0 h1) (shape_lam h) (shape_b h he) rfl rfl, ?_⟩
    unfold phiGen
    simp only [map_mul, map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
      exact (incl_initMinor K _ _ _).symm
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
      rw [incl_initMinor K _ _ (Nat.succ_le_succ i.isLt.le)]
      refine congrArg (fun I => initMinor K I (Nat.succ_le_succ i.isLt.le)) ?_
      funext p
      induction p using Fin.lastCases with
      | last => simp
      | cast p => simp

end GlobalTheory.BrCompare.LiftGen
