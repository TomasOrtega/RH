import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv

open Matrix Finset

noncomputable section

namespace AAInvW

/- English proof (translation)
Establish `hone : ∀ j : Fin m, w (φ (Fin.castLE hm j)) (φ (Fin.castLE hm j)) = 1`. Introduce `j`. Establish `h` using `hw (Fin.castLE hm j) (φ (Fin.castLE hm j)) (fun b hb hb' => by`. Use `hφ hb'` as an intermediate fact. Rewrite `hb` using `[this]`.

Conclude with `lt_irrefl _ hb)`. Rewrite using `[h, if_pos rfl]`. Rewrite using `[Finset.sum_eq_single (fun j => φ (Fin.castLE hm j))]`. Simplify using `only [hone, Finset.prod_const_one, one_smul]`. Introduce `c _ hc`.

Distinguish the cases in `hinj : Function.Injective c`. Establish `hex : ∃ j, w (c j) (φ (Fin.castLE hm j)) = 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Apply `hc` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Take `⟨k, hk⟩` from `j`. Use `revert hk`. Use `Nat.strong_induction_on k ?_` and prove the remaining obligations. Introduce `k ih hk`.

Distinguish the cases in `hex : ∃ b : Fin r, b.val < k ∧ c ⟨k, hk⟩ = φ b`. Take `⟨b, hbk, hb⟩` from `hex`. Establish `hbm : b.val < m` using `lt_trans hbk hk`. Establish `e1 : c ⟨b.val, hbm⟩ = φ (Fin.castLE hm ⟨b.val, hbm⟩)` using `ih b.val hbk hbm`. Establish `e2 : Fin.castLE hm ⟨b.val, hbm⟩ = b` using `Fin.ext rfl`.

Rewrite `e1` using `[e2]`. Establish `e3` using `hinj (e1.trans hb.symm)`. Establish `e4 : b.val = k` using `congrArg Fin.val e3`. Use linear arithmetic over natural numbers and integers. Use `push_neg at hex`.

Establish `hw'` using `hw (Fin.castLE hm ⟨k, hk⟩) (c ⟨k, hk⟩) (fun b hb => hex b hb)`. Establish `hne` using `hall ⟨k, hk⟩`. Rewrite `hne` using `[hw']`. Assume the negation of the conclusion as `hcon`. Conclude with `hne (if_neg hcon)`.

Take `⟨j, hj⟩` from `hex`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j) hj, zero_smul]`. Rewrite using `[hq c hinj, smul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem collapse {A : Type*} [AddCommGroup A] [Module ℂ A] {N r m : ℕ} (hm : m ≤ r)
    (φ : Fin r → Fin N) (hφ : Function.Injective φ) (w : Fin N → Fin N → ℂ)
    (hw : ∀ (a : Fin r) (i : Fin N), (∀ b : Fin r, b.val < a.val → i ≠ φ b) →
      w i (φ a) = if i = φ a then 1 else 0)
    (q : (Fin m → Fin N) → A) (hq : ∀ c : Fin m → Fin N, ¬ Function.Injective c → q c = 0) :
    ∑ c : Fin m → Fin N, (∏ j, w (c j) (φ (Fin.castLE hm j))) • q c =
      q (fun j => φ (Fin.castLE hm j)) := by
  have hone : ∀ j : Fin m, w (φ (Fin.castLE hm j)) (φ (Fin.castLE hm j)) = 1 := by
    intro j
    have h := hw (Fin.castLE hm j) (φ (Fin.castLE hm j)) (fun b hb hb' => by
      have := hφ hb'
      rw [this] at hb
      exact lt_irrefl _ hb)
    rw [h, if_pos rfl]
  rw [Finset.sum_eq_single (fun j => φ (Fin.castLE hm j))]
  · simp only [hone, Finset.prod_const_one, one_smul]
  · intro c _ hc
    by_cases hinj : Function.Injective c
    · have hex : ∃ j, w (c j) (φ (Fin.castLE hm j)) = 0 := by
        by_contra hall
        push_neg at hall
        apply hc
        funext j
        obtain ⟨k, hk⟩ := j
        revert hk
        refine Nat.strong_induction_on k ?_
        intro k ih hk
        by_cases hex : ∃ b : Fin r, b.val < k ∧ c ⟨k, hk⟩ = φ b
        · obtain ⟨b, hbk, hb⟩ := hex
          have hbm : b.val < m := lt_trans hbk hk
          have e1 : c ⟨b.val, hbm⟩ = φ (Fin.castLE hm ⟨b.val, hbm⟩) := ih b.val hbk hbm
          have e2 : Fin.castLE hm ⟨b.val, hbm⟩ = b := Fin.ext rfl
          rw [e2] at e1
          have e3 := hinj (e1.trans hb.symm)
          have e4 : b.val = k := congrArg Fin.val e3
          omega
        · push_neg at hex
          have hw' := hw (Fin.castLE hm ⟨k, hk⟩) (c ⟨k, hk⟩) (fun b hb => hex b hb)
          have hne := hall ⟨k, hk⟩
          rw [hw'] at hne
          by_contra hcon
          exact hne (if_neg hcon)
      obtain ⟨j, hj⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, zero_smul]
    · rw [hq c hinj, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hR : ∀ C : Fin t → Fin N, (if StrictMono (fun l => κ (C l)) then (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0) = ∑ σ : Equiv.Perm (Fin t), if StrictMono (fun l => κ (C l)) then W (C ∘ σ) • F (C ∘ σ) else 0`. Introduce `C`. Use `split_ifs with h`. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations.

Rewrite using `[hF C σ, mul_smul]`. Use `first`. Consider the case `rw [Int.cast_smul_eq_zsmul ℂ, zsmul_eq_mul, mul_smul_comm]`. Consider the case `simp only [Algebra.smul_def, map_intCast, ← mul_assoc, (Int.cast_commute _ _).eq]`. Simplify using the standard rewrite rules.

Simplify using `only [hR]`. Rewrite using `[← Fintype.sum_prod_type']`. Use `symm`. Use `Finset.sum_bij_ne_zero (fun p _ _ => p.1 ∘ p.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨C, σ⟩ _ h1 ⟨C', σ'⟩ _ h2 heq`.

Establish `hC : StrictMono (fun l => κ (C l))`. Assume the negation of the conclusion as `hc`. Conclude with `h1 (by simp [hc])`. Establish `hC' : StrictMono (fun l => κ (C' l))`. Assume the negation of the conclusion as `hc`.

Conclude with `h2 (by simp [hc])`. Establish `heq' : C ∘ σ = C' ∘ σ'` using `heq`. Establish `e1 : Set.range (fun l => κ (C l)) = Set.range (fun l => κ (C' l))`. Rewrite using `[← σ.surjective.range_comp (fun l => κ (C l)), ← σ'.surjective.range_comp (fun l => κ (C' l))]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Conclude with `congrArg κ (congrFun heq' x)`. Establish `e2 : (fun l => κ (C l)) = (fun l => κ (C' l))` using `by first`. Consider the case `exact (StrictMono.range_inj hC hC').1 e1`. Consider the case `exact (WellFounded.eq_strictMono_iff_eq_range wellFounded_lt hC hC').1 e1`.

Establish `e3 : C = C'` using `funext fun l => hκ (congrFun e2 l)`. Substitute `e3` using the available equality. Establish `e4 : σ = σ'` using `Equiv.ext fun x => hC.injective (congrArg κ (congrFun heq' x))`. Rewrite using `[e4]`. Introduce `d _ hd`.

Establish `hinj : Function.Injective d`. Assume the negation of the conclusion as `hni`. Apply `hd` to reduce the goal to its premises. Simplify using `[hF0 d hni]`. Establish `hmono : Monotone ((fun l => κ (d l)) ∘ Tuple.sort (fun l => κ (d l)))` using `Tuple.monotone_sort _`.

Establish `hsm : StrictMono (fun l => κ ((d ∘ Tuple.sort (fun l => κ (d l))) l))` using `hmono.strictMono_of_injective ((hκ.comp hinj).comp (Tuple.sort (fun l => κ (d l))).injective)`. Establish `hcomp : (d ∘ Tuple.sort (fun l => κ (d l))) ∘ (Tuple.sort (fun l => κ (d l))).symm = d`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use `⟨(d ∘ Tuple.sort (fun l => κ (d l)), (Tuple.sort (fun l => κ (d l))).symm), Finset.mem_univ _, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[if_pos hsm, hcomp]`. Conclude with `hd`. Conclude with `hcomp`. Introduce and unpack `⟨C, σ⟩ _ h1`.

Establish `hC : StrictMono (fun l => κ (C l))`. Assume the negation of the conclusion as `hc`. Conclude with `h1 (by simp [hc])`. Simplify using `only`. Rewrite using `[if_pos hC]`.
-/
theorem grouping {A : Type*} [Ring A] [Algebra ℂ A] {t N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (F : (Fin t → Fin N) → A)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)),
      F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : A) * F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C : Fin t → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0 := by
  classical
  have hR : ∀ C : Fin t → Fin N,
      (if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0) =
      ∑ σ : Equiv.Perm (Fin t),
        if StrictMono (fun l => κ (C l)) then W (C ∘ σ) • F (C ∘ σ) else 0 := by
    intro C
    split_ifs with h
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [hF C σ, mul_smul]
      first
      | rw [Int.cast_smul_eq_zsmul ℂ, zsmul_eq_mul, mul_smul_comm]
      | simp only [Algebra.smul_def, map_intCast, ← mul_assoc, (Int.cast_commute _ _).eq]
    · simp
  simp only [hR]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => p.1 ∘ p.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨C, σ⟩ _ h1 ⟨C', σ'⟩ _ h2 heq
    have hC : StrictMono (fun l => κ (C l)) := by
      by_contra hc
      exact h1 (by simp [hc])
    have hC' : StrictMono (fun l => κ (C' l)) := by
      by_contra hc
      exact h2 (by simp [hc])
    have heq' : C ∘ σ = C' ∘ σ' := heq
    have e1 : Set.range (fun l => κ (C l)) = Set.range (fun l => κ (C' l)) := by
      rw [← σ.surjective.range_comp (fun l => κ (C l)), ← σ'.surjective.range_comp (fun l => κ (C' l))]
      congr 1
      funext x
      exact congrArg κ (congrFun heq' x)
    have e2 : (fun l => κ (C l)) = (fun l => κ (C' l)) := by
      first
      | exact (StrictMono.range_inj hC hC').1 e1
      | exact (WellFounded.eq_strictMono_iff_eq_range wellFounded_lt hC hC').1 e1
    have e3 : C = C' := funext fun l => hκ (congrFun e2 l)
    subst e3
    have e4 : σ = σ' := Equiv.ext fun x => hC.injective (congrArg κ (congrFun heq' x))
    rw [e4]
  · intro d _ hd
    have hinj : Function.Injective d := by
      by_contra hni
      apply hd
      simp [hF0 d hni]
    have hmono : Monotone ((fun l => κ (d l)) ∘ Tuple.sort (fun l => κ (d l))) :=
      Tuple.monotone_sort _
    have hsm : StrictMono (fun l => κ ((d ∘ Tuple.sort (fun l => κ (d l))) l)) :=
      hmono.strictMono_of_injective ((hκ.comp hinj).comp (Tuple.sort (fun l => κ (d l))).injective)
    have hcomp : (d ∘ Tuple.sort (fun l => κ (d l))) ∘ (Tuple.sort (fun l => κ (d l))).symm = d := by
      funext x
      simp
    refine ⟨(d ∘ Tuple.sort (fun l => κ (d l)), (Tuple.sort (fun l => κ (d l))).symm),
      Finset.mem_univ _, ?_, ?_⟩
    · dsimp only
      rw [if_pos hsm, hcomp]
      exact hd
    · exact hcomp
  · rintro ⟨C, σ⟩ _ h1
    have hC : StrictMono (fun l => κ (C l)) := by
      by_contra hc
      exact h1 (by simp [hc])
    dsimp only
    rw [if_pos hC]

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose]`. Establish `hT : (X * Y)ᵀ = fun l => ∑ k, Y k l • (fun a => X a k)`. Use extensionality with `l a`. Simplify using `[Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_apply, mul_comm]`. Rewrite using `[hT]`.

Use `((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_sum (fun l k => Y k l • (fun a => X a k))).trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Use `((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_smul_univ (fun l => Y (d l) l) (fun l a => X a (d l))).trans ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← Matrix.det_transpose]`.

Both sides reduce to the same expression.
-/
theorem det_mul_expand {m N : ℕ} (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ d : Fin m → Fin N, (∏ l, Y (d l) l) • (Matrix.of fun a l => X a (d l)).det := by
  rw [← Matrix.det_transpose]
  have hT : (X * Y)ᵀ = fun l => ∑ k, Y k l • (fun a => X a k) := by
    ext l a
    simp [Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [hT]
  refine ((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_sum
    (fun l k => Y k l • (fun a => X a k))).trans ?_
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine ((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_smul_univ
    (fun l => Y (d l) l) (fun l a => X a (d l))).trans ?_
  congr 1
  rw [← Matrix.det_transpose]
  rfl

/- English proof (translation)
Establish `hF : ∀ (d : Fin m → Fin N) (τ : Equiv.Perm (Fin m)), (Matrix.of fun a l => X a ((d ∘ τ) l)).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (Matrix.of fun a l => X a (d l)).det`. Introduce `d τ`. Conclude with `Matrix.det_permute' τ (Matrix.of fun a l => X a (d l))`. Establish `hF0 : ∀ d : Fin m → Fin N, ¬ Function.Injective d → (Matrix.of fun a l => X a (d l)).det = 0`. Introduce `d hd`.

Simplify using `only [Function.Injective, not_forall] at hd`. Take `⟨p, q, hpq, hne⟩` from `hd`. Conclude with `Matrix.det_zero_of_column_eq hne (fun a => by simp [hpq])`. Rewrite using `[det_mul_expand X Y]`. Rewrite using `[grouping κ hκ (fun d => (Matrix.of fun a l => X a (d l)).det) hF hF0 (fun d => ∏ l, Y (d l) l)]`.

Use `Finset.sum_congr rfl (fun C _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[smul_eq_mul, mul_comm]`. Use `congr 1`. Rewrite using `[Matrix.det_apply]`.

Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Simplify using `[Units.smul_def, zsmul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem cauchyBinet {m N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ C : Fin m → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (Matrix.of fun a l => X a (C l)).det * (Matrix.of fun i l => Y (C i) l).det else 0 := by
  have hF : ∀ (d : Fin m → Fin N) (τ : Equiv.Perm (Fin m)),
      (Matrix.of fun a l => X a ((d ∘ τ) l)).det =
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * (Matrix.of fun a l => X a (d l)).det := by
    intro d τ
    exact Matrix.det_permute' τ (Matrix.of fun a l => X a (d l))
  have hF0 : ∀ d : Fin m → Fin N, ¬ Function.Injective d → (Matrix.of fun a l => X a (d l)).det = 0 := by
    intro d hd
    simp only [Function.Injective, not_forall] at hd
    obtain ⟨p, q, hpq, hne⟩ := hd
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hpq])
  rw [det_mul_expand X Y]
  rw [grouping κ hκ (fun d => (Matrix.of fun a l => X a (d l)).det) hF hF0 (fun d => ∏ l, Y (d l) l)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with h
  · rw [smul_eq_mul, mul_comm]
    congr 1
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp [Units.smul_def, zsmul_eq_mul]
  · rfl

end AAInvW
