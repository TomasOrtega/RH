import Formalism.RealPlaceAnalysis.StatementE
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.GroupTheory.Perm.Support

open Polynomial Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.REAL

def QTopAlg : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (h : ℂ),
    ∃ d : ℕ → A, (∀ Y : ℂ, qminor E id id (Y + h) = ∑ j ∈ Finset.range (n + 1), Y ^ j • d j) ∧
      (1 ≤ n → d (n - 1) = ∑ a, E a a + algebraMap ℂ A ((n : ℂ) * h - (n : ℂ) * ((n : ℂ) - 1) / 2))

namespace TopAlg

variable {A : Type*} [Ring A] [Algebra ℂ A]

def fac (lin : Prop) [Decidable lin] (B : A) : A[X] := (if lin then X else 0) + C B

/- English proof (translation)
Unfold `fac`. Use `split_ifs`. Conclude with `(natDegree_add_le _ _).trans (by simp [natDegree_X_le])`. Simplify using the standard rewrite rules.
-/
theorem natDegree_fac (lin : Prop) [Decidable lin] (B : A) :
    (fac lin B).natDegree ≤ if lin then 1 else 0 := by
  unfold fac
  split_ifs
  · exact (natDegree_add_le _ _).trans (by simp [natDegree_X_le])
  · simp

def prodP {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A) : A[X] :=
  (List.ofFn fun l => fac (lin l) (B l)).prod

/- English proof (translation)
The claim follows from `| 0, lin, _, B => by simp [prodP] | m + 1, lin, _, B => by unfold prodP rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ] refine (natDegree_mul_le).trans (add_le_add (natDegree_fac _ _) ?_) exact natDegree_prodP (fun l => lin l.succ) (fun l => B l.succ)`.
-/
theorem natDegree_prodP : ∀ {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A),
    (prodP lin B).natDegree ≤ ∑ l, (if lin l then 1 else 0)
  | 0, lin, _, B => by simp [prodP]
  | m + 1, lin, _, B => by
    unfold prodP
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    refine (natDegree_mul_le).trans (add_le_add (natDegree_fac _ _) ?_)
    exact natDegree_prodP (fun l => lin l.succ) (fun l => B l.succ)

/- English proof (translation)
Unfold `prodP`. Rewrite using `[eval₂_list_prod_noncomm]`. Rewrite using `[List.map_ofFn]`. Use `congrArg List.prod (congrArg List.ofFn (funext fun l => ?_))` and prove the remaining obligations. Simplify using `only [Function.comp, fac, eval₂_add, eval₂_C, RingHom.id_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Introduce `p _ k`. Conclude with `(Algebra.commutes Y _).symm`.
-/
theorem eval_prodP {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A) (Y : ℂ) :
    eval₂ (RingHom.id A) (algebraMap ℂ A Y) (prodP lin B) =
      (List.ofFn fun l => (if lin l then algebraMap ℂ A Y else 0) + B l).prod := by
  unfold prodP
  rw [eval₂_list_prod_noncomm]
  · rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun l => ?_))
    simp only [Function.comp, fac, eval₂_add, eval₂_C, RingHom.id_apply]
    split_ifs <;> simp
  · intro p _ k
    exact (Algebra.commutes Y _).symm

/- English proof (translation)
The claim follows from `| 0, B => by simp | m + 1, B => by have ih := coeff_all (fun l : Fin m => B l.succ) have hdeg : (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod.natDegree ≤ m := by have := natDegree_prodP (fun _ : Fin m => True) (fun l => B l.succ) simp only [if_true, Finset.sum_const …`.
-/
theorem coeff_all : ∀ {m : ℕ} (B : Fin m → A),
    (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff m = 1 ∧
      (1 ≤ m → (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff (m - 1) = ∑ l, B l)
  | 0, B => by simp
  | m + 1, B => by
    have ih := coeff_all (fun l : Fin m => B l.succ)
    have hdeg : (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod.natDegree ≤ m := by
      have := natDegree_prodP (fun _ : Fin m => True) (fun l => B l.succ)
      simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
      simpa [prodP, fac] using this
    rw [List.ofFn_succ, List.prod_cons]
    set Q := (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod with hQ
    refine ⟨?_, fun _ => ?_⟩
    · rw [add_mul, coeff_add, coeff_X_mul, ih.1, coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m + 1), mul_zero, add_zero]
    · rw [Fin.sum_univ_succ, add_mul, coeff_add, coeff_C_mul, Nat.add_sub_cancel, ih.1, mul_one]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [coeff_X_mul, add_comm]
        congr 1
        have := ih.2 (by omega)
        simpa using this

end TopAlg

open TopAlg in
/- English proof (translation)
Introduce `A _ _ n E h`. Set `lin : Equiv.Perm (Fin n) → Fin n → Prop` to `fun σ l => σ l = l`. Set `B : Equiv.Perm (Fin n) → Fin n → A` to `fun σ l => (if σ l = l then algebraMap ℂ A (h - ((l : ℕ) : ℂ)) else 0) + E (σ l) l`. Set `Pσ : Equiv.Perm (Fin n) → A[X]` to `fun σ => prodP (lin σ) (B σ)`. Use `⟨fun j => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * (Pσ σ).coeff j, fun Y => ?_, fun hn => ?_⟩` and prove the remaining obligations.

Establish `hfac : ∀ σ : Equiv.Perm (Fin n), (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)).prod = ∑ j ∈ Finset.range (n + 1), Y ^ j • (Pσ σ).coeff j`. Introduce `σ`. Establish `e1 : (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)) = List.ofFn fun l => (if lin σ l then algebraMap ℂ A Y else 0) + B σ l`. Use `congr 1`. Use function extensionality and compare the values at `l`.

Simplify using `only [Tm, id, lin, B]`. Use `split_ifs with hl`. Establish `: Y + h - ((l : ℕ) : ℂ) = Y + (h - ((l : ℕ) : ℂ))` using `by ring`. Rewrite using `[this, map_add]`. Normalize the expressions using the abelian group laws.

Simplify using the standard rewrite rules. Rewrite using `[e1, ← eval_prodP]`. Establish `hdeg : (Pσ σ).natDegree < n + 1`. Use `natDegree_prodP (lin σ) (B σ)` as an intermediate fact. Establish `h2 : ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ n`.

Combine the equalities or inequalities in the displayed calculation. Use `show (prodP (lin σ) (B σ)).natDegree < n + 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[eval₂_eq_sum_range' (RingHom.id A) hdeg]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]`. Unfold `qminor`. Repeatedly rewrite using `[hfac, Finset.mul_sum, mul_smul_comm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.smul_sum]`. Simplify using `only`. Rewrite using `[Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Simplify using `only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]`. Establish `e1 : Pσ 1 = (List.ofFn fun l => (X + C (B 1 l) : A[X])).prod` using `by show prodP (lin 1) (B 1) = _`.

Unfold `prodP fac`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `l`. Rewrite using `[if_pos (show lin 1 l from rfl)]`.

Rewrite using `[e1, (coeff_all (B 1)).2 hn]`. Simplify using `only [B, Equiv.Perm.one_apply, if_true]`. Rewrite using `[Finset.sum_add_distrib, add_comm, ← map_sum]`. Use `congr 1`. Use `congr 1`.

Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `hs : ∑ l : Fin n, ((l : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]`. Use `Finset.sum_range_id_mul_two n` as an intermediate fact. Establish `hc : ((∑ i ∈ Finset.range n, i : ℕ) : ℂ) * 2 = (n : ℂ) * ((n : ℂ) - 1)`.

Rewrite using `[← Nat.cast_ofNat, ← Nat.cast_mul, this]`. Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Nat.cast_mul, Nat.cast_sub (by omega)]`.

Simplify using the standard rewrite rules. Move the coercions through the operations in `at hc`. Take the linear combination `hc / 2`. Rewrite using `[hs]`. Introduce `σ _ hσ`.

Establish `h2 : 2 ≤ σ.support.card` using `Equiv.Perm.two_le_card_support_of_ne_one hσ`. Establish `hdeg` using `natDegree_prodP (lin σ) (B σ)`. Establish `hcount : ∑ l : Fin n, (if lin σ l then 1 else 0) + σ.support.card = n`. Establish `hsupp : σ.support.card = ∑ l : Fin n, (if ¬ lin σ l then 1 else 0)`. Rewrite using `[Finset.sum_boole, Nat.cast_id]`.

Both sides reduce to the same expression. Rewrite using `[hsupp, ← Finset.sum_add_distrib]`. Combine the equalities or inequalities in the displayed calculation. Establish `: (Pσ σ).coeff (n - 1) = 0` using `coeff_eq_zero_of_natDegree_lt (by show (prodP (lin σ) (B σ)).natDegree < n - 1; omega)`. Rewrite using `[this, mul_zero]`.

Introduce `h1`. Conclude with `absurd (Finset.mem_univ _) h1`.
-/
theorem quadratic_top_algebra_holds : QTopAlg := by
  intro A _ _ n E h
  classical

  let lin : Equiv.Perm (Fin n) → Fin n → Prop := fun σ l => σ l = l
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ l =>
    (if σ l = l then algebraMap ℂ A (h - ((l : ℕ) : ℂ)) else 0) + E (σ l) l
  let Pσ : Equiv.Perm (Fin n) → A[X] := fun σ => prodP (lin σ) (B σ)
  refine ⟨fun j => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * (Pσ σ).coeff j, fun Y => ?_, fun hn => ?_⟩
  ·
    have hfac : ∀ σ : Equiv.Perm (Fin n),
        (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)).prod =
          ∑ j ∈ Finset.range (n + 1), Y ^ j • (Pσ σ).coeff j := by
      intro σ
      have e1 : (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)) =
          List.ofFn fun l => (if lin σ l then algebraMap ℂ A Y else 0) + B σ l := by
        congr 1
        funext l
        simp only [Tm, id, lin, B]
        split_ifs with hl
        · have : Y + h - ((l : ℕ) : ℂ) = Y + (h - ((l : ℕ) : ℂ)) := by ring
          rw [this, map_add]
          abel
        · simp
      rw [e1, ← eval_prodP]
      have hdeg : (Pσ σ).natDegree < n + 1 := by
        have := natDegree_prodP (lin σ) (B σ)
        have h2 : ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ n := by
          calc ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ ∑ _l : Fin n, 1 :=
                Finset.sum_le_sum fun l _ => by split_ifs <;> simp
            _ = n := by simp
        show (prodP (lin σ) (B σ)).natDegree < n + 1
        omega
      rw [eval₂_eq_sum_range' (RingHom.id A) hdeg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
    unfold qminor
    simp_rw [hfac, Finset.mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
  ·
    dsimp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]
      have e1 : Pσ 1 = (List.ofFn fun l => (X + C (B 1 l) : A[X])).prod := by
        show prodP (lin 1) (B 1) = _
        unfold prodP fac
        congr 1
        congr 1
        funext l
        rw [if_pos (show lin 1 l from rfl)]
      rw [e1, (coeff_all (B 1)).2 hn]
      simp only [B, Equiv.Perm.one_apply, if_true]
      rw [Finset.sum_add_distrib, add_comm, ← map_sum]
      congr 1
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hs : ∑ l : Fin n, ((l : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]
        have := Finset.sum_range_id_mul_two n
        have hc : ((∑ i ∈ Finset.range n, i : ℕ) : ℂ) * 2 = (n : ℂ) * ((n : ℂ) - 1) := by
          rw [← Nat.cast_ofNat, ← Nat.cast_mul, this]
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0; simp
          · rw [Nat.cast_mul, Nat.cast_sub (by omega)]
            simp
        push_cast at hc
        linear_combination hc / 2
      rw [hs]
    · intro σ _ hσ
      have h2 : 2 ≤ σ.support.card := Equiv.Perm.two_le_card_support_of_ne_one hσ
      have hdeg := natDegree_prodP (lin σ) (B σ)
      have hcount : ∑ l : Fin n, (if lin σ l then 1 else 0) + σ.support.card = n := by
        have hsupp : σ.support.card = ∑ l : Fin n, (if ¬ lin σ l then 1 else 0) := by
          rw [Finset.sum_boole, Nat.cast_id]
          rfl
        rw [hsupp, ← Finset.sum_add_distrib]
        calc ∑ l : Fin n, ((if lin σ l then 1 else 0) + (if ¬lin σ l then 1 else 0)) = ∑ _l : Fin n, 1 :=
              Finset.sum_congr rfl fun l _ => by split_ifs <;> simp_all
          _ = n := by simp
      have : (Pσ σ).coeff (n - 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by show (prodP (lin σ) (B σ)).natDegree < n - 1; omega)
      rw [this, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
