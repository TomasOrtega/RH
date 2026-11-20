import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne

open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

open Polynomial

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pseudo_character_sum_cons_expand {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ) (a : M)
    (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a r) =
      T a * _root_.GlobalTheory.PsChar.alt T n r -
        ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * r i)) := rfl

/- English proof (translation)
Rewrite using `[pseudo_character_sum_cons_expand, pseudo_character_sum_cons_expand, ih]`. Use `congr 1`. Establish `: ∀ i, Function.update (w ∘ τ) i (a * (w ∘ τ) i) = Function.update w (τ i) (a * w (τ i)) ∘ τ` using `fun i => by`. Rewrite using `[Function.update_comp_equiv, Equiv.symm_apply_apply]`. Both sides reduce to the same expression.

Simplify using `only [this, ih]`. Conclude with `Equiv.sum_comp τ (fun j => _root_.GlobalTheory.PsChar.alt T n (Function.update w j (a * w j)))`.
-/
private theorem pseudo_character_sum_cons_comp_perm {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ)
    (ih : ∀ (w : Fin n → M) (τ : Equiv.Perm (Fin n)),
      _root_.GlobalTheory.PsChar.alt T n (w ∘ τ) = _root_.GlobalTheory.PsChar.alt T n w)
    (a : M) (w : Fin n → M) (τ : Equiv.Perm (Fin n)) :
    _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a (w ∘ τ)) =
      _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a w) := by
  rw [pseudo_character_sum_cons_expand, pseudo_character_sum_cons_expand, ih]
  congr 1
  have : ∀ i, Function.update (w ∘ τ) i (a * (w ∘ τ) i) =
      Function.update w (τ i) (a * w (τ i)) ∘ τ := fun i => by
    rw [Function.update_comp_equiv, Equiv.symm_apply_apply]; rfl
  simp only [this, ih]
  exact Equiv.sum_comp τ (fun j => _root_.GlobalTheory.PsChar.alt T n (Function.update w j (a * w j)))

/- English proof (translation)
Rewrite using `[pseudo_character_sum_cons_expand, Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, Fin.cons_update, pseudo_character_sum_cons_expand]`. Establish `hin : ∀ i : Fin n, ∑ l, _root_.GlobalTheory.PsChar.alt T n (Function.update (Function.update r i (a * r i)) l (b * Function.update r i (a * r i) l)) = _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) + ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt …`. Introduce `i`. Establish `hX : (∑ l : Fin n, if l = i then _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) else 0) = _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i))` using `by simp`.

Rewrite using `[← hX, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l = i`. Substitute `hl` using the available equality. Simplify using `[mul_assoc]`.

Rewrite using `[if_neg hl, if_neg hl, zero_add, Function.update_of_ne hl]`. Simplify using `only [← Fin.cons_update, pseudo_character_sum_cons_expand, Finset.sum_sub_distrib, Function.update_self]`. Simplify using `only [hin, Finset.sum_add_distrib, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem alt_cons_cons_lemma_5 {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ)
    (a b : M) (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons a (Fin.cons b r)) =
      T a * T b * _root_.GlobalTheory.PsChar.alt T n r
      - T a * ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * r i))
      - T b * ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * r i))
      - T (a * b) * _root_.GlobalTheory.PsChar.alt T n r
      + ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * b * r i))
      + ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i))
      + ∑ i, ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l)) := by
  rw [pseudo_character_sum_cons_expand, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, Fin.cons_update, pseudo_character_sum_cons_expand]
  have hin : ∀ i : Fin n, ∑ l, _root_.GlobalTheory.PsChar.alt T n
      (Function.update (Function.update r i (a * r i)) l
        (b * Function.update r i (a * r i) l)) =
      _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) +
      ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l)) := by
    intro i
    have hX : (∑ l : Fin n, if l = i then
        _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) else 0) =
        _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) := by simp
    rw [← hX, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp [mul_assoc]
    · rw [if_neg hl, if_neg hl, zero_add, Function.update_of_ne hl]
  simp only [← Fin.cons_update, pseudo_character_sum_cons_expand, Finset.sum_sub_distrib, Function.update_self]
  simp only [hin, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/- English proof (translation)
Rewrite using `[alt_cons_cons_lemma_5, alt_cons_cons_lemma_5, hc a b]`. Establish `hoff : (∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n (Function.update (Function.update r i (a * r i)) l (b * r l))) = ∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n (Function.update (Function.update r i (b * r i)) l (a * r l))`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l = i`.

Simplify using `[hl]`. Rewrite using `[if_neg (Ne.symm hl), if_neg hl, Function.update_comm (Ne.symm hl)]`. Rewrite using `[hoff]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pseudo_character_sum_swap_head_pair {M A : Type*} [Monoid M] [CommRing A] (T : M → A)
    (hc : ∀ a b, T (a * b) = T (b * a)) (n : ℕ) (a b : M) (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons a (Fin.cons b r)) =
      _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons b (Fin.cons a r)) := by
  rw [alt_cons_cons_lemma_5, alt_cons_cons_lemma_5, hc a b]
  have hoff : (∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l))) =
      ∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (b * r i)) l (a * r l)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · simp [hl]
    · rw [if_neg (Ne.symm hl), if_neg hl, Function.update_comm (Ne.symm hl)]
  rw [hoff]
  ring

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v σ`. Both sides reduce to the same expression. Consider the case `succ n ih`.

Establish `htail : ∀ (v : Fin (n + 1) → M) (i j : Fin n), _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap i.succ j.succ) = _root_.GlobalTheory.PsChar.alt T (n + 1) v`. Introduce `v i j`. Establish `hv : v ∘ Equiv.swap i.succ j.succ = Fin.cons (v 0) (Fin.tail v ∘ Equiv.swap i j)`. Use function extensionality and compare the values at `k`. Proceed by induction on `k using Fin.cases with`.

Consider the case `zero`. Simplify using `[Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]`. Consider the case `succ k`. Simplify using `only [Function.comp_apply, Fin.cons_succ, Fin.tail]`. Rewrite using `[(Fin.succ_injective n).swap_apply]`.

Rewrite using `[hv, pseudo_character_sum_cons_comp_perm T n ih, Fin.cons_self_tail]`. Establish `h0 : ∀ (v : Fin (n + 1) → M) (j : Fin n), _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap 0 j.succ) = _root_.GlobalTheory.PsChar.alt T (n + 1) v`. Introduce `v j`. Consider the cases of `n with`. Consider the case `zero => exact j.elim0`.

Consider the case `succ m`. Establish `h01 : ∀ v : Fin (m + 2) → M, _root_.GlobalTheory.PsChar.alt T (m + 2) (v ∘ Equiv.swap 0 (Fin.succ 0)) = _root_.GlobalTheory.PsChar.alt T (m + 2) v`. Introduce `v`. Take `⟨a, b, r, rfl⟩ : ∃ a b r, v = Fin.cons a (Fin.cons b r)` from `⟨_, _, _, (Fin.cons_self_tail v).symm.trans (congrArg _ (Fin.cons_self_tail _).symm)⟩`. Establish `hv : (Fin.cons a (Fin.cons b r) : Fin (m + 2) → M) ∘ Equiv.swap 0 (Fin.succ 0) = Fin.cons b (Fin.cons a r)`.

Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [Function.comp_apply]`.

Rewrite using `[Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => Fin.succ_ne_zero k (Fin.succ_injective _ h))]`. Simplify using the standard rewrite rules. Rewrite using `[hv, pseudo_character_sum_swap_head_pair T hc]`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact h01 v`.

Consider the case `succ k`. Establish `hp : Equiv.swap (0 : Fin (m + 2)) k.succ.succ = Equiv.swap (Fin.succ 0) k.succ.succ * Equiv.swap 0 (Fin.succ 0) * Equiv.swap (Fin.succ 0) k.succ.succ`. Establish `h1 : Equiv.swap (Fin.succ 0) k.succ.succ (0 : Fin (m + 2)) = 0` using `Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero _).symm`. Establish `h2 : Equiv.swap (Fin.succ 0) k.succ.succ (Fin.succ 0 : Fin (m + 2)) = k.succ.succ` using `Equiv.swap_apply_left _ _`. Use `Equiv.swap_apply_apply (Equiv.swap (Fin.succ 0) k.succ.succ) 0 (Fin.succ 0)` as an intermediate fact.

Rewrite `this` using `[h1, h2, Equiv.swap_inv]`. Conclude with `this`. Rewrite using `[hp, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← Function.comp_assoc, ← Function.comp_assoc, htail, h01, htail]`. Establish `hswap : ∀ (v : Fin (n + 1) → M) (x y : Fin (n + 1)), _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap x y) = _root_.GlobalTheory.PsChar.alt T (n + 1) v`. Introduce `v x y`.

Proceed by induction on `x using Fin.cases with`. Consider the case `zero`. Proceed by induction on `y using Fin.cases with`. Consider the case `zero => simp`. Consider the case `succ j => exact h0 v j`.

Consider the case `succ i`. Proceed by induction on `y using Fin.cases with`. Consider the case `zero => rw [Equiv.swap_comm]`. Conclude with `h0 v i`. Consider the case `succ j => exact htail v i j`.

Introduce `v σ`. Use `revert v`. Use `Equiv.Perm.swap_induction_on (motive := fun σ => ∀ v : Fin (n + 1) → M, _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T (n + 1) v) σ (fun v => rfl) ?_` and prove the remaining obligations. Introduce `f x y _ hf v`. Rewrite using `[Equiv.Perm.coe_mul, ← Function.comp_assoc, hf, hswap]`.
-/
private theorem pseudo_character_sum_comp_perm {M A : Type*} [Monoid M] [CommRing A] (T : M → A)
    (hc : ∀ a b, T (a * b) = T (b * a)) :
    ∀ (n : ℕ) (v : Fin n → M) (σ : Equiv.Perm (Fin n)),
      _root_.GlobalTheory.PsChar.alt T n (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T n v := by
  intro n
  induction n with
  | zero => intro v σ; rfl
  | succ n ih =>
    have htail : ∀ (v : Fin (n + 1) → M) (i j : Fin n),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap i.succ j.succ) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v i j
      have hv : v ∘ Equiv.swap i.succ j.succ = Fin.cons (v 0) (Fin.tail v ∘ Equiv.swap i j) := by
        funext k
        induction k using Fin.cases with
        | zero =>
          simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
            (Fin.succ_ne_zero j).symm]
        | succ k =>
          simp only [Function.comp_apply, Fin.cons_succ, Fin.tail]
          rw [(Fin.succ_injective n).swap_apply]
      rw [hv, pseudo_character_sum_cons_comp_perm T n ih, Fin.cons_self_tail]
    have h0 : ∀ (v : Fin (n + 1) → M) (j : Fin n),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap 0 j.succ) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v j
      cases n with
      | zero => exact j.elim0
      | succ m =>
        have h01 : ∀ v : Fin (m + 2) → M,
            _root_.GlobalTheory.PsChar.alt T (m + 2) (v ∘ Equiv.swap 0 (Fin.succ 0)) =
              _root_.GlobalTheory.PsChar.alt T (m + 2) v := by
          intro v
          obtain ⟨a, b, r, rfl⟩ : ∃ a b r, v = Fin.cons a (Fin.cons b r) :=
            ⟨_, _, _, (Fin.cons_self_tail v).symm.trans (congrArg _ (Fin.cons_self_tail _).symm)⟩
          have hv : (Fin.cons a (Fin.cons b r) : Fin (m + 2) → M) ∘ Equiv.swap 0 (Fin.succ 0) =
              Fin.cons b (Fin.cons a r) := by
            funext k
            refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
            · simp
            · simp
            · simp only [Function.comp_apply]
              rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
                (fun h => Fin.succ_ne_zero k (Fin.succ_injective _ h))]
              simp
          rw [hv, pseudo_character_sum_swap_head_pair T hc]
        induction j using Fin.cases with
        | zero => exact h01 v
        | succ k =>
          have hp : Equiv.swap (0 : Fin (m + 2)) k.succ.succ =
              Equiv.swap (Fin.succ 0) k.succ.succ * Equiv.swap 0 (Fin.succ 0) *
                Equiv.swap (Fin.succ 0) k.succ.succ := by
            have h1 : Equiv.swap (Fin.succ 0) k.succ.succ (0 : Fin (m + 2)) = 0 :=
              Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero _).symm
            have h2 : Equiv.swap (Fin.succ 0) k.succ.succ (Fin.succ 0 : Fin (m + 2)) = k.succ.succ :=
              Equiv.swap_apply_left _ _
            have := Equiv.swap_apply_apply (Equiv.swap (Fin.succ 0) k.succ.succ) 0 (Fin.succ 0)
            rw [h1, h2, Equiv.swap_inv] at this
            exact this
          rw [hp, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← Function.comp_assoc,
            ← Function.comp_assoc, htail, h01, htail]
    have hswap : ∀ (v : Fin (n + 1) → M) (x y : Fin (n + 1)),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap x y) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v x y
      induction x using Fin.cases with
      | zero =>
        induction y using Fin.cases with
        | zero => simp
        | succ j => exact h0 v j
      | succ i =>
        induction y using Fin.cases with
        | zero => rw [Equiv.swap_comm]; exact h0 v i
        | succ j => exact htail v i j
    intro v σ
    revert v
    refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ v : Fin (n + 1) → M,
      _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T (n + 1) v)
      σ (fun v => rfl) ?_
    intro f x y _ hf v
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hf, hswap]

open Polynomial in

/- English proof (translation)
Establish `hc : ∀ a b : R, T (a * b) = T (b * a)` using `h.comm`. Establish `hupd : ∀ (m : ℕ) (i : Fin (m + 1)) (w : R), _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Function.update (fun _ => x) i w) = _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons w fun _ => x)`. Introduce `m i w`. Rewrite using `[← pseudo_character_sum_comp_perm _ hc (m + 1) _ (Equiv.swap 0 i)]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Rewrite using `[Function.comp_apply, Equiv.swap_apply_left, Function.update_self, Fin.cons_zero]`. Rewrite using `[Function.comp_apply, Fin.cons_succ, Function.update_of_ne]`. Introduce `hj`.

Conclude with `Fin.succ_ne_zero _ ((Equiv.swap 0 i).injective (hj.trans (Equiv.swap_apply_left 0 i).symm))`. Establish `hrec : ∀ (m : ℕ) (y : R), _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 2) (Fin.cons y fun _ => x) = T y * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (fun _ => x) - (m + 1) * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons (y * x) fun _ …`. Introduce `m y`. Rewrite using `[pseudo_character_sum_cons_expand]`. Simplify using `only [hupd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hcoef : ∀ m : ℕ, ∃ c : ℕ → k, (∀ y, _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons y fun _ => x) = ∑ j ∈ Finset.range (m + 1), c j * T (y * x ^ j)) ∧ c m = (-1) ^ m * (m.factorial : k)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero`. Use `⟨fun _ => 1, fun y => ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[pseudo_character_sum_cons_expand]`. Simplify using the standard rewrite rules. Conclude with `mul_one (T y)`.

Consider the case `succ m ih`. Take `⟨c, hc1, hc2⟩` from `ih`. Use `⟨fun j => if j = 0 then _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (fun _ => x) else -((m : k) + 1) * c (j - 1), fun y => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hrec, hc1, Finset.sum_range_succ' _ (m + 1)]`. Simplify using `only [Nat.add_one_ne_zero, if_false, if_true, Nat.add_sub_cancel, pow_zero, mul_one, pow_succ', ← mul_assoc, Finset.mul_sum]`.

Rewrite using `[sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, hc2, Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc1, hc2⟩` from `hcoef d`. Establish `hzero : ∀ y, ∑ j ∈ Finset.range (d + 1), c j * T (y * x ^ j) = 0` using `fun y => (hc1 y).symm.trans (h.alt_eq_zero _)`. Establish `hcd : c d ≠ 0`.

Rewrite using `[hc2]`. Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero d)`. Establish `hdeg : (∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ)).degree < (d : WithBot ℕ)` using `Polynomial.degree_sum_fin_lt _`. Use `⟨X ^ d + ∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ), Polynomial.monic_X_pow_add hdeg, ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]), Polynomial.natDegree_X_pow]`.

Establish `e` using `hzero y`. Rewrite `e` using `[Finset.sum_range_succ]`. Simplify using `only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C, add_mul, Finset.sum_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => c i / c d * T (x ^ i * y)) d, hc]`. Establish `hs : ∑ i ∈ Finset.range d, c i / c d * T (x ^ i * y) = (∑ i ∈ Finset.range d, c i * T (y * x ^ i)) / c d`.

Rewrite using `[Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hc]; ring`. Rewrite using `[hs]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`.
-/
theorem _root_.GlobalTheory.PsChar.cayleyHamilton (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : _root_.GlobalTheory.PsChar.IsPsChar d (fun x => T x)) (x : R) :
    ∃ p : Polynomial k, p.Monic ∧ p.natDegree = d ∧ ∀ y : R, T (Polynomial.aeval x p * y) = 0 := by
  have hc : ∀ a b : R, T (a * b) = T (b * a) := h.comm
  have hupd : ∀ (m : ℕ) (i : Fin (m + 1)) (w : R),
      _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Function.update (fun _ => x) i w) =
        _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons w fun _ => x) := by
    intro m i w
    rw [← pseudo_character_sum_comp_perm _ hc (m + 1) _ (Equiv.swap 0 i)]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Function.comp_apply, Equiv.swap_apply_left, Function.update_self, Fin.cons_zero]
    · rw [Function.comp_apply, Fin.cons_succ, Function.update_of_ne]
      intro hj
      exact Fin.succ_ne_zero _
        ((Equiv.swap 0 i).injective (hj.trans (Equiv.swap_apply_left 0 i).symm))
  have hrec : ∀ (m : ℕ) (y : R),
      _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 2) (Fin.cons y fun _ => x) =
        T y * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (fun _ => x) -
          (m + 1) * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1)
            (Fin.cons (y * x) fun _ => x) := by
    intro m y
    rw [pseudo_character_sum_cons_expand]
    simp only [hupd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hcoef : ∀ m : ℕ, ∃ c : ℕ → k,
      (∀ y, _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons y fun _ => x) =
        ∑ j ∈ Finset.range (m + 1), c j * T (y * x ^ j)) ∧
      c m = (-1) ^ m * (m.factorial : k) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => 1, fun y => ?_, by simp⟩
      rw [pseudo_character_sum_cons_expand]
      simp
      exact mul_one (T y)
    | succ m ih =>
      obtain ⟨c, hc1, hc2⟩ := ih
      refine ⟨fun j => if j = 0 then _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1)
        (fun _ => x) else -((m : k) + 1) * c (j - 1), fun y => ?_, ?_⟩
      · rw [hrec, hc1, Finset.sum_range_succ' _ (m + 1)]
        simp only [Nat.add_one_ne_zero, if_false, if_true, Nat.add_sub_cancel, pow_zero, mul_one,
          pow_succ', ← mul_assoc, Finset.mul_sum]
        rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by ring
        · ring
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, hc2, Nat.factorial_succ]
        push_cast
        ring
  obtain ⟨c, hc1, hc2⟩ := hcoef d
  have hzero : ∀ y, ∑ j ∈ Finset.range (d + 1), c j * T (y * x ^ j) = 0 := fun y =>
    (hc1 y).symm.trans (h.alt_eq_zero _)
  have hcd : c d ≠ 0 := by
    rw [hc2]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero d)
  have hdeg : (∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) :=
    Polynomial.degree_sum_fin_lt _
  refine ⟨X ^ d + ∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ), Polynomial.monic_X_pow_add hdeg, ?_,
    fun y => ?_⟩
  · rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  · have e := hzero y
    rw [Finset.sum_range_succ] at e
    simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
      add_mul, Finset.sum_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => c i / c d * T (x ^ i * y)) d, hc]
    have hs : ∑ i ∈ Finset.range d, c i / c d * T (x ^ i * y) =
        (∑ i ∈ Finset.range d, c i * T (y * x ^ i)) / c d := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hc]; ring
    rw [hs]
    field_simp
    linear_combination e

end GlobalTheory.PsChar
