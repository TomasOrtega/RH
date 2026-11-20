import Mathlib
import Formalism.RealPlaceAnalysis.StatementE
open Finset

namespace GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}

def oprod (S : Finset (Fin n)) (e : Fin n → A) : A :=
  (List.ofFn fun k => if k ∈ S then e k else 1).prod

/- English proof (translation)
Establish `h` using `(MultilinearMap.mkPiAlgebraFin ℂ n A).map_add_univ e (fun k => c k • (1 : A))`. Simplify using `only [MultilinearMap.mkPiAlgebraFin_apply] at h`. Establish `h0 : (fun k => c k • (1 : A) + e k) = e + fun k => c k • (1 : A)`. Use function extensionality and compare the values at `k`. Simplify using `[add_comm]`.

Rewrite using `[h0, h]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Establish `h1` using `(MultilinearMap.mkPiAlgebraFin ℂ n A).map_smul_univ (fun k => if k ∈ S then 1 else c k) (fun k => if k ∈ S then e k else 1)`. Simplify using `only [MultilinearMap.mkPiAlgebraFin_apply] at h1`. Establish `h2 : S.piecewise e (fun k => c k • (1 : A)) = fun k => (if k ∈ S then (1 : ℂ) else c k) • (if k ∈ S then e k else 1)`.

Apply the tactic sequence `funext k; by_cases hk : k ∈ S <;> simp [hk]`. Rewrite using `[h2, h1, oprod]`. Use `congr 1`. Rewrite using `[← Finset.prod_mul_prod_compl S, Finset.prod_eq_one (s := S) (fun k hk => by simp [hk]), one_mul]`. Conclude with `Finset.prod_congr rfl fun k hk => by simp [Finset.mem_compl.1 hk]`.
-/
theorem prod_add_expand [Algebra ℂ A] (c : Fin n → ℂ) (e : Fin n → A) :
    (List.ofFn fun k => c k • (1 : A) + e k).prod =
      ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, c k) • oprod S e := by
  have h := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_add_univ e (fun k => c k • (1 : A))
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at h
  have h0 : (fun k => c k • (1 : A) + e k) = e + fun k => c k • (1 : A) := by
    funext k; simp [add_comm]
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_smul_univ (fun k => if k ∈ S then 1 else c k)
    (fun k => if k ∈ S then e k else 1)
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at h1
  have h2 : S.piecewise e (fun k => c k • (1 : A)) =
      fun k => (if k ∈ S then (1 : ℂ) else c k) • (if k ∈ S then e k else 1) := by
    funext k; by_cases hk : k ∈ S <;> simp [hk]
  rw [h2, h1, oprod]
  congr 1
  rw [← Finset.prod_mul_prod_compl S, Finset.prod_eq_one (s := S) (fun k hk => by simp [hk]), one_mul]
  exact Finset.prod_congr rfl fun k hk => by simp [Finset.mem_compl.1 hk]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => by_cases h : p a <;> simp [h, ih]`.
-/
theorem list_ite {ι : Type} (p : ι → Prop) [DecidablePred p] (e : ι → A) (l : List ι) :
    (l.map fun k => if p k then e k else 1).prod = ((l.filter fun k => decide (p k)).map e).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/- English proof (translation)
Rewrite using `[oprod, List.ofFn_eq_map, list_ite]`. Use `congr 2`. Establish `h1 : ((List.finRange n).filter fun k => decide (k ∈ S)).Pairwise (· < ·)` using `(List.pairwise_lt_finRange n).filter _`. Conclude with `h1.eq_of_mem_iff hl (fun k => by simp [h])`.
-/
theorem oprod_eq (S : Finset (Fin n)) (e : Fin n → A) (l : List (Fin n)) (hl : l.Pairwise (· < ·))
    (h : ∀ k, k ∈ l ↔ k ∈ S) : oprod S e = (l.map e).prod := by
  rw [oprod, List.ofFn_eq_map, list_ite]
  congr 2
  have h1 : ((List.finRange n).filter fun k => decide (k ∈ S)).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange n).filter _
  exact h1.eq_of_mem_iff hl (fun k => by simp [h])

def subdet (E : Fin n → Fin n → A) (S : Finset (Fin n)) : A :=
  ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ S → σ k = k),
    ((Equiv.Perm.sign σ : ℤ) : A) * oprod S (fun k => E (σ k) k)

/- English proof (translation)
Unfold `Formalism.REAL.qdet Formalism.REAL.qminor`. Establish `h : ∀ σ : Equiv.Perm (Fin n), (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod = ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (if σ k = k then u - (k : ℂ) else 0)) • oprod S (fun k => E (σ k) k)`. Introduce `σ`. Rewrite using `[← prod_add_expand]`. Use `congr 2`.

Use function extensionality and compare the values at `k`. Apply the tactic sequence `by_cases hk : σ k = k <;> simp [Formalism.REAL.Tm, hk, Algebra.algebraMap_eq_smul_one]`. Repeatedly rewrite using `[h, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations.

Rewrite using `[subdet, Finset.smul_sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm]`. Use `split_ifs with hσ`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun k hk => by rw [if_pos (hσ k (Finset.mem_compl.1 hk))]`. Use `push Not at hσ`. Take `⟨k, hk, hk'⟩` from `hσ`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_compl.2 hk) (if_neg hk'), zero_smul]`.
-/
theorem qdet_expand [Algebra ℂ A] (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet E u = ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (u - (k : ℂ))) • subdet E S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  have h : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (if σ k = k then u - (k : ℂ) else 0)) •
        oprod S (fun k => E (σ k) k) := by
    intro σ
    rw [← prod_add_expand]
    congr 2
    funext k
    by_cases hk : σ k = k <;> simp [Formalism.REAL.Tm, hk, Algebra.algebraMap_eq_smul_one]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [subdet, Finset.smul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]
  split_ifs with hσ
  · congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [if_pos (hσ k (Finset.mem_compl.1 hk))]
  · push Not at hσ
    obtain ⟨k, hk, hk'⟩ := hσ
    rw [Finset.prod_eq_zero (Finset.mem_compl.2 hk) (if_neg hk'), zero_smul]

/- English proof (translation)
Establish `: univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ (∅ : Finset (Fin n)) → σ k = k) = {1}`. Use extensionality with `σ`. Simplify using `[Equiv.ext_iff]`. Rewrite using `[subdet, this, Finset.sum_singleton, oprod_eq _ _ [] (by simp) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem subdet_empty (E : Fin n → Fin n → A) : subdet E ∅ = 1 := by
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ (∅ : Finset (Fin n)) → σ k = k) = {1} := by
    ext σ; simp [Equiv.ext_iff]
  rw [subdet, this, Finset.sum_singleton, oprod_eq _ _ [] (by simp) (by simp)]
  simp

/- English proof (translation)
Establish `: univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ ({i} : Finset (Fin n)) → σ k = k) = {1}`. Use extensionality with `σ`. Simplify using `only [mem_filter, mem_univ, true_and, mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Assume the negation of the conclusion as `hne`. Establish `hne' : σ k ≠ k` using `fun h' => hne (by simp [h'])`.

Conclude with `hne' (σ.injective (h _ hne'))`. Simplify using `[h k hk]`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Rewrite using `[subdet, this, Finset.sum_singleton, oprod_eq _ _ [i] (by simp) (by simp)]`.

Simplify using the standard rewrite rules.
-/
theorem subdet_single (E : Fin n → Fin n → A) (i : Fin n) : subdet E {i} = E i i := by
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ ({i} : Finset (Fin n)) → σ k = k) = {1} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      ext k
      by_cases hk : k = i
      · subst hk
        by_contra hne
        have hne' : σ k ≠ k := fun h' => hne (by simp [h'])
        exact hne' (σ.injective (h _ hne'))
      · simp [h k hk]
    · rintro rfl; simp
  rw [subdet, this, Finset.sum_singleton, oprod_eq _ _ [i] (by simp) (by simp)]
  simp

/- English proof (translation)
Establish `hne : i ≠ j` using `hij.ne`. Establish `: univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ ({i, j} : Finset (Fin n)) → σ k = k) = {1, Equiv.swap i j}`. Use extensionality with `σ`. Simplify using `only [mem_filter, mem_univ, true_and, mem_singleton, mem_insert, not_or]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `key : ∀ k, k = i ∨ k = j → σ k = i ∨ σ k = j`. Introduce `k hk`. Assume the negation of the conclusion as `hc`. Establish `h1` using `σ.injective (h _ (not_or.1 hc))`.

Rewrite `hc` using `[h1]`. Conclude with `hc hk`. Establish `hinj : σ i ≠ σ j` using `σ.injective.ne hne`. Apply the tactic sequence `rcases key i (Or.inl rfl) with hi | hi <;> rcases key j (Or.inr rfl) with hj | hj`. Conclude with `absurd (hi.trans hj.symm) hinj`.

Use `left`. Use `Equiv.ext fun k => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : k = i`. Simplify using `[h1, hi]`. Distinguish the cases in `h2 : k = j`.

Simplify using `[h2, hj]`. Simplify using `[h k ⟨h1, h2⟩]`. Use `right`. Use `Equiv.ext fun k => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : k = i`.

Simplify using `[h1, hi]`. Distinguish the cases in `h2 : k = j`. Simplify using `[h2, hj]`. Rewrite using `[h k ⟨h1, h2⟩, Equiv.swap_apply_of_ne_of_ne h1 h2]`. Conclude with `absurd (hi.trans hj.symm) hinj`.

Introduce and unpack `(rfl | rfl) k hk`. Simplify using the standard rewrite rules. Conclude with `Equiv.swap_apply_of_ne_of_ne hk.1 hk.2`. Establish `h1 : (1 : Equiv.Perm (Fin n)) ≠ Equiv.swap i j` using `fun h => hne (Equiv.swap_eq_one_iff.1 h.symm)`. Rewrite using `[subdet, this, Finset.sum_pair h1, oprod_eq _ _ [i, j] (by simp [hij]) (by simp), oprod_eq _ _ [i, j] (by simp [hij]) (by simp), Equiv.Perm.sign_swap hne]`.

Simplify using `[sub_eq_add_neg]`.
-/
theorem subdet_pair (E : Fin n → Fin n → A) (i j : Fin n) (hij : i < j) :
    subdet E {i, j} = E i i * E j j - E j i * E i j := by
  have hne : i ≠ j := hij.ne
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ ({i, j} : Finset (Fin n)) → σ k = k) =
      {1, Equiv.swap i j} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton, mem_insert, not_or]
    constructor
    · intro h
      have key : ∀ k, k = i ∨ k = j → σ k = i ∨ σ k = j := by
        intro k hk
        by_contra hc
        have h1 := σ.injective (h _ (not_or.1 hc))
        rw [h1] at hc
        exact hc hk
      have hinj : σ i ≠ σ j := σ.injective.ne hne
      rcases key i (Or.inl rfl) with hi | hi <;> rcases key j (Or.inr rfl) with hj | hj
      · exact absurd (hi.trans hj.symm) hinj
      · left
        refine Equiv.ext fun k => ?_
        by_cases h1 : k = i
        · simp [h1, hi]
        by_cases h2 : k = j
        · simp [h2, hj]
        simp [h k ⟨h1, h2⟩]
      · right
        refine Equiv.ext fun k => ?_
        by_cases h1 : k = i
        · simp [h1, hi]
        by_cases h2 : k = j
        · simp [h2, hj]
        rw [h k ⟨h1, h2⟩, Equiv.swap_apply_of_ne_of_ne h1 h2]
      · exact absurd (hi.trans hj.symm) hinj
    · rintro (rfl | rfl) k hk
      · simp
      · exact Equiv.swap_apply_of_ne_of_ne hk.1 hk.2
  have h1 : (1 : Equiv.Perm (Fin n)) ≠ Equiv.swap i j := fun h => hne (Equiv.swap_eq_one_iff.1 h.symm)
  rw [subdet, this, Finset.sum_pair h1, oprod_eq _ _ [i, j] (by simp [hij]) (by simp),
    oprod_eq _ _ [i, j] (by simp [hij]) (by simp), Equiv.Perm.sign_swap hne]
  simp [sub_eq_add_neg]

/- English proof (translation)
Establish `h0 : univ.filter (fun S : Finset (Fin n) => S.card = 0) = {∅}`. Use extensionality with `S`. Simplify using the standard rewrite rules. Establish `h1 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 1), F S = ∑ i, F {i}`. Use `symm`.

Use `Finset.sum_bij (fun i _ => {i}) (by simp) (by simp) ?_ (by simp)` and prove the remaining obligations. Introduce `S hS`. Take `⟨a, rfl⟩` from `Finset.card_eq_one.1 (mem_filter.1 hS).2`. Conclude with `⟨a, mem_univ _, rfl⟩`. Establish `h2 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 2), F S = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j}`.

Rewrite using `[Finset.sum_sigma']`. Use `symm`. Use `Finset.sum_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_ (by simp)` and prove the remaining obligations. Introduce and unpack `⟨i, j⟩ hp`. Establish `: i < j` using `by simpa using hp`.

Simplify using `[Finset.card_pair this.ne]`. Introduce and unpack `⟨i, j⟩ hp ⟨i', j'⟩ hp' h`. Establish `a1 : i < j` using `by simpa using hp`. Establish `a2 : i' < j'` using `by simpa using hp'`. Establish `h' : ({i, j} : Finset (Fin n)) = {i', j'}` using `h`.

Establish `b1 : i ∈ ({i', j'} : Finset (Fin n))` using `h' ▸ by simp`. Establish `b2 : j ∈ ({i', j'} : Finset (Fin n))` using `h' ▸ by simp`. Establish `b3 : i' ∈ ({i, j} : Finset (Fin n))` using `h' ▸ by simp`. Simplify using `only [mem_insert, mem_singleton] at b1 b2 b3`. Establish `: i = i' ∧ j = j'` using `by omega`.

Take `⟨rfl, rfl⟩` from `this`. Both sides reduce to the same expression. Introduce `S hS`. Take `⟨a, b, hab, rfl⟩` from `Finset.card_eq_two.1 (mem_filter.1 hS).2`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases.

Conclude with `⟨⟨a, b⟩, by simpa using h, rfl⟩`. Conclude with `⟨⟨b, a⟩, by simpa using h, Finset.pair_comm _ _⟩`. Establish `h0' : F ∅ = ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 0), F S`. Rewrite using `[h0, Finset.sum_singleton]`. Rewrite using `[← h1, ← h2, h0']`.

Simplify using `only [Finset.sum_filter, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases hc : S.card with _ | _ | _ | m <;> simp`.
-/
theorem sum_split {M : Type} [AddCommMonoid M] (F : Finset (Fin n) → M) :
    ∑ S, F S = F ∅ + ∑ i, F {i} + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j} +
      ∑ S ∈ univ.filter (fun S : Finset (Fin n) => 3 ≤ S.card), F S := by
  have h0 : univ.filter (fun S : Finset (Fin n) => S.card = 0) = {∅} := by
    ext S; simp
  have h1 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 1), F S = ∑ i, F {i} := by
    symm
    refine Finset.sum_bij (fun i _ => {i}) (by simp) (by simp) ?_ (by simp)
    intro S hS
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (mem_filter.1 hS).2
    exact ⟨a, mem_univ _, rfl⟩
  have h2 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 2), F S =
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j} := by
    rw [Finset.sum_sigma']
    symm
    refine Finset.sum_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_ (by simp)
    · rintro ⟨i, j⟩ hp
      have : i < j := by simpa using hp
      simp [Finset.card_pair this.ne]
    · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' h
      have a1 : i < j := by simpa using hp
      have a2 : i' < j' := by simpa using hp'
      have h' : ({i, j} : Finset (Fin n)) = {i', j'} := h
      have b1 : i ∈ ({i', j'} : Finset (Fin n)) := h' ▸ by simp
      have b2 : j ∈ ({i', j'} : Finset (Fin n)) := h' ▸ by simp
      have b3 : i' ∈ ({i, j} : Finset (Fin n)) := h' ▸ by simp
      simp only [mem_insert, mem_singleton] at b1 b2 b3
      have : i = i' ∧ j = j' := by omega
      obtain ⟨rfl, rfl⟩ := this
      rfl
    · intro S hS
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (mem_filter.1 hS).2
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨⟨a, b⟩, by simpa using h, rfl⟩
      · exact ⟨⟨b, a⟩, by simpa using h, Finset.pair_comm _ _⟩
  have h0' : F ∅ = ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 0), F S := by
    rw [h0, Finset.sum_singleton]
  rw [← h1, ← h2, h0']
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases hc : S.card with _ | _ | _ | m <;> simp

end GlobalTheory.CapelliTop

namespace GlobalTheory
open CapelliTop

/- English proof (translation)
Introduce `A _ _ n E`. Set `p : Finset (Fin n) → Polynomial ℂ` to `fun S => ∏ k ∈ Sᶜ, (Polynomial.X - Polynomial.C (k : ℂ))`. Use `⟨fun d => ∑ S ∈ univ.filter (fun S : Finset (Fin n) => 3 ≤ S.card), (p S).coeff d • subdet E S, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[qdet_expand, sum_split]`. Use `congr 1`.

Use `congr 1`. Use `congr 1`. Rewrite using `[subdet_empty, Finset.compl_empty]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[subdet_single, Finset.compl_singleton]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[subdet_pair E i j (mem_filter.1 hj).2]`. Use `congr 2`. Use extensionality with `k`. Simplify using `[and_comm]`.

Repeatedly rewrite using `[Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun S hS => ?_` and prove the remaining obligations. Establish `hS3` using `(mem_filter.1 hS).2`. Establish `hle : S.card ≤ n` using `by simpa using Finset.card_le_univ S`.

Establish `hdeg : (p S).natDegree < n - 2`. Establish `: (p S).natDegree = Sᶜ.card` using `Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _`. Rewrite using `[this, Finset.card_compl, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hev : (p S).eval u = ∏ k ∈ Sᶜ, (u - (k : ℂ))`.

Simplify using `[p, Polynomial.eval_prod]`. Rewrite using `[← hev, Polynomial.eval_eq_sum_range' hdeg, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`.
-/
theorem qdet_top_three_orders :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), ∃ Rm : ℕ → A, ∀ u : ℂ,
      Formalism.REAL.qdet E u = (∏ l : Fin n, (u - (l : ℂ))) • (1 : A) +
        ∑ i : Fin n, (∏ l ∈ univ.erase i, (u - (l : ℂ))) • E i i +
        ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j),
          (∏ l ∈ (univ.erase i).erase j, (u - (l : ℂ))) • (E i i * E j j - E j i * E i j) +
        ∑ d ∈ range (n - 2), u ^ d • Rm d := by
  intro A _ _ n E
  let p : Finset (Fin n) → Polynomial ℂ := fun S => ∏ k ∈ Sᶜ, (Polynomial.X - Polynomial.C (k : ℂ))
  refine ⟨fun d => ∑ S ∈ univ.filter (fun S : Finset (Fin n) => 3 ≤ S.card),
    (p S).coeff d • subdet E S, fun u => ?_⟩
  rw [qdet_expand, sum_split]
  congr 1
  · congr 1
    · congr 1
      · rw [subdet_empty, Finset.compl_empty]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [subdet_single, Finset.compl_singleton]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [subdet_pair E i j (mem_filter.1 hj).2]
      congr 2
      ext k; simp [and_comm]
  · simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hS3 := (mem_filter.1 hS).2
    have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hdeg : (p S).natDegree < n - 2 := by
      have : (p S).natDegree = Sᶜ.card := Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _
      rw [this, Finset.card_compl, Fintype.card_fin]
      omega
    have hev : (p S).eval u = ∏ k ∈ Sᶜ, (u - (k : ℂ)) := by
      simp [p, Polynomial.eval_prod]
    rw [← hev, Polynomial.eval_eq_sum_range' hdeg, Finset.sum_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, mul_comm]

end GlobalTheory
