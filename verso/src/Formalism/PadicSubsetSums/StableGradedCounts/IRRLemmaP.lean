import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih => match n, hn with`. Consider the case `1, _ => simp [numDerangements_one]`. Consider the case `2, _ => simp [numDerangements_add_two, numDerangements_zero, numDerangements_one, Nat.factorial]`. Consider the case `k + 3, _`.

Establish `h1` using `ih (k + 1) (by omega) (by omega)`. Establish `h2` using `ih (k + 2) (by omega) (by omega)`. Use `show 2 * numDerangements (k + 1 + 2) ≤ (k + 1 + 2).factorial`. Rewrite using `[numDerangements_add_two, Nat.factorial_succ (k + 1 + 1)]`. Rewrite `*` using `[show k + 1 + 1 = k + 2 from rfl, Nat.factorial_succ (k + 1)]`.

Use polynomial arithmetic with `[h1, h2]`.
-/
theorem two_numDerangements_le (n : ℕ) (hn : 1 ≤ n) : 2 * numDerangements n ≤ n.factorial := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [numDerangements_one]
    | 2, _ => simp [numDerangements_add_two, numDerangements_zero, numDerangements_one, Nat.factorial]
    | k + 3, _ =>
      have h1 := ih (k + 1) (by omega) (by omega)
      have h2 := ih (k + 2) (by omega) (by omega)
      show 2 * numDerangements (k + 1 + 2) ≤ (k + 1 + 2).factorial
      rw [numDerangements_add_two, Nat.factorial_succ (k + 1 + 1)]
      rw [show k + 1 + 1 = k + 2 from rfl, Nat.factorial_succ (k + 1)] at *
      nlinarith [h1, h2]

/- English proof (translation)
Establish `hd` using `card_derangements_eq_numDerangements β`. Establish `h2` using `two_numDerangements_le _ hβ`. Establish `hsplit : ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card + ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card = (Fintype.card β).factorial`. Rewrite using `[← Fintype.card_perm, ← Finset.card_univ]`. Use `first`.

Consider the case `exact Finset.card_filter_add_card_filter_not _`. Consider the case `exact Finset.filter_card_add_filter_neg_card_eq_card _`. Consider the case `exact Finset.card_filter_add_card_filter_neg _`. Establish `hneg : ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card = Fintype.card (derangements β)`. Rewrite using `[Fintype.card_subtype]`.

Use `congr 1`. Use extensionality with `s`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]`. Conclude with `Iff.rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_fixed_ge (β : Type) [Fintype β] [DecidableEq β] (hβ : 1 ≤ Fintype.card β) :
    (Fintype.card β).factorial ≤
      2 * ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card := by
  have hd := card_derangements_eq_numDerangements β
  have h2 := two_numDerangements_le _ hβ
  have hsplit : ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card +
      ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card =
      (Fintype.card β).factorial := by
    rw [← Fintype.card_perm, ← Finset.card_univ]
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | exact Finset.card_filter_add_card_filter_neg _
  have hneg : ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card =
      Fintype.card (derangements β) := by
    rw [Fintype.card_subtype]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    exact Iff.rfl
  omega

section

variable {N : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Assume the negation of the conclusion as `hxA`. Establish `hsub : A.image σ ⊆ A` using `fun y hy => by`. Take `⟨z, hz, rfl⟩` from `Finset.mem_image.mp hy`.

Conclude with `h z hz`. Establish `hcard : (A.image σ).card = A.card` using `Finset.card_image_of_injective A σ.injective`. Establish `heq` using `Finset.eq_of_subset_of_card_le hsub hcard.ge`. Rewrite `hx` using `[← heq]`. Take `⟨z, hz, hzx⟩` from `Finset.mem_image.mp hx`.

Conclude with `hxA (σ.injective hzx ▸ hz)`. Conclude with `h x`.
-/
theorem stab_iff (A : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) (h : ∀ x ∈ A, σ x ∈ A) (x : Fin N) :
    σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    by_contra hxA
    have hsub : A.image σ ⊆ A := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact h z hz
    have hcard : (A.image σ).card = A.card := Finset.card_image_of_injective A σ.injective
    have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
    rw [← heq] at hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    exact hxA (σ.injective hzx ▸ hz)
  · exact h x

/- English proof (translation)
Establish `key : Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} ≤ Fintype.card (Equiv.Perm {x // x ∈ A} × Equiv.Perm {x // x ∉ A})`. Use `Fintype.card_le_of_injective (fun σ => (σ.1.subtypePerm (fun x => stab_iff A σ.1 σ.2 x), σ.1.subtypePerm (fun x => not_congr (stab_iff A σ.1 σ.2 x)))) ?_` and prove the remaining obligations. Introduce and unpack `⟨σ, hσ⟩ ⟨τ, hτ⟩ he`. Simplify using `only [Prod.mk.injEq] at he`. Apply `Subtype.ext` to reduce the goal to its premises.

Use extensionality with `x`. Distinguish the cases in `hx : x ∈ A`. Use `congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.1` as an intermediate fact. Conclude with `congrArg Fin.val (by simpa using this)`. Use `congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.2` as an intermediate fact.

Conclude with `congrArg Fin.val (by simpa using this)`. Rewrite `key` using `[Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_coe, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_stab_le (A : Finset (Fin N)) :
    ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have key : Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} ≤
      Fintype.card (Equiv.Perm {x // x ∈ A} × Equiv.Perm {x // x ∉ A}) := by
    refine Fintype.card_le_of_injective
      (fun σ => (σ.1.subtypePerm (fun x => stab_iff A σ.1 σ.2 x),
        σ.1.subtypePerm (fun x => not_congr (stab_iff A σ.1 σ.2 x)))) ?_
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ he
    simp only [Prod.mk.injEq] at he
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ A
    · have := congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.1
      exact congrArg Fin.val (by simpa using this)
    · have := congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.2
      exact congrArg Fin.val (by simpa using this)
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_coe,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at key
  calc _ = Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} := (Fintype.card_subtype _).symm
    _ ≤ _ := key

/- English proof (translation)
Use `set P : Finset (Equiv.Perm {x // x ∈ A}) := univ.filter (fun s => ∃ x, s x = x) with hP`. Use `set Q : Finset (Equiv.Perm {x // x ∉ A}) := univ.filter (fun s => ∃ x, s x = x) with hQ`. Establish `hP1 : A.card.factorial ≤ 2 * P.card`. Use `card_fixed_ge {x // x ∈ A} (by rw [Fintype.card_coe]; exact h1)` as an intermediate fact. Rewrite `this` using `[Fintype.card_coe]`. Then use the resulting hypothesis.

Establish `hc : Fintype.card {x // x ∉ A} = N - A.card`. Rewrite using `[Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]`. Establish `hQ1 : (N - A.card).factorial ≤ 2 * Q.card`. Use `card_fixed_ge {x // x ∉ A} (by rw [hc]; exact h2)` as an intermediate fact. Rewrite `this` using `[hc]`. Then use the resulting hypothesis.

Establish `hinj : (P ×ˢ Q).card ≤ ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card`. Use `Finset.card_le_card_of_injOn (fun q => Equiv.Perm.subtypeCongr q.1 q.2) ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨α, β⟩ hq`. Simplify using `only [Finset.mem_coe, Finset.mem_product, hP, hQ, Finset.mem_filter, Finset.mem_univ, true_and] at hq`. Take `⟨⟨x, hx⟩, ⟨y, hy⟩⟩` from `hq`.

Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]`. Use `⟨fun z hz => ?_, ⟨x.1, x.2, ?_⟩, ⟨y.1, y.2, ?_⟩⟩` and prove the remaining obligations. Simplify using `[Equiv.Perm.subtypeCongr.left_apply, hz]`. Simplify using `[Equiv.Perm.subtypeCongr.left_apply, x.2, hx]`. Simplify using `[Equiv.Perm.subtypeCongr.right_apply, y.2, hy]`.

Introduce and unpack `⟨α, β⟩ _ ⟨α', β'⟩ _ he`. Simplify using `only at he`. Establish `hA : α = α'`. Use extensionality with `⟨z, hz⟩`. Use `congrArg (fun e : Equiv.Perm (Fin N) => e z) he` as an intermediate fact.

Establish `h' : α ⟨z, hz⟩ = α' ⟨z, hz⟩`. Simplify `this` using `[Equiv.Perm.subtypeCongr.left_apply, hz]`. Rewrite using `[h']`. Establish `hB : β = β'`. Use extensionality with `⟨z, hz⟩`.

Use `congrArg (fun e : Equiv.Perm (Fin N) => e z) he` as an intermediate fact. Establish `h' : (β ⟨z, hz⟩ : Fin N) = β' ⟨z, hz⟩`. Simplify `this` using `[Equiv.Perm.subtypeCongr.right_apply, hz]`. Rewrite using `[h']`. Rewrite using `[hA, hB]`.

Rewrite `hinj` using `[Finset.card_product]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_good_ge (A : Finset (Fin N)) (h1 : 1 ≤ A.card) (h2 : 1 ≤ N - A.card) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
        (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
  set P : Finset (Equiv.Perm {x // x ∈ A}) := univ.filter (fun s => ∃ x, s x = x) with hP
  set Q : Finset (Equiv.Perm {x // x ∉ A}) := univ.filter (fun s => ∃ x, s x = x) with hQ
  have hP1 : A.card.factorial ≤ 2 * P.card := by
    have := card_fixed_ge {x // x ∈ A} (by rw [Fintype.card_coe]; exact h1)
    rwa [Fintype.card_coe] at this
  have hc : Fintype.card {x // x ∉ A} = N - A.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have hQ1 : (N - A.card).factorial ≤ 2 * Q.card := by
    have := card_fixed_ge {x // x ∉ A} (by rw [hc]; exact h2)
    rwa [hc] at this
  have hinj : (P ×ˢ Q).card ≤ ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
      (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    refine Finset.card_le_card_of_injOn (fun q => Equiv.Perm.subtypeCongr q.1 q.2) ?_ ?_
    · rintro ⟨α, β⟩ hq
      simp only [Finset.mem_coe, Finset.mem_product, hP, hQ, Finset.mem_filter, Finset.mem_univ,
        true_and] at hq
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun z hz => ?_, ⟨x.1, x.2, ?_⟩, ⟨y.1, y.2, ?_⟩⟩
      · simp [Equiv.Perm.subtypeCongr.left_apply, hz]
      · simp [Equiv.Perm.subtypeCongr.left_apply, x.2, hx]
      · simp [Equiv.Perm.subtypeCongr.right_apply, y.2, hy]
    · rintro ⟨α, β⟩ _ ⟨α', β'⟩ _ he
      simp only at he
      have hA : α = α' := by
        ext ⟨z, hz⟩
        have := congrArg (fun e : Equiv.Perm (Fin N) => e z) he
        have h' : α ⟨z, hz⟩ = α' ⟨z, hz⟩ := by
          simpa [Equiv.Perm.subtypeCongr.left_apply, hz] using this
        rw [h']
      have hB : β = β' := by
        ext ⟨z, hz⟩
        have := congrArg (fun e : Equiv.Perm (Fin N) => e z) he
        have h' : (β ⟨z, hz⟩ : Fin N) = β' ⟨z, hz⟩ := by
          simpa [Equiv.Perm.subtypeCongr.right_apply, hz] using this
        rw [h']
      rw [hA, hB]
  rw [Finset.card_product] at hinj
  calc A.card.factorial * (N - A.card).factorial ≤ (2 * P.card) * (2 * Q.card) :=
        Nat.mul_le_mul hP1 hQ1
    _ = 4 * (P.card * Q.card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hinj

end

/- English proof (translation)
Introduce `N a ha haN`. Establish `key : ∀ σ : Equiv.Perm (Fin N), 2 * (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) + (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card ≤ 2 * (((univ : Finset (Fin N)).powerset …`. Introduce `σ`. Establish `hsub : ((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y) ⊆ ((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)`. Introduce `A hA`.

Simplify using `only [Finset.mem_filter] at hA ⊢`. Conclude with `⟨hA.1, hA.2.1⟩`. Establish `hle` using `Finset.card_le_card hsub`. Use `split_ifs with hX`. Take `⟨A0, hA0c, hA0⟩` from `hX`.

Establish `h1 : 1 ≤ (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card`. Apply `Finset.card_pos.mpr` to reduce the goal to its premises. Conclude with `⟨A0, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA0c⟩, hA0⟩⟩`. Distinguish the cases in `hg : (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card = 0`. Use linear arithmetic over natural numbers and integers.

Take `⟨A, hA⟩` from `Finset.card_pos.mp (Nat.pos_of_ne_zero hg)`. Simplify using `only [Finset.mem_filter, Finset.mem_powersetCard] at hA`. Take `⟨⟨-, hAc⟩, hinv, ⟨x, hxA, hx⟩, ⟨y, hyA, hy⟩⟩` from `hA`. Establish `hyE : y ∉ A.erase x` using `fun h => hyA (Finset.mem_of_mem_erase h)`. Establish `h2 : 1 < (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card`.

Rewrite using `[Finset.one_lt_card]`. Use `⟨A, ?_, insert y (A.erase x), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩, hinv⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.card_insert_of_notMem hyE, Finset.card_erase_of_mem hxA]`. Establish `: 1 ≤ A.card` using `Finset.card_pos.mpr ⟨x, hxA⟩`. Use linear arithmetic over natural numbers and integers. Introduce `z hz`. Break down `Finset.mem_insert.mp hz with rfl | hz` into its components or cases.

Rewrite using `[hy]`. Conclude with `Finset.mem_insert_self _ _`. Establish `hzA` using `Finset.mem_of_mem_erase hz`. Establish `hzx` using `Finset.ne_of_mem_erase hz`. Apply `Finset.mem_insert_of_mem` to reduce the goal to its premises.

Use `Finset.mem_erase.mpr ⟨?_, hinv z hzA⟩` and prove the remaining obligations. Introduce `h`. Apply `hzx` to reduce the goal to its premises. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[h, hx]`.

Introduce `h`. Apply `hyA` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `Finset.mem_insert_self _ _`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hsum` using `Finset.sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm (Fin N)))) => key σ)`. Rewrite `hsum` using `[Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]`. Establish `hX : ∑ σ : Equiv.Perm (Fin N), (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) = ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A))).card` using `(Finset.card_filter _ _).symm`. Establish `hs1 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card = ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card`.

Simplify using `only [Finset.card_filter]`. Conclude with `Finset.sum_comm`. Establish `hs2 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card = ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x …`. Simplify using `only [Finset.card_filter]`. Conclude with `Finset.sum_comm`.

Establish `hfac : ∑ _A ∈ ((univ : Finset (Fin N)).powersetCard a), a.factorial * (N - a).factorial = N.factorial`. Rewrite using `[Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← mul_assoc]`. Conclude with `Nat.choose_mul_factorial_mul_factorial haN.le`. Establish `hinv : ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤ N.factorial`. Rewrite using `[← hfac]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `A hA`. Rewrite `hA` using `[Finset.mem_powersetCard]`. Use `card_stab_le A` as an intermediate fact. Rewrite `this` using `[hA.2]`. Then use the resulting hypothesis.

Establish `hgood : N.factorial ≤ 4 * ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card`. Rewrite using `[← hfac, Finset.mul_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `A hA`. Rewrite `hA` using `[Finset.mem_powersetCard]`.

Use `card_good_ge A (by omega) (by omega)` as an intermediate fact. Rewrite `this` using `[hA.2]`. Then use the resulting hypothesis. Rewrite `hsum` using `[hX, hs1, hs2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem prodMaxInvLeSq : LemmaP := by
  intro N a ha haN
  have key : ∀ σ : Equiv.Perm (Fin N),
      2 * (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) + (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card ≤ 2 * (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
    intro σ
    have hsub : ((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y) ⊆ ((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A) := by
      intro A hA
      simp only [Finset.mem_filter] at hA ⊢
      exact ⟨hA.1, hA.2.1⟩
    have hle := Finset.card_le_card hsub
    split_ifs with hX
    · obtain ⟨A0, hA0c, hA0⟩ := hX
      have h1 : 1 ≤ (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
        apply Finset.card_pos.mpr
        exact ⟨A0, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA0c⟩, hA0⟩⟩
      by_cases hg : (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card = 0
      · omega
      · obtain ⟨A, hA⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hg)
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hA
        obtain ⟨⟨-, hAc⟩, hinv, ⟨x, hxA, hx⟩, ⟨y, hyA, hy⟩⟩ := hA
        have hyE : y ∉ A.erase x := fun h => hyA (Finset.mem_of_mem_erase h)
        have h2 : 1 < (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
          rw [Finset.one_lt_card]
          refine ⟨A, ?_, insert y (A.erase x), ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩, hinv⟩
          · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
            refine ⟨?_, ?_⟩
            · rw [Finset.card_insert_of_notMem hyE, Finset.card_erase_of_mem hxA]
              have : 1 ≤ A.card := Finset.card_pos.mpr ⟨x, hxA⟩
              omega
            · intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · rw [hy]
                exact Finset.mem_insert_self _ _
              · have hzA := Finset.mem_of_mem_erase hz
                have hzx := Finset.ne_of_mem_erase hz
                apply Finset.mem_insert_of_mem
                refine Finset.mem_erase.mpr ⟨?_, hinv z hzA⟩
                intro h
                apply hzx
                apply σ.injective
                rw [h, hx]
          · intro h
            apply hyA
            rw [h]
            exact Finset.mem_insert_self _ _
        omega
    · omega
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm (Fin N)))) => key σ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hX : ∑ σ : Equiv.Perm (Fin N), (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) =
      ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A))).card :=
    (Finset.card_filter _ _).symm
  have hs1 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card =
      ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hs2 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card =
      ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hfac : ∑ _A ∈ ((univ : Finset (Fin N)).powersetCard a), a.factorial * (N - a).factorial = N.factorial := by
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial haN.le
  have hinv : ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤ N.factorial := by
    rw [← hfac]
    apply Finset.sum_le_sum
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have := card_stab_le A
    rwa [hA.2] at this
  have hgood : N.factorial ≤ 4 * ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    rw [← hfac, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have := card_good_ge A (by omega) (by omega)
    rwa [hA.2] at this
  rw [hX, hs1, hs2] at hsum
  omega

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
