import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.BinaryFormCount

open Finset

variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

/- English proof (translation)
Take `⟨u, v, huv⟩` from `UnramifiedHermitian.exists_binary_eq_of_finite hD c`. Use `symm`. Use `Finset.card_nbij' (fun p => (p.1 * u - n * p.2 * v, p.1 * v + p.2 * u + t * p.2 * v)) (fun p => ((p.1 * (u + t * v) + n * p.2 * v) / c, (p.2 * u - p.1 * v) / c)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢`.

Take the linear combination `(u ^ 2 + t * u * v + n * v ^ 2) * hp + huv`. Introduce `p hp`. Simplify using `only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(u ^ 2 + t * u * v + n * v ^ 2) * hp + c * huv`.

Introduce `p _`. Use `ext`. Simplify using `only`. Clear the denominators using the available nonvanishing facts. Take the linear combination `p.1 * huv`.

Simplify using `only`. Clear the denominators using the available nonvanishing facts. Take the linear combination `p.2 * huv`. Introduce `p _`. Use `ext`.

Simplify using `only`. Clear the denominators using the available nonvanishing facts. Take the linear combination `p.1 * huv`. Simplify using `only`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `p.2 * huv`.
-/
theorem card_fibre_eq {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {c : k} (hc : c ≠ 0) :
    #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c}
      = #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 1} := by
  obtain ⟨u, v, huv⟩ := UnramifiedHermitian.exists_binary_eq_of_finite hD c
  symm
  refine Finset.card_nbij' (fun p => (p.1 * u - n * p.2 * v, p.1 * v + p.2 * u + t * p.2 * v))
    (fun p => ((p.1 * (u + t * v) + n * p.2 * v) / c, (p.2 * u - p.1 * v) / c)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    linear_combination (u ^ 2 + t * u * v + n * v ^ 2) * hp + huv
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    field_simp
    linear_combination (u ^ 2 + t * u * v + n * v ^ 2) * hp + c * huv
  · intro p _
    ext
    · simp only; field_simp; linear_combination p.1 * huv
    · simp only; field_simp; linear_combination p.2 * huv
  · intro p _
    ext
    · simp only; field_simp; linear_combination p.1 * huv
    · simp only; field_simp; linear_combination p.2 * huv

/- English proof (translation)
Distinguish the cases in `h : ∃ r : k, r ^ 2 - t * r + n = 0`. Rewrite using `[h1 h]`. Take `⟨r, hr⟩` from `h`. Establish `hne : t - 2 * r ≠ 0`. Introduce `h0`.

Apply `hD` to reduce the goal to its premises. Take the linear combination `(t - 2 * r) * h0 - 4 * hr`. Establish `e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k)) = (univ.image fun b : k => (-r * b, b)) ∪ (univ.image fun b : k => (-(t - r) * b, b))`. Use extensionality with `⟨a, b⟩`. Simplify using `only [mem_filter, mem_univ, true_and, mem_union, mem_image, Prod.mk.injEq, exists_eq_right]`.

Prove the components needed by the constructor for the conclusion. Introduce `hab`. Establish `: (-r * b - a) * (-(t - r) * b - a) = 0` using `by linear_combination hab - b ^ 2 * hr`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.1 h)`.

Conclude with `Or.inr (sub_eq_zero.1 h)`. Apply the tactic sequence `rintro (rfl | rfl) <;> linear_combination b ^ 2 * hr`. Establish `i : (univ.image fun b : k => (-r * b, b)) ∩ (univ.image fun b : k => (-(t - r) * b, b)) = {((0 : k), (0 : k))}`. Use extensionality with `⟨a, b⟩`. Simplify using `only [mem_univ, true_and, mem_inter, mem_image, Prod.mk.injEq, exists_eq_right, mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl, h⟩`. Establish `: (t - 2 * r) * b = 0` using `by linear_combination -h`. Establish `hb` using `(mul_eq_zero.1 this).resolve_left hne`. Simplify using `[hb]`.

Introduce and unpack `⟨rfl, rfl⟩`. Simplify using the standard rewrite rules. Use `Finset.card_union_add_card_inter (univ.image fun b : k => (-r * b, b)) (univ.image fun b : k => (-(t - r) * b, b))` as an intermediate fact. Rewrite `this` using `[i, ← e, card_image_of_injective _ (fun a b h => congrArg Prod.snd h), card_image_of_injective _ (fun a b h => congrArg Prod.snd h), card_singleton, card_univ]`. Establish `h3` using `congrArg (Nat.cast : ℕ → ℝ) this`.

Move the coercions through the operations in `at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h2 h]`. Establish `e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k)) = {((0 : k), (0 : k))}`. Use extensionality with `⟨a, b⟩`.

Simplify using `only [mem_filter, mem_univ, true_and, Prod.mk.injEq, mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `hab`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality.

Simplify using `using hab`. Use `(h ⟨-a / b, ?_⟩).elim` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `hab`. Introduce and unpack `⟨rfl, rfl⟩`.

Simplify using the standard rewrite rules. Rewrite using `[e, card_singleton]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_zero {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : ℝ)
      = Fintype.card k - η + η * Fintype.card k := by
  by_cases h : ∃ r : k, r ^ 2 - t * r + n = 0
  · rw [h1 h]
    obtain ⟨r, hr⟩ := h
    have hne : t - 2 * r ≠ 0 := by
      intro h0
      apply hD
      linear_combination (t - 2 * r) * h0 - 4 * hr
    have e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k))
        = (univ.image fun b : k => (-r * b, b)) ∪ (univ.image fun b : k => (-(t - r) * b, b)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, Prod.mk.injEq,
        exists_eq_right]
      constructor
      · intro hab
        have : (-r * b - a) * (-(t - r) * b - a) = 0 := by linear_combination hab - b ^ 2 * hr
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (sub_eq_zero.1 h)
      · rintro (rfl | rfl) <;> linear_combination b ^ 2 * hr
    have i : (univ.image fun b : k => (-r * b, b)) ∩ (univ.image fun b : k => (-(t - r) * b, b))
        = {((0 : k), (0 : k))} := by
      ext ⟨a, b⟩
      simp only [mem_univ, true_and, mem_inter, mem_image, Prod.mk.injEq,
        exists_eq_right, mem_singleton]
      constructor
      · rintro ⟨rfl, h⟩
        have : (t - 2 * r) * b = 0 := by linear_combination -h
        have hb := (mul_eq_zero.1 this).resolve_left hne
        simp [hb]
      · rintro ⟨rfl, rfl⟩; simp
    have := Finset.card_union_add_card_inter (univ.image fun b : k => (-r * b, b))
      (univ.image fun b : k => (-(t - r) * b, b))
    rw [i, ← e, card_image_of_injective _ (fun a b h => congrArg Prod.snd h),
      card_image_of_injective _ (fun a b h => congrArg Prod.snd h), card_singleton,
      card_univ] at this
    have h3 := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at h3
    linarith
  · rw [h2 h]
    have e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k))
        = {((0 : k), (0 : k))} := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq, mem_singleton]
      constructor
      · intro hab
        by_cases hb : b = 0
        · subst hb
          simpa using hab
        · refine (h ⟨-a / b, ?_⟩).elim
          field_simp
          linear_combination hab
      · rintro ⟨rfl, rfl⟩; simp
    rw [e, card_singleton]
    push_cast
    ring

/- English proof (translation)
Establish `hz` using `card_zero hD h1 h2`. Distinguish the cases in `hc : c = 0`. Rewrite using `[if_pos hc, hc, hz]`. Rewrite using `[if_neg hc, card_fibre_eq hD hc, add_zero]`. Establish `tot` using `Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (k × k))) (t := univ) (f := fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (fun _ _ => mem_univ _)`.

Rewrite `tot` using `[← Finset.add_sum_erase _ _ (mem_univ (0 : k)), Finset.sum_congr rfl (fun d hd => card_fibre_eq hD (Finset.ne_of_mem_erase hd)), sum_const, card_erase_of_mem (mem_univ _), card_univ, card_univ, Fintype.card_prod, smul_eq_mul]`. Establish `hq : 1 < Fintype.card k` using `Fintype.one_lt_card`. Establish `h3` using `congrArg (Nat.cast : ℕ → ℝ) tot`. Move the coercions through the operations in `[Nat.cast_sub hq.le] at h3`. Rewrite `h3` using `[hz]`.

Establish `hq' : (Fintype.card k : ℝ) - 1 ≠ 0`. Establish `: (1 : ℝ) < Fintype.card k` using `by exact_mod_cast hq`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `mul_left_cancel₀ hq'` to reduce the goal to its premises. Take the linear combination `-h3`.
-/
theorem card_fibre {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (c : k) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c} : ℝ)
      = Fintype.card k - η + if c = 0 then η * Fintype.card k else 0 := by
  have hz := card_zero hD h1 h2
  by_cases hc : c = 0
  · rw [if_pos hc, hc, hz]
  rw [if_neg hc, card_fibre_eq hD hc, add_zero]
  have tot := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (k × k))) (t := univ)
    (f := fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (fun _ _ => mem_univ _)
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : k)),
    Finset.sum_congr rfl (fun d hd => card_fibre_eq hD (Finset.ne_of_mem_erase hd)),
    sum_const, card_erase_of_mem (mem_univ _), card_univ, card_univ, Fintype.card_prod,
    smul_eq_mul] at tot
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have h3 := congrArg (Nat.cast : ℕ → ℝ) tot
  push_cast [Nat.cast_sub hq.le] at h3
  rw [hz] at h3
  have hq' : (Fintype.card k : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card k := by exact_mod_cast hq
    linarith
  apply mul_left_cancel₀ hq'
  linear_combination -h3

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => simp`. Consider the case `succ M ih`. Establish `key : (#{x : Fin (M + 1) → α | ∑ i, Q (x i) = 0} : ℝ) = q ^ (2 * M) * (q - η) + η * q * #{x : Fin M → α | ∑ i, Q (x i) = 0}`. Rewrite using `[Finset.card_filter, Finset.card_filter]`.

Use `push_cast`. Rewrite using `[← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type_right]`. Establish `: ∀ y : Fin M → α, (∑ a : α, if ∑ i, Q ((Fin.consEquiv fun _ => α) (a, y) i) = 0 then (1 : ℝ) else 0) = q - η + η * q * if ∑ i, Q (y i) = 0 then 1 else 0`. Introduce `y`. Use `hQ (-∑ i, Q (y i))` as an intermediate fact.

Rewrite `this` using `[Finset.card_filter]`. Move the coercions through the operations in `at this`. Simplify using `only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← eq_neg_iff_add_eq_zero, this, neg_eq_zero, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_congr rfl fun y _ => this y, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`.

Rewrite using `[hα, ← pow_mul]`. Rewrite using `[key, show 2 * (M + 1) = 2 * M + 2 by ring]`. Take the linear combination `(η * q) * ih`.
-/
theorem card_sum_zero {α : Type} [Fintype α] [DecidableEq α] (Q : α → k) (q η : ℝ)
    (hα : (Fintype.card α : ℝ) = q ^ 2)
    (hQ : ∀ c, (#{p : α | Q p = c} : ℝ) = q - η + if c = 0 then η * q else 0) (M : ℕ) :
    (#{x : Fin M → α | ∑ i, Q (x i) = 0} : ℝ) * q = q ^ (2 * M) + (q - 1) * (η * q) ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have key : (#{x : Fin (M + 1) → α | ∑ i, Q (x i) = 0} : ℝ)
        = q ^ (2 * M) * (q - η) + η * q * #{x : Fin M → α | ∑ i, Q (x i) = 0} := by
      rw [Finset.card_filter, Finset.card_filter]
      push_cast
      rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type_right]
      have : ∀ y : Fin M → α, (∑ a : α, if ∑ i, Q ((Fin.consEquiv fun _ => α) (a, y) i) = 0
          then (1 : ℝ) else 0) = q - η + η * q * if ∑ i, Q (y i) = 0 then 1 else 0 := by
        intro y
        have := hQ (-∑ i, Q (y i))
        rw [Finset.card_filter] at this
        push_cast at this
        simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          ← eq_neg_iff_add_eq_zero, this, neg_eq_zero, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_congr rfl fun y _ => this y, sum_add_distrib, ← mul_sum, sum_const,
        card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [hα, ← pow_mul]
    rw [key, show 2 * (M + 1) = 2 * M + 2 by ring]
    linear_combination (η * q) * ih

end GlobalTheory.BinaryFormCount

namespace GlobalTheory

open Finset in

/- English proof (translation)
Use `haveI := Fintype.ofFinite k`. Establish `hz` using `BinaryFormCount.card_sum_zero (fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (Fintype.card k) η (by rw [Fintype.card_prod]; push_cast; ring) (BinaryFormCount.card_fibre hD h1 h2) M`. Establish `hs` using `Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M → k × k))) (fun x => ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0)`. Establish `hb : {x : Fin M × Fin 2 → k | ∑ i : Fin M, (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard = #{x : Fin M → k × k | ¬ ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0}`. Rewrite using `[Set.ncard_eq_toFinset_card', Set.toFinset_setOf]`.

Use `Finset.card_nbij' (fun x i => (x (i, 0), x (i, 1))) (fun x p => ![(x p.1).1, (x p.1).2] p.2) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `using hx`. Introduce `x hx`. Simplify using `using hx`.

Introduce `x _`. Use extensionality with `⟨i, j⟩`. Apply the tactic sequence `fin_cases j <;> simp`. Introduce `x _`. Apply the tactic sequence `ext i <;> simp`.

Rewrite `hs` using `[card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]`. Establish `h3` using `congrArg (Nat.cast : ℕ → ℝ) hs`. Move the coercions through the operations in `at h3`. Rewrite using `[hb, Nat.card_eq_fintype_card, pow_mul, pow_two]`. Rewrite `hz` using `[pow_mul, pow_two]`.

Take the linear combination `(Fintype.card k : ℝ) * h3 - hz`.
-/
theorem ncard_sum_binary_form_ne_zero (k : Type) [Field k] [Finite k] (t n : k)
    (hD : t ^ 2 - 4 * n ≠ 0) (η : ℝ) (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (M : ℕ) :
    ({x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard : ℝ)
      * (Nat.card k : ℝ)
      = ((Nat.card k : ℝ) - 1) * ((Nat.card k : ℝ) ^ (2 * M) - (η * (Nat.card k : ℝ)) ^ M) := by
  classical
  haveI := Fintype.ofFinite k
  have hz := BinaryFormCount.card_sum_zero
    (fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (Fintype.card k) η
    (by rw [Fintype.card_prod]; push_cast; ring) (BinaryFormCount.card_fibre hD h1 h2) M
  have hs := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M → k × k)))
    (fun x => ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0)
  have hb : {x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard
      = #{x : Fin M → k × k |
        ¬ ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0} := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    refine Finset.card_nbij' (fun x i => (x (i, 0), x (i, 1)))
      (fun x p => ![(x p.1).1, (x p.1).2] p.2) ?_ ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro x hx
      simpa using hx
    · intro x _
      ext ⟨i, j⟩
      fin_cases j <;> simp
    · intro x _
      ext i <;> simp
  rw [card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin] at hs
  have h3 := congrArg (Nat.cast : ℕ → ℝ) hs
  push_cast at h3
  rw [hb, Nat.card_eq_fintype_card, pow_mul, pow_two]
  rw [pow_mul, pow_two] at hz
  linear_combination (Fintype.card k : ℝ) * h3 - hz

end GlobalTheory
