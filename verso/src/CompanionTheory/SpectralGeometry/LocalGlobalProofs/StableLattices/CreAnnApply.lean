import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.GopEntries

open CompanionTheory.D.DSIC

variable {n : ℕ} {ε : Fin n → Bool}

def sgR (i : NC ε) (A : Finset (NC ε)) : ℝ := (-1) ^ (A.filter fun j => key j < key i).card

def hh (i j : NC ε) (A B : Finset (NC ε)) : ℝ :=
  if i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j then sgR i (A.erase i) * sgR j (B.erase j) else 0

def coef (c d : Fin n) (i j : NC ε) : ℝ :=
  (if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
    (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0)

def gg (c d : Fin n) (A B : Finset (NC ε)) : ℝ := ∑ i : NC ε, ∑ j : NC ε, coef c d i j * hh i j A B

/- English proof (translation)
Simplify using `[sg, sgR]`.
-/
lemma sg_eq (i : NC ε) (A : Finset (NC ε)) : sg i A = (sgR i A : ℂ) := by
  simp [sg, sgR]

/- English proof (translation)
Unfold `sgR`. Use `congr 2`. Use extensionality with `j`. Simplify using `only [mem_filter, mem_erase]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨_, h⟩, h'⟩`. Conclude with `⟨h, h'⟩`. Introduce and unpack `⟨h, h'⟩`. Use `⟨⟨?_, h⟩, h'⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `lt_irrefl _ h'`.
-/
lemma sgR_erase (i : NC ε) (A : Finset (NC ε)) : sgR i (A.erase i) = sgR i A := by
  unfold sgR
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨?_, h⟩, h'⟩
    rintro rfl
    exact lt_irrefl _ h'

/- English proof (translation)
Unfold `sgR`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.
-/
lemma sgR_mul_self (i : NC ε) (A : Finset (NC ε)) : sgR i A * sgR i A = 1 := by
  unfold sgR
  rw [← mul_pow]; simp

/- English proof (translation)
Unfold `hh`. Distinguish the cases in `h : i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j`. Rewrite using `[if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, mul_comm]`. Rewrite using `[if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩)]`.
-/
lemma hh_symm (i j : NC ε) (A B : Finset (NC ε)) : hh i j A B = hh j i B A := by
  unfold hh
  by_cases h : i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, mul_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩)]

/- English proof (translation)
Unfold `coef`. Use `congr 1`. Conclude with `if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl`. Conclude with `if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl`.
-/
lemma coef_symm (c d : Fin n) (i j : NC ε) : coef c d i j = coef d c j i := by
  unfold coef
  congr 1
  · exact if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl
  · exact if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(if i ∈ A then sg i A • (if j ∈ A.erase i then 0 else sg j (A.erase i) • x (insert j (A.erase i))) else 0) = _`. Distinguish the cases in `hi : i ∈ A`. Rewrite using `[if_pos hi]`. Distinguish the cases in `hj : j ∈ A.erase i`. Rewrite using `[if_pos hj, smul_zero]`.

Use `symm`. Use `Finset.sum_eq_zero fun B _ => ?_` and prove the remaining obligations. Establish `: ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j)`. Introduce and unpack `⟨_, _, h⟩`. Rewrite `hj` using `[h]`.

Conclude with `Finset.notMem_erase _ _ hj`. Simplify using `only [hh, if_neg this, Complex.ofReal_zero, zero_smul]`. Rewrite using `[if_neg hj, Finset.sum_eq_single (insert j (A.erase i))]`. Establish `: i ∈ A ∧ j ∈ insert j (A.erase i) ∧ A.erase i = (insert j (A.erase i)).erase j` using `⟨hi, mem_insert_self _ _, (Finset.erase_insert hj).symm⟩`. Rewrite using `[hh, if_pos this, Finset.erase_insert hj, sgR_erase, smul_smul, sg_eq, sg_eq, Complex.ofReal_mul]`.

Introduce `B _ hB`. Establish `: ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j)`. Introduce and unpack `⟨_, h1, h⟩`. Apply `hB` to reduce the goal to its premises. Rewrite using `[h, Finset.insert_erase h1]`.

Simplify using `only [hh, if_neg this, Complex.ofReal_zero, zero_smul]`. Introduce `h`. Conclude with `absurd (mem_univ _) h`. Rewrite using `[if_neg hi]`. Use `symm`.

Use `Finset.sum_eq_zero fun B _ => ?_` and prove the remaining obligations. Establish `: ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j)` using `fun h => hi h.1`. Simplify using `only [hh, if_neg this, Complex.ofReal_zero, zero_smul]`.
-/
lemma cre_ann_apply {V : Type} [AddCommGroup V] [Module ℂ V] (i j : NC ε) (x : Ch ε V)
    (A : Finset (NC ε)) :
    (cre i * ann j : Module.End ℂ (Ch ε V)) x A = ∑ B, (hh i j A B : ℂ) • x B := by
  change (if i ∈ A then sg i A • (if j ∈ A.erase i then 0 else
    sg j (A.erase i) • x (insert j (A.erase i))) else 0) = _
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    by_cases hj : j ∈ A.erase i
    · rw [if_pos hj, smul_zero]
      symm
      refine Finset.sum_eq_zero fun B _ => ?_
      have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := by
        rintro ⟨_, _, h⟩
        rw [h] at hj
        exact Finset.notMem_erase _ _ hj
      simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
    · rw [if_neg hj, Finset.sum_eq_single (insert j (A.erase i))]
      · have : i ∈ A ∧ j ∈ insert j (A.erase i) ∧ A.erase i = (insert j (A.erase i)).erase j :=
          ⟨hi, mem_insert_self _ _, (Finset.erase_insert hj).symm⟩
        rw [hh, if_pos this, Finset.erase_insert hj, sgR_erase, smul_smul, sg_eq, sg_eq,
          Complex.ofReal_mul]
      · intro B _ hB
        have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := by
          rintro ⟨_, h1, h⟩
          apply hB
          rw [h, Finset.insert_erase h1]
        simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
      · intro h; exact absurd (mem_univ _) h
  · rw [if_neg hi]
    symm
    refine Finset.sum_eq_zero fun B _ => ?_
    have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := fun h => hi h.1
    simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]

/- English proof (translation)
Establish `hc : ∀ i j : NC ε, ((if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) - (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0) : ℂ) = (coef c d i j : ℂ)`. Introduce `i j`. Unfold `coef`. Apply the tactic sequence `split_ifs <;> simp`. Unfold `Gop gg`.

Simplify using `only [hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, cre_ann_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
lemma Gop_apply {V : Type} [AddCommGroup V] [Module ℂ V] (c d : Fin n) (x : Ch ε V)
    (A : Finset (NC ε)) : Gop ε c d x A = ∑ B, (gg c d A B : ℂ) • x B := by
  have hc : ∀ i j : NC ε, ((if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
      (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0) : ℂ) = (coef c d i j : ℂ) := by
    intro i j
    unfold coef
    split_ifs <;> simp
  unfold Gop gg
  simp only [hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    cre_ann_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `key : ∀ (p : NC ε → Prop) [DecidablePred p], ((A.filter p).card : ℝ) = (((A.erase i).filter p).card : ℝ) + if p i then 1 else 0`. Introduce `p _`. Use `conv_lhs => rw [← Finset.insert_erase hi, Finset.filter_insert]`. Use `split_ifs with h`.

Rewrite using `[Finset.card_insert_of_notMem (by simp)]; simp`. Simplify using the standard rewrite rules. Simplify using `only [wtA, Pi.sub_apply, Pi.add_apply, Pi.single_apply]`. Rewrite using `[key (fun i => i.1.1 = c), key (fun i => i.1.2 = c)]`. Simplify using `only [eq_comm (a := c)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma wtA_erase (i : NC ε) (A : Finset (NC ε)) (hi : i ∈ A) :
    wtA A = wtA (A.erase i) + Pi.single i.1.1 1 - Pi.single i.1.2 1 := by
  funext c
  have key : ∀ (p : NC ε → Prop) [DecidablePred p],
      ((A.filter p).card : ℝ) = (((A.erase i).filter p).card : ℝ) + if p i then 1 else 0 := by
    intro p _
    conv_lhs => rw [← Finset.insert_erase hi, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]; simp
    · simp
  simp only [wtA, Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  rw [key (fun i => i.1.1 = c), key (fun i => i.1.2 = c)]
  simp only [eq_comm (a := c)]
  ring

/- English proof (translation)
Take `⟨i, -, h⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Take `⟨j, -, h⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Use `⟨i, j, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h'`. Rewrite `h'` using `[not_or]`.

Conclude with `left_ne_zero_of_mul h (by rw [coef, if_neg h'.1, if_neg h'.2, sub_zero])`. Assume the negation of the conclusion as `h'`. Conclude with `right_ne_zero_of_mul h (by rw [hh, if_neg h'])`.
-/
lemma exists_of_ne {c d : Fin n} {A B : Finset (NC ε)} (h : gg c d A B ≠ 0) :
    ∃ i j : NC ε, ((i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2) ∨ (i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1)) ∧
      i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j := by
  obtain ⟨i, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨j, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨i, j, ?_, ?_⟩
  · by_contra h'
    rw [not_or] at h'
    exact left_ne_zero_of_mul h (by rw [coef, if_neg h'.1, if_neg h'.2, sub_zero])
  · by_contra h'
    exact right_ne_zero_of_mul h (by rw [hh, if_neg h'])

/- English proof (translation)
Establish `h1 : ∀ i : NC ε, ∑ j : NC ε, coef c c i j * hh i j A B = coef c c i i * hh i i A B`. Introduce `i`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (mem_univ _) h)` and prove the remaining obligations. Establish `e1 : ¬ (i.1.1 = c ∧ j.1.1 = c ∧ i.1.2 = j.1.2)`. Introduce and unpack `⟨a, b, e⟩`.

Conclude with `hj (Subtype.ext (Prod.ext (b.trans a.symm) e.symm))`. Establish `e2 : ¬ (i.1.2 = c ∧ j.1.2 = c ∧ i.1.1 = j.1.1)`. Introduce and unpack `⟨a, b, e⟩`. Conclude with `hj (Subtype.ext (Prod.ext e.symm (b.trans a.symm)))`. Rewrite using `[coef, if_neg e1, if_neg e2, sub_zero, zero_mul]`.

Unfold `gg`. Simplify using `only [h1]`. Use `split_ifs with h`. Substitute `h` using the available equality. Establish `h2 : ∀ i : NC ε, hh i i A A = if i ∈ A then 1 else 0`.

Introduce `i`. Unfold `hh`. Distinguish the cases in `hi : i ∈ A`. Simplify using `[hi, sgR_mul_self]`. Simplify using `[hi]`.

Simplify using `only [h2, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_mem, Finset.univ_inter]`. Simplify using `[coef, wtA, Finset.sum_sub_distrib]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `: ¬ (i ∈ A ∧ i ∈ B ∧ A.erase i = B.erase i)`.

Introduce and unpack `⟨a, b, e⟩`. Apply `h` to reduce the goal to its premises. Rewrite using `[← Finset.insert_erase a, e, Finset.insert_erase b]`. Rewrite using `[hh, if_neg this, mul_zero]`.
-/
lemma gg_diag (c : Fin n) (A B : Finset (NC ε)) : gg c c A B = if A = B then wtA A c else 0 := by
  have h1 : ∀ i : NC ε, ∑ j : NC ε, coef c c i j * hh i j A B = coef c c i i * hh i i A B := by
    intro i
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (mem_univ _) h)
    have e1 : ¬ (i.1.1 = c ∧ j.1.1 = c ∧ i.1.2 = j.1.2) := by
      rintro ⟨a, b, e⟩
      exact hj (Subtype.ext (Prod.ext (b.trans a.symm) e.symm))
    have e2 : ¬ (i.1.2 = c ∧ j.1.2 = c ∧ i.1.1 = j.1.1) := by
      rintro ⟨a, b, e⟩
      exact hj (Subtype.ext (Prod.ext e.symm (b.trans a.symm)))
    rw [coef, if_neg e1, if_neg e2, sub_zero, zero_mul]
  unfold gg
  simp only [h1]
  split_ifs with h
  · subst h
    have h2 : ∀ i : NC ε, hh i i A A = if i ∈ A then 1 else 0 := by
      intro i
      unfold hh
      by_cases hi : i ∈ A
      · simp [hi, sgR_mul_self]
      · simp [hi]
    simp only [h2, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp [coef, wtA, Finset.sum_sub_distrib]
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬ (i ∈ A ∧ i ∈ B ∧ A.erase i = B.erase i) := by
      rintro ⟨a, b, e⟩
      apply h
      rw [← Finset.insert_erase a, e, Finset.insert_erase b]
    rw [hh, if_neg this, mul_zero]

/- English proof (translation)
Introduce `n ε`. Use `⟨gg, fun V _ _ c d x A => Gop_apply c d x A, fun c d A B => ?_, fun c d A B h => ?_, gg_diag, fun c d A hdc => ?_⟩` and prove the remaining obligations. Unfold `gg`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[coef_symm, hh_symm]`. Take `⟨i, j, hc, hi, hj, e⟩` from `exists_of_ne h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.card_erase_add_one hi, e, Finset.card_erase_add_one hj]`. Rewrite using `[wtA_erase i A hi, wtA_erase j B hj, e]`.

Break down `hc with ⟨a, b, f⟩ | ⟨a, b, f⟩` into its components or cases. Rewrite using `[a, b, f]`. Normalize the expressions using the abelian group laws. Rewrite using `[a, b, f]`. Normalize the expressions using the abelian group laws.

Assume the negation of the conclusion as `h`. Take `⟨i, j, hc, hi, hj, e⟩` from `exists_of_ne h`. Establish `hn : i ∉ (A1 ε).erase j` using `e ▸ Finset.notMem_erase i A`. Apply `hn` to reduce the goal to its premises. Simplify using `only [A1, mem_filter, mem_univ, true_and, mem_erase] at hj ⊢`.

Break down `hc with ⟨a, b, f⟩ | ⟨a, b, f⟩` into its components or cases. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hdc.ne (b.symm.trans a)`. Rewrite using `[a, f]`.

Rewrite `hj` using `[b]`. Conclude with `hj.trans hdc`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hdc.ne (a.symm.trans b)`.

Rewrite using `[a, f]`. Rewrite `hj` using `[b]`. Conclude with `hdc.trans hj`.
-/
theorem gFacts : GFacts := by
  intro n ε
  refine ⟨gg, fun V _ _ c d x A => Gop_apply c d x A, fun c d A B => ?_, fun c d A B h => ?_,
    gg_diag, fun c d A hdc => ?_⟩
  · unfold gg
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [coef_symm, hh_symm]
  · obtain ⟨i, j, hc, hi, hj, e⟩ := exists_of_ne h
    refine ⟨?_, ?_⟩
    · rw [← Finset.card_erase_add_one hi, e, Finset.card_erase_add_one hj]
    · rw [wtA_erase i A hi, wtA_erase j B hj, e]
      rcases hc with ⟨a, b, f⟩ | ⟨a, b, f⟩
      · rw [a, b, f]; abel
      · rw [a, b, f]; abel
  · by_contra h
    obtain ⟨i, j, hc, hi, hj, e⟩ := exists_of_ne h
    have hn : i ∉ (A1 ε).erase j := e ▸ Finset.notMem_erase i A
    apply hn
    simp only [A1, mem_filter, mem_univ, true_and, mem_erase] at hj ⊢
    rcases hc with ⟨a, b, f⟩ | ⟨a, b, f⟩
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hdc.ne (b.symm.trans a)
      · rw [a, f]; rw [b] at hj; exact hj.trans hdc
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hdc.ne (a.symm.trans b)
      · rw [a, f]; rw [b] at hj; exact hdc.trans hj

end GlobalTheory.CompanionTheory.GopEntries
