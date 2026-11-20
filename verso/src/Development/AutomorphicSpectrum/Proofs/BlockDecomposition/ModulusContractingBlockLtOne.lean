import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCModulus

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hx, ih]`.
-/
theorem prod_zpow_eq {ι : Type*} {x : ℝ} (hx : x ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ a ∈ s, x ^ f a = x ^ ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hx, ih]

/- English proof (translation)
Use `set f : Fin h → Fin h → ℤ := fun a b => (d a : ℤ) * ((d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0))) with hf`. Establish `hm : ∀ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = ∑ b, f a b`. Introduce `a`. Rewrite using `[← Finset.mul_sum]`. Use `congr 1`.

Simplify using `[modExp, Finset.sum_filter, mul_sub, Finset.sum_sub_distrib]`. Establish `hanti : ∀ a b, f b a = - f a b`. Introduce `a b`. Simplify using `only [hf]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcancel : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = 0`. Establish `h1 : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = ∑ a with a ≤ j, ∑ b with b ≤ j, f b a` using `Finset.sum_comm`. Establish `h2 : ∑ a with a ≤ j, ∑ b with b ≤ j, f b a = - ∑ a with a ≤ j, ∑ b with b ≤ j, f a b`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun b _ => hanti a b`. Use linear arithmetic over natural numbers and integers. Establish `hcross : ∑ a with a ≤ j, ∑ b with j < b, f a b = (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ)`. Rewrite using `[Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hab : a < b` using `lt_of_le_of_lt (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2`. Simplify using `[hf, hab, hab.not_gt]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_filter]`.

Conclude with `Finset.sum_congr rfl fun a _ => by rw [hm]`. Use `_ = ∑ a with a ≤ j, ((∑ b with b ≤ j, f a b) + ∑ b with j < b, f a b) := by`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ j)]`. Simplify using `only [not_le]`.

Use `_ = _ := by rw [Finset.sum_add_distrib, hcancel, zero_add, hcross]`.
-/
theorem exponent_eq {h : ℕ} (d : Fin h → ℕ) (j : Fin h) :
    ∑ a, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) =
      (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
  set f : Fin h → Fin h → ℤ := fun a b =>
    (d a : ℤ) * ((d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0))) with hf
  have hm : ∀ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = ∑ b, f a b := by
    intro a
    rw [← Finset.mul_sum]
    congr 1
    simp [modExp, Finset.sum_filter, mul_sub, Finset.sum_sub_distrib]
  have hanti : ∀ a b, f b a = - f a b := by
    intro a b
    simp only [hf]
    ring
  have hcancel : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = 0 := by
    have h1 : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = ∑ a with a ≤ j, ∑ b with b ≤ j, f b a :=
      Finset.sum_comm
    have h2 : ∑ a with a ≤ j, ∑ b with b ≤ j, f b a = - ∑ a with a ≤ j, ∑ b with b ≤ j, f a b := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => hanti a b
    omega
  have hcross : ∑ a with a ≤ j, ∑ b with j < b, f a b =
      (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have hab : a < b := lt_of_le_of_lt (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
    simp [hf, hab, hab.not_gt]
  calc ∑ a, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0)
      = ∑ a with a ≤ j, ∑ b, f a b := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun a _ => by rw [hm]
    _ = ∑ a with a ≤ j, ((∑ b with b ≤ j, f a b) + ∑ b with j < b, f a b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ j)]
        simp only [not_le]
    _ = _ := by rw [Finset.sum_add_distrib, hcancel, zero_add, hcross]

/- English proof (translation)
Take `⟨-, -, hle, hone, -⟩` from `nabs_properties k`. Establish `h1 : nabs k (1 : kˣ) = 1` using `(hone 1).2 (by simp)`. Use `lt_of_le_of_ne ?_ fun h => ht.ne ((hone t).1 h)` and prove the remaining obligations. Rewrite using `[← h1]`. Conclude with `(hle t 1).2 (by simpa using ht.le)`.
-/
theorem nabs_lt_one_of_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ) (ht : ValuativeRel.valuation k (t : k) < 1) :
    nabs k t < 1 := by
  obtain ⟨-, -, hle, hone, -⟩ := nabs_properties k
  have h1 : nabs k (1 : kˣ) = 1 := (hone 1).2 (by simp)
  refine lt_of_le_of_ne ?_ fun h => ht.ne ((hone t).1 h)
  rw [← h1]
  exact (hle t 1).2 (by simpa using ht.le)

/- English proof (translation)
Introduce `k _ _ _ _ h N d _ hpos t ht j hj`. Establish `hx1` using `nabs_lt_one_of_valuation_lt_one k t ht`. Take `⟨hmul, hx0', -, hone, -⟩` from `nabs_properties k`. Establish `hx0` using `hx0' t`. Establish `hdet : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) = if a ≤ j then nabs k t ^ d a else 1`.

Introduce `a`. Establish `hpow : ∀ n : ℕ, nabs k (t ^ n) = nabs k t ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using (hone 1).2 (by simp)`.

Consider the case `succ n ih => rw [pow_succ, hmul, ih, pow_succ]`. Distinguish the cases in `ha : a ≤ j`. Establish `h1 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = t ^ d a`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.det_diagonal]`.

Rewrite using `[h1, hpow, if_pos ha]`. Establish `h1 : Zl.JC.zj d t j a = 1` using `by simp [Zl.JC.zj, ha]`. Rewrite using `[h1, if_neg ha, map_one]`. Conclude with `(hone 1).2 (by simp)`. Establish `hE : 0 < (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ)`.

Use `mul_pos (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨j, by simp⟩) (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨⟨j.val + 1, hj⟩, ?_⟩)` and prove the remaining obligations. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩`. Establish `hmod : modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) = nabs k t ^ ((∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ))`. Rewrite using `[← exponent_eq, ← prod_zpow_eq hx0.ne']`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[hdet]`. Use `split_ifs with ha`. Rewrite using `[zpow_mul, zpow_natCast]`. Simplify using the standard rewrite rules. Rewrite using `[hmod]`.

Conclude with `zpow_lt_one₀ hx0 hx1 hE`.
-/
theorem modulus_zj_lt_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) →
    ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h →
    modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) < 1 := by
  intro k _ _ _ _ h N d _ hpos t ht j hj
  have hx1 := nabs_lt_one_of_valuation_lt_one k t ht
  obtain ⟨hmul, hx0', -, hone, -⟩ := nabs_properties k
  have hx0 := hx0' t
  have hdet : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) =
      if a ≤ j then nabs k t ^ d a else 1 := by
    intro a
    have hpow : ∀ n : ℕ, nabs k (t ^ n) = nabs k t ^ n := by
      intro n
      induction n with
      | zero => simpa using (hone 1).2 (by simp)
      | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
    by_cases ha : a ≤ j
    · have h1 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = t ^ d a := by
        apply Units.ext
        simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.det_diagonal]
      rw [h1, hpow, if_pos ha]
    · have h1 : Zl.JC.zj d t j a = 1 := by simp [Zl.JC.zj, ha]
      rw [h1, if_neg ha, map_one]
      exact (hone 1).2 (by simp)
  have hE : 0 < (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
    refine mul_pos (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨j, by simp⟩)
      (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨⟨j.val + 1, hj⟩, ?_⟩)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩
  have hmod : modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) =
      nabs k t ^ ((∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ)) := by
    rw [← exponent_eq, ← prod_zpow_eq hx0.ne']
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hdet]
    split_ifs with ha
    · rw [zpow_mul, zpow_natCast]
    · simp
  rw [hmod]
  exact zpow_lt_one₀ hx0 hx1 hE

end GlobalTheory.CompanionTheory.JCModulus
