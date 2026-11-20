import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Take `⟨m, rfl⟩` from `hβ`. Use `choose! N hN using hℓ`. Use `⟨∑ a, ∑ b, if a < b then m a b * N a b else 0, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Rewrite using `[map_smul, hN a b h, smul_eq_mul]`. Simplify using the standard rewrite rules.
-/
theorem root_cone_functional_natural (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, ℓ (root a b) = N)
    {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, ℓ β = N := by
  classical
  obtain ⟨m, rfl⟩ := hβ
  choose! N hN using hℓ
  refine ⟨∑ a, ∑ b, if a < b then m a b * N a b else 0, ?_⟩
  simp only [map_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [map_smul, hN a b h, smul_eq_mul]
  · simp

def weightPowerSumFunctional (k : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), LinearMap.proj a

/- English proof (translation)
Simplify using `[weightPowerSumFunctional, kirrPs, LinearMap.sum_apply]`.
-/
theorem k3vdPs_apply (k : ℕ) (μ : Fin n → ℝ) : weightPowerSumFunctional k μ = kirrPs k μ := by
  simp [weightPowerSumFunctional, kirrPs, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `[kirrPs, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter]`.
-/
theorem partial_sum_of_basis_vector (k : ℕ) (a : Fin n) :
    kirrPs k (Pi.single a (1 : ℝ)) = if a.val < k then 1 else 0 := by
  simp [kirrPs, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter]

/- English proof (translation)
Rewrite using `[← partial_sum_of_basis_vector, ← partial_sum_of_basis_vector]`. Simplify using `[kirrPs, root, Finset.sum_sub_distrib]`.
-/
theorem partial_sum_of_root (k : ℕ) (a b : Fin n) :
    kirrPs k (root a b) = (if a.val < k then 1 else 0) - (if b.val < k then 1 else 0) := by
  rw [← partial_sum_of_basis_vector, ← partial_sum_of_basis_vector]
  simp [kirrPs, root, Finset.sum_sub_distrib]

/- English proof (translation)
Establish `hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightPowerSumFunctional k (root a b) = N`. Introduce `a b hab`. Establish `hv` using `Fin.lt_def.1 hab`. Rewrite using `[k3vdPs_apply, partial_sum_of_root]`. Apply the tactic sequence `by_cases ha : a.val < k <;> by_cases hb : b.val < k`.

Conclude with `⟨0, by simp [ha, hb]⟩`. Conclude with `⟨1, by simp [ha, hb]⟩`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨0, by simp [ha, hb]⟩`. Take `⟨N, hN⟩` from `root_cone_functional_natural (weightPowerSumFunctional k) hℓ hβ`.

Conclude with `⟨N, by rw [← k3vdPs_apply]; exact hN⟩`.
-/
theorem root_cone_partial_sum_natural {β : Fin n → ℝ} (hβ : InRootCone β) (k : ℕ) : ∃ N : ℕ, kirrPs k β = N := by
  have hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightPowerSumFunctional k (root a b) = N := by
    intro a b hab
    have hv := Fin.lt_def.1 hab
    rw [k3vdPs_apply, partial_sum_of_root]
    by_cases ha : a.val < k <;> by_cases hb : b.val < k
    · exact ⟨0, by simp [ha, hb]⟩
    · exact ⟨1, by simp [ha, hb]⟩
    · omega
    · exact ⟨0, by simp [ha, hb]⟩
  obtain ⟨N, hN⟩ := root_cone_functional_natural (weightPowerSumFunctional k) hℓ hβ
  exact ⟨N, by rw [← k3vdPs_apply]; exact hN⟩

def weightHeightFunctional : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) • LinearMap.proj c

/- English proof (translation)
Simplify using `only [weightHeightFunctional, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, root, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem k3vdHt_root (a b : Fin n) : weightHeightFunctional (root a b) = ((b : ℕ) : ℝ) - (a : ℕ) := by
  simp only [weightHeightFunctional, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    root, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Establish `hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightHeightFunctional (root a b) = N`. Introduce `a b hab`. Use `⟨b.val - a.val, ?_⟩` and prove the remaining obligations. Rewrite using `[k3vdHt_root, Nat.cast_sub (le_of_lt (Fin.lt_def.1 hab))]`. Conclude with `root_cone_functional_natural weightHeightFunctional hℓ hβ`.
-/
theorem root_cone_height_natural {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, weightHeightFunctional β = N := by
  have hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightHeightFunctional (root a b) = N := by
    intro a b hab
    refine ⟨b.val - a.val, ?_⟩
    rw [k3vdHt_root, Nat.cast_sub (le_of_lt (Fin.lt_def.1 hab))]
  exact root_cone_functional_natural weightHeightFunctional hℓ hβ

/- English proof (translation)
Unfold `kirrPs`. Rewrite using `[Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Establish `: c.val ≠ a.val` using `fun h => hc (Fin.ext h)`.

Distinguish the cases in `h1 : c.val < a.val`. Simplify using `[h1, show c.val < a.val + 1 by omega]`. Simplify using `[h1, show ¬ c.val < a.val + 1 by omega]`. Simplify using the standard rewrite rules.
-/
theorem coordinate_eq_partial_sum_difference (γ : Fin n → ℝ) (a : Fin n) :
    γ a = kirrPs ((a : ℕ) + 1) γ - kirrPs (a : ℕ) γ := by
  unfold kirrPs
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    have : c.val ≠ a.val := fun h => hc (Fin.ext h)
    by_cases h1 : c.val < a.val
    · simp [h1, show c.val < a.val + 1 by omega]
    · simp [h1, show ¬ c.val < a.val + 1 by omega]
  · simp

/- English proof (translation)
The claim follows from `|γ a - γ b| ≤ 2 := by have h1 := coordinate_eq_partial_sum_difference γ a have h2 := coordinate_eq_partial_sum_difference γ b have a1 := hγ ((a : ℕ) + 1) have a0 := hγ (a : ℕ) have b1 := hγ ((b : ℕ) + 1) have b0 := hγ (b : ℕ) rw [abs_le] constructor <;> linarith [a1.1, a1.2, a0.1 …`.
-/
theorem coordinate_difference_le_two (γ : Fin n → ℝ) (hγ : ∀ k, -1 ≤ kirrPs k γ ∧ kirrPs k γ ≤ 0) (a b : Fin n) :
    |γ a - γ b| ≤ 2 := by
  have h1 := coordinate_eq_partial_sum_difference γ a
  have h2 := coordinate_eq_partial_sum_difference γ b
  have a1 := hγ ((a : ℕ) + 1)
  have a0 := hγ (a : ℕ)
  have b1 := hγ ((b : ℕ) + 1)
  have b0 := hγ (b : ℕ)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a0.1, a0.2, b1.1, b1.2, b0.1, b0.2]

/- English proof (translation)
Introduce `a b hab`. Establish `key : ∀ d : ℕ, ∀ b : Fin n, b.val = a.val + d + 1 → f b < f a`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro b hb; exact h a b (by omega)`.

Consider the case `succ d ih`. Introduce `b hb`. Establish `hc : a.val + d + 1 < n` using `by have := b.isLt; omega`. Conclude with `lt_trans (h ⟨a.val + d + 1, hc⟩ b (by show b.val = a.val + d + 1 + 1; omega)) (ih ⟨a.val + d + 1, hc⟩ rfl)`. Conclude with `key (b.val - a.val - 1) b (by have := Fin.lt_def.1 hab; omega)`.
-/
theorem strictAnti_of_consecutive_lt {f : Fin n → ℝ} (h : ∀ a b : Fin n, b.val = a.val + 1 → f b < f a) :
    StrictAnti f := by
  intro a b hab
  have key : ∀ d : ℕ, ∀ b : Fin n, b.val = a.val + d + 1 → f b < f a := by
    intro d
    induction d with
    | zero => intro b hb; exact h a b (by omega)
    | succ d ih =>
      intro b hb
      have hc : a.val + d + 1 < n := by have := b.isLt; omega
      exact lt_trans (h ⟨a.val + d + 1, hc⟩ b (by show b.val = a.val + d + 1 + 1; omega))
        (ih ⟨a.val + d + 1, hc⟩ rfl)
  exact key (b.val - a.val - 1) b (by have := Fin.lt_def.1 hab; omega)

/- English proof (translation)
Establish `hab : ∀ c : Fin n, a < c ↔ c = b ∨ b < c`. Introduce `c`. Rewrite using `[Fin.lt_def, Fin.lt_def, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hba : ∀ c : Fin n, c < b ↔ c = a ∨ c < a`.

Introduce `c`. Rewrite using `[Fin.lt_def, Fin.lt_def, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `e1 : (univ.filter fun c => a < c ∧ ε c = ε a) = insert b (univ.filter fun c => b < c ∧ ε c = ε b)`. Use extensionality with `c`.

Simplify using `only [mem_filter, mem_univ, true_and, mem_insert, hab c, he]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1 | h1, h2⟩`. Conclude with `Or.inl h1`. Conclude with `Or.inr ⟨h1, h2⟩`.

Introduce and unpack `(rfl | ⟨h1, h2⟩)`. Conclude with `⟨Or.inl rfl, rfl⟩`. Conclude with `⟨Or.inr h1, h2⟩`. Establish `e2 : (univ.filter fun c => c < b ∧ ε c = ε b) = insert a (univ.filter fun c => c < a ∧ ε c = ε a)`. Use extensionality with `c`.

Simplify using `only [mem_filter, mem_univ, true_and, mem_insert, hba c, he]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1 | h1, h2⟩`. Conclude with `Or.inl h1`. Conclude with `Or.inr ⟨h1, h2⟩`.

Introduce and unpack `(rfl | ⟨h1, h2⟩)`. Conclude with `⟨Or.inl rfl, he⟩`. Conclude with `⟨Or.inr h1, h2⟩`. Establish `e3 : (univ.filter fun c => a < c ∧ ε c ≠ ε a) = (univ.filter fun c => b < c ∧ ε c ≠ ε b)`. Use extensionality with `c`.

Simplify using `only [mem_filter, mem_univ, true_and, hab c, he]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1 | h1, h2⟩`. Conclude with `absurd (h1 ▸ rfl) h2`. Conclude with `⟨h1, h2⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨Or.inr h1, h2⟩`. Establish `e4 : (univ.filter fun c => c < b ∧ ε c ≠ ε b) = (univ.filter fun c => c < a ∧ ε c ≠ ε a)`. Use extensionality with `c`. Simplify using `only [mem_filter, mem_univ, true_and, hba c, he]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1 | h1, h2⟩`. Conclude with `absurd (h1 ▸ he) h2`. Conclude with `⟨h1, h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨Or.inr h1, h2⟩`. Establish `nb : b ∉ univ.filter fun c => b < c ∧ ε c = ε b` using `by simp`. Establish `na : a ∉ univ.filter fun c => c < a ∧ ε c = ε a` using `by simp`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `rhoC`.

Rewrite using `[e1, e2, card_insert_of_notMem nb, card_insert_of_notMem na]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `rhoN`. Rewrite using `[e3, e4]`.
-/
theorem rho_consecutive_compact_pair (ε : Fin n → Bool) (a b : Fin n) (hb : b.val = a.val + 1) (he : ε a = ε b) :
    rhoC ε a = rhoC ε b + 1 ∧ rhoN ε a = rhoN ε b := by
  have hab : ∀ c : Fin n, a < c ↔ c = b ∨ b < c := by
    intro c; rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega
  have hba : ∀ c : Fin n, c < b ↔ c = a ∨ c < a := by
    intro c; rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega
  have e1 : (univ.filter fun c => a < c ∧ ε c = ε a) =
      insert b (univ.filter fun c => b < c ∧ ε c = ε b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, hab c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr h1, h2⟩
  have e2 : (univ.filter fun c => c < b ∧ ε c = ε b) =
      insert a (univ.filter fun c => c < a ∧ ε c = ε a) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, hba c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, he⟩
      · exact ⟨Or.inr h1, h2⟩
  have e3 : (univ.filter fun c => a < c ∧ ε c ≠ ε a) = (univ.filter fun c => b < c ∧ ε c ≠ ε b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hab c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ rfl) h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  have e4 : (univ.filter fun c => c < b ∧ ε c ≠ ε b) = (univ.filter fun c => c < a ∧ ε c ≠ ε a) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hba c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ he) h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  have nb : b ∉ univ.filter fun c => b < c ∧ ε c = ε b := by simp
  have na : a ∉ univ.filter fun c => c < a ∧ ε c = ε a := by simp
  refine ⟨?_, ?_⟩
  · unfold rhoC
    rw [e1, e2, card_insert_of_notMem nb, card_insert_of_notMem na]
    push_cast
    ring
  · unfold rhoN
    rw [e3, e4]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
