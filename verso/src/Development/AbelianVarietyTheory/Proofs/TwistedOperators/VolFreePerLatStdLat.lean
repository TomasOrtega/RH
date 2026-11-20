import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

def boxExp {n n' : Type} {c : ℕ} : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → ℕ
  | (_, Sum.inl _) => 0
  | (Sum.inl _, Sum.inr j) => j.val
  | (Sum.inr l, Sum.inr j) => j.val - (l.val + 1)

/- English proof (translation)
Apply the tactic sequence `rcases rs with ⟨r | l, s | j⟩ <;> simp only [Free, boxExp] at h ⊢ <;> omega`.
-/
theorem boxExp_eq_zero {n n' : Type} {c : ℕ} (rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
    (h : ¬ Free 1 rs) : boxExp rs = 0 := by
  rcases rs with ⟨r | l, s | j⟩ <;> simp only [Free, boxExp] at h ⊢ <;> omega

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun l => j - (l + 1)) c]`. Establish `h1 : ∑ l ∈ Finset.range c, (j - (l + 1)) = ∑ l ∈ Finset.range j, (j - (l + 1))`. Use `symm`. Use `Finset.sum_subset (Finset.range_subset_range.2 hj) ?_` and prove the remaining obligations. Introduce `x _ hx`.

Simplify using `only [Finset.mem_range] at hx`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, ← Finset.sum_range_id, ← Finset.sum_range_reflect (fun i => i) j]`. Use `Finset.sum_congr rfl fun x _ => by omega` and prove the remaining obligations.
-/
theorem sum_fin_sub (c j : ℕ) (hj : j ≤ c) :
    ∑ l : Fin c, (j - (l.val + 1)) = j * (j - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun l => j - (l + 1)) c]
  have h1 : ∑ l ∈ Finset.range c, (j - (l + 1)) = ∑ l ∈ Finset.range j, (j - (l + 1)) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 hj) ?_
    intro x _ hx
    simp only [Finset.mem_range] at hx
    omega
  rw [h1, ← Finset.sum_range_id, ← Finset.sum_range_reflect (fun i => i) j]
  refine Finset.sum_congr rfl fun x _ => by omega

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type_right, Fintype.sum_sum_type]`. Simplify using `only [Fintype.sum_sum_type, boxExp, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Establish `h : ∀ j : Fin (c + 1), Fintype.card n * j.val + ∑ l : Fin c, (j.val - (l.val + 1)) = j.val * Fintype.card n + j.val * (j.val - 1) / 2`. Introduce `j`. Rewrite using `[sum_fin_sub c j (by omega), mul_comm]`.

Rewrite using `[Finset.sum_congr rfl fun j _ => h j, Fin.sum_univ_eq_sum_range (fun j => j * Fintype.card n + j * (j - 1) / 2) (c + 1), expo]`. Use `symm`. Use `Finset.sum_subset ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Finset.mem_Icc, Finset.mem_range] at hx ⊢`.

Use linear arithmetic over natural numbers and integers. Introduce `x hx hx'`. Simplify using `only [Finset.mem_Icc, Finset.mem_range] at hx hx'`. Take `rfl : x = 0` from `by omega`. Simplify using the standard rewrite rules.
-/
theorem sum_boxExp (n n' : Type) [Fintype n] [Fintype n'] (c : ℕ) :
    ∑ rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), boxExp rs = expo c (Fintype.card n) := by
  rw [Fintype.sum_prod_type_right, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, boxExp, Finset.sum_const_zero, zero_add,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h : ∀ j : Fin (c + 1), Fintype.card n * j.val + ∑ l : Fin c, (j.val - (l.val + 1))
      = j.val * Fintype.card n + j.val * (j.val - 1) / 2 := by
    intro j
    rw [sum_fin_sub c j (by omega), mul_comm]
  rw [Finset.sum_congr rfl fun j _ => h j,
    Fin.sum_univ_eq_sum_range (fun j => j * Fintype.card n + j * (j - 1) / 2) (c + 1), expo]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_range] at hx hx'
    obtain rfl : x = 0 := by omega
    simp

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `hν.1` as an intermediate fact. Establish `h0 : (ϖ : k) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Use `set u : kˣ := Units.mk0 (ϖ : k) h0 with hu`. Establish `hset : {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = cball (u⁻¹ ^ m)`. Use extensionality with `x`.

Establish `hv : 0 < valuation k (ϖ : k) ^ m` using `pow_pos ((Valuation.pos_iff _).2 h0) m`. Simplify using `only [Set.mem_ofPred_eq, cball, Valuation.mem_integer_iff, map_mul, map_pow, hu, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, inv_pow]`. Rewrite using `[← one_div, le_div_iff₀ hv, mul_comm]`. Establish `h1 : distribHaarChar k u⁻¹ = (resCard k : NNReal)`. Use `nabs_uniformiser hϖ (x := u) rfl` as an intermediate fact.

Rewrite using `[map_inv]`. Apply `NNReal.coe_injective` to reduce the goal to its premises. Rewrite using `[NNReal.coe_inv]`. Simplify using `only [nabs] at this`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Rewrite using `[hset, measure_cball, hν.2, mul_one, map_pow, h1]`. Simplify using the standard rewrite rules.
-/
theorem measure_pow_mul_mem [MeasurableSpace k] [BorelSpace k] {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ)
    (ν : Measure k) (hν : IsUnitVol ν) (m : ℕ) :
    ν {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = (resCard k : ENNReal) ^ m := by
  have := hν.1
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set u : kˣ := Units.mk0 (ϖ : k) h0 with hu
  have hset : {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = cball (u⁻¹ ^ m) := by
    ext x
    have hv : 0 < valuation k (ϖ : k) ^ m := pow_pos ((Valuation.pos_iff _).2 h0) m
    simp only [Set.mem_ofPred_eq, cball, Valuation.mem_integer_iff, map_mul, map_pow, hu,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, inv_pow]
    rw [← one_div, le_div_iff₀ hv, mul_comm]
  have h1 : distribHaarChar k u⁻¹ = (resCard k : NNReal) := by
    have := nabs_uniformiser hϖ (x := u) rfl
    rw [map_inv]
    apply NNReal.coe_injective
    rw [NNReal.coe_inv]
    simp only [nabs] at this
    rw [this]
    simp
  rw [hset, measure_cball, hν.2, mul_one, map_pow, h1]
  simp

/- English proof (translation)
Establish `key : ∀ (i l : ℕ) (x : k), l ≤ i → ((∃ a : 𝒪[k], (ϖ : k) ^ (i + 1) * x = a * (ϖ : k) ^ (l + 1)) ↔ (ϖ : k) ^ (i + 1 - (l + 1)) * x ∈ 𝒪[k])`. Introduce `i l x hl`. Establish `hp : (ϖ : k) ^ (i + 1) = (ϖ : k) ^ (i + 1 - (l + 1)) * (ϖ : k) ^ (l + 1)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Establish `: (ϖ : k) ^ (i + 1 - (l + 1)) * x = a`. Apply `mul_right_cancel₀ (pow_ne_zero (l + 1) h0)` to reduce the goal to its premises.

Rewrite using `[← ha, hp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `a.2`. Introduce `h`.

Conclude with `⟨⟨_, h⟩, by rw [hp]; ring⟩`. Use extensionality with `e`. Simplify using `only [SetLike.mem_coe, mem_perLat, mem_chainLat, mem_stdLat, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_true_left, Pi.smul_apply, smul_eq_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ⟨⟨r, s | j⟩, hf⟩`.

Apply the tactic sequence `rcases r with r | l <;> simp [Free] at hf`. Establish `hj : j ≠ 0`. Introduce and unpack `rfl`. Apply the tactic sequence `rcases r with r | l <;> simp [Free] at hf`. Take `⟨i, rfl⟩` from `Fin.exists_succ_eq.2 hj`.

Break down `r with r | l` into its components or cases. Use `(h i).1 r` as an intermediate fact. Simplify using `only [UnfoldShape.col, dif_pos hf] at this`. Conclude with `this`. Use `(h i).2 l` as an intermediate fact.

Simplify using `only [UnfoldShape.col, dif_pos hf] at this`. Establish `hl : l.val ≤ i.val`. Simplify using `only [Free, Fin.val_succ] at hf`. Use linear arithmetic over natural numbers and integers. Conclude with `(key _ _ _ hl).1 this`.

Introduce `h i`. Use `⟨fun r => ?_, fun l => ?_⟩` and prove the remaining obligations. Establish `hf : Free 1 ((Sum.inl r, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))`. Simplify using `[Free]`. Simplify using `only [UnfoldShape.col, dif_pos hf]`.

Conclude with `h ⟨_, hf⟩`. Distinguish the cases in `hf : Free 1 ((Sum.inr l, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))`. Simplify using `only [UnfoldShape.col, dif_pos hf]`. Establish `hl : l.val ≤ i.val`. Simplify using `only [Free, Fin.val_succ] at hf`.

Use linear arithmetic over natural numbers and integers. Conclude with `(key _ _ _ hl).2 (h ⟨_, hf⟩)`. Simplify using `only [UnfoldShape.col, dif_neg hf]`. Conclude with `⟨0, by simp⟩`.
-/
theorem perLat_stdLat_eq {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} {ϖ : 𝒪[k]} (h0 : (ϖ : k) ≠ 0) :
    ((perLat ϖ n' c (stdLat k n) : AddSubgroup _) :
      Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) =
      Set.univ.pi fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} =>
        {x | (ϖ : k) ^ boxExp rs.1 * x ∈ 𝒪[k]} := by
  have key : ∀ (i l : ℕ) (x : k), l ≤ i →
      ((∃ a : 𝒪[k], (ϖ : k) ^ (i + 1) * x = a * (ϖ : k) ^ (l + 1)) ↔
        (ϖ : k) ^ (i + 1 - (l + 1)) * x ∈ 𝒪[k]) := by
    intro i l x hl
    have hp : (ϖ : k) ^ (i + 1) = (ϖ : k) ^ (i + 1 - (l + 1)) * (ϖ : k) ^ (l + 1) := by
      rw [← pow_add]; congr 1; omega
    constructor
    · rintro ⟨a, ha⟩
      have : (ϖ : k) ^ (i + 1 - (l + 1)) * x = a := by
        apply mul_right_cancel₀ (pow_ne_zero (l + 1) h0)
        rw [← ha, hp]; ring
      rw [this]; exact a.2
    · intro h
      exact ⟨⟨_, h⟩, by rw [hp]; ring⟩
  ext e
  simp only [SetLike.mem_coe, mem_perLat, mem_chainLat, mem_stdLat, Set.mem_pi, Set.mem_univ,
    Set.mem_ofPred_eq, forall_true_left, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro h ⟨⟨r, s | j⟩, hf⟩
    · rcases r with r | l <;> simp [Free] at hf
    · have hj : j ≠ 0 := by
        rintro rfl
        rcases r with r | l <;> simp [Free] at hf
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hj
      rcases r with r | l
      · have := (h i).1 r
        simp only [UnfoldShape.col, dif_pos hf] at this
        exact this
      · have := (h i).2 l
        simp only [UnfoldShape.col, dif_pos hf] at this
        have hl : l.val ≤ i.val := by
          simp only [Free, Fin.val_succ] at hf; omega
        exact (key _ _ _ hl).1 this
  · intro h i
    refine ⟨fun r => ?_, fun l => ?_⟩
    · have hf : Free 1 ((Sum.inl r, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
        simp [Free]
      simp only [UnfoldShape.col, dif_pos hf]
      exact h ⟨_, hf⟩
    · by_cases hf : Free 1 ((Sum.inr l, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
      · simp only [UnfoldShape.col, dif_pos hf]
        have hl : l.val ≤ i.val := by
          simp only [Free, Fin.val_succ] at hf; omega
        exact (key _ _ _ hl).2 (h ⟨_, hf⟩)
      · simp only [UnfoldShape.col, dif_neg hf]
        exact ⟨0, by simp⟩

end

/- English proof (translation)
Use `hν.1` as an intermediate fact. Use `secondCountable k` as an intermediate fact. Establish `h0 : (ϖ : k) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Rewrite using `[perLat_stdLat_eq h0, volFree, Measure.pi_pi]`. Simplify using `only [measure_pow_mul_mem hϖ ν hν]`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, ← sum_boxExp n n' c]`. Use `congr 1`. Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun rs => Free 1 rs) (by simp) boxExp]`. Use `Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => boxExp_eq_zero x ?_` and prove the remaining obligations. Simplify using `using hx`.
-/
theorem volFree_perLat_stdLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n]
    [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (c : ℕ) (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (ν : Measure k) (hν : IsUnitVol ν) :
    volFree ν n n' c (perLat ϖ n' c (stdLat k n))
      = (resCard k : ENNReal) ^ expo c (Fintype.card n) := by
  classical
  have := hν.1
  have := secondCountable k
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rw [perLat_stdLat_eq h0, volFree, Measure.pi_pi]
  simp only [measure_pow_mul_mem hϖ ν hν]
  rw [Finset.prod_pow_eq_pow_sum, ← sum_boxExp n n' c]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter fun rs => Free 1 rs) (by simp) boxExp]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => boxExp_eq_zero x ?_
  simpa using hx

end GlobalTheory.RootEx.UnfoldShape
