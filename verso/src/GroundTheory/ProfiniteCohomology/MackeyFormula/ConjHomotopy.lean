import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.InnerConj
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology Finset

universe u

section Sequences

variable {Γ : Type*} [Group Γ]

def seqTuple (m : ℕ) (F : ℕ → Γ) : Fin m → Γ :=
  fun k => F k

def tupleSeq {m : ℕ} (γ : Fin m → Γ) : ℕ → Γ :=
  fun k => if h : k < m then γ ⟨k, h⟩ else 1

/- English proof (translation)
The claim follows from `funext fun k => dif_pos k.2`.
-/
theorem seqTuple_tupleSeq {m : ℕ} (γ : Fin m → Γ) : seqTuple m (tupleSeq γ) = γ :=
  funext fun k => dif_pos k.2

omit [Group Γ] in
/- English proof (translation)
The claim follows from `funext fun k => h k k.2`.
-/
theorem seqTuple_congr {m : ℕ} {F F' : ℕ → Γ} (h : ∀ k < m, F k = F' k) :
    seqTuple m F = seqTuple m F' :=
  funext fun k => h k k.2

/- English proof (translation)
The claim follows from `dif_pos hk`.
-/
theorem tupleSeq_seqTuple_of_lt {m : ℕ} (F : ℕ → Γ) {k : ℕ} (hk : k < m) :
    tupleSeq (seqTuple m F) k = F k :=
  dif_pos hk

def prismSeq (g : Γ) (i : ℕ) (F : ℕ → Γ) : ℕ → Γ :=
  fun k => if k < i then F k else if k = i then g else g⁻¹ * F (k - 1) * g

def contractSeq (j : ℕ) (F : ℕ → Γ) : ℕ → Γ :=
  fun k => if k < j then F k else if k = j then F k * F (k + 1) else F (k + 1)

def prismTuple (g : Γ) (i : ℕ) {m : ℕ} (γ : Fin m → Γ) : Fin (m + 1) → Γ :=
  seqTuple (m + 1) (prismSeq g i (tupleSeq γ))

/- English proof (translation)
The claim follows from `seqTuple_congr fun k hk => by simp only [prismSeq] split_ifs with h1 h2 · exact tupleSeq_seqTuple_of_lt F (by omega) · rfl · rw [tupleSeq_seqTuple_of_lt F (by omega)]`.
-/
theorem prismTuple_seqTuple (g : Γ) {i m : ℕ} (hi : i ≤ m) (F : ℕ → Γ) :
    prismTuple g i (seqTuple m F) = seqTuple (m + 1) (prismSeq g i F) :=
  seqTuple_congr fun k hk => by
    simp only [prismSeq]
    split_ifs with h1 h2
    · exact tupleSeq_seqTuple_of_lt F (by omega)
    · rfl
    · rw [tupleSeq_seqTuple_of_lt F (by omega)]

/- English proof (translation)
Simplify using `[prismSeq]`.
-/
theorem prismSeq_zero_zero (g : Γ) (F : ℕ → Γ) : prismSeq g 0 F 0 = g := by
  simp [prismSeq]

/- English proof (translation)
Simplify using `[prismSeq]`.
-/
theorem prismSeq_zero_succ (g : Γ) (F : ℕ → Γ) (k : ℕ) :
    prismSeq g 0 F (k + 1) = g⁻¹ * F k * g := by
  simp [prismSeq]

/- English proof (translation)
Simplify using `[prismSeq]`.
-/
theorem prismSeq_succ_zero (g : Γ) (i : ℕ) (F : ℕ → Γ) : prismSeq g (i + 1) F 0 = F 0 := by
  simp [prismSeq]

/- English proof (translation)
Simplify using `only [prismSeq, Nat.add_sub_cancel]`. Use `split_ifs`. Apply the tactic sequence `all_goals first | omega | rfl | (congr!; omega)`.
-/
theorem prismSeq_succ_succ (g : Γ) (i : ℕ) (F : ℕ → Γ) (k : ℕ) :
    prismSeq g (i + 1) F (k + 1) = prismSeq g i (fun l => F (l + 1)) k := by
  simp only [prismSeq, Nat.add_sub_cancel]
  split_ifs
  all_goals first | omega | rfl | (congr!; omega)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [contractSeq, prismSeq, Nat.add_sub_cancel]`. Use `split_ifs`. Apply the tactic sequence `all_goals first | omega | rfl | (congr!; omega)`.
-/
theorem contractSeq_prismSeq_of_lt (g : Γ) {i j : ℕ} (h : j + 1 < i) (F : ℕ → Γ) :
    contractSeq j (prismSeq g i F) = prismSeq g (i - 1) (contractSeq j F) := by
  funext k
  simp only [contractSeq, prismSeq, Nat.add_sub_cancel]
  split_ifs
  all_goals first | omega | rfl | (congr!; omega)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [contractSeq, prismSeq, Nat.add_sub_cancel]`. Use `split_ifs`. Apply the tactic sequence `all_goals first | omega | rfl | (congr!; omega) | group`.
-/
theorem contractSeq_prismSeq_self (g : Γ) (i : ℕ) (F : ℕ → Γ) :
    contractSeq i (prismSeq g i F) = contractSeq i (prismSeq g (i + 1) F) := by
  funext k
  simp only [contractSeq, prismSeq, Nat.add_sub_cancel]
  split_ifs
  all_goals first | omega | rfl | (congr!; omega) | group

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [contractSeq, prismSeq, Nat.add_sub_cancel]`. Use `split_ifs`. Apply the tactic sequence `all_goals first | omega | rfl | (congr!; omega) | (group; done) | (simp only [Nat.sub_add_cancel (show 1 ≤ k by omega)]; group)`.
-/
theorem contractSeq_prismSeq_of_gt (g : Γ) {i j : ℕ} (h : i < j) (F : ℕ → Γ) :
    contractSeq j (prismSeq g i F) = prismSeq g i (contractSeq (j - 1) F) := by
  funext k
  simp only [contractSeq, prismSeq, Nat.add_sub_cancel]
  split_ifs
  all_goals first | omega | rfl | (congr!; omega) | (group; done) | (simp only [Nat.sub_add_cancel (show 1 ≤ k by omega)]; group)

/- English proof (translation)
The claim follows from `seqTuple_congr fun k hk => by simp only [contractSeq, prismSeq] split_ifs all_goals first | omega | rfl`.
-/
theorem contractSeq_prismSeq_last (g : Γ) (m : ℕ) (F : ℕ → Γ) :
    seqTuple m (contractSeq m (prismSeq g m F)) = seqTuple m F :=
  seqTuple_congr fun k hk => by
    simp only [contractSeq, prismSeq]
    split_ifs
    all_goals first | omega | rfl

end Sequences

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Establish `e1 : ∑ j ∈ range N, s (N + 1) j + ∑ j ∈ range N, r N j = 0`. Rewrite using `[← sum_add_distrib]`.

Conclude with `sum_eq_zero fun j hj => by`. Rewrite using `[h1 (N + 1) j (by simp at hj; omega)]`. Simplify using the standard rewrite rules. Establish `e2 : ∑ i ∈ range (N + 1), s i (N + 1) + ∑ i ∈ range (N + 1), r i N = 0`. Rewrite using `[← sum_add_distrib]`.

Conclude with `sum_eq_zero fun i hi => by`. Rewrite using `[h2 i (N + 1) (by simp at hi; omega)]`. Simplify using the standard rewrite rules. Establish `e3` using `h3 N`. Establish `key` using `congrArg₂ (· + ·) (congrArg₂ (· + ·) ih e1) (congrArg₂ (· + ·) e2 e3)`.

Simplify using `only [sum_range_succ, sum_add_distrib] at key ⊢`. Rewrite using `[← sub_eq_zero, ← sub_eq_zero.mpr key]`. Normalize the expressions using the abelian group laws.
-/
theorem prism_double_sum_eq {M : Type*} [AddCommGroup M] (s r : ℕ → ℕ → M)
    (h1 : ∀ i j, j + 1 < i → s i j = -r (i - 1) j)
    (h2 : ∀ i j, i < j → s i j = -r i (j - 1))
    (h3 : ∀ i, s i i + s (i + 1) i = 0) (N : ℕ) :
    ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), s i j + ∑ i ∈ range N, ∑ j ∈ range N, r i j =
      s N N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e1 : ∑ j ∈ range N, s (N + 1) j + ∑ j ∈ range N, r N j = 0 := by
      rw [← sum_add_distrib]
      exact sum_eq_zero fun j hj => by
        rw [h1 (N + 1) j (by simp at hj; omega)]
        simp
    have e2 : ∑ i ∈ range (N + 1), s i (N + 1) + ∑ i ∈ range (N + 1), r i N = 0 := by
      rw [← sum_add_distrib]
      exact sum_eq_zero fun i hi => by
        rw [h2 i (N + 1) (by simp at hi; omega)]
        simp
    have e3 := h3 N
    have key := congrArg₂ (· + ·) (congrArg₂ (· + ·) ih e1) (congrArg₂ (· + ·) e2 e3)
    simp only [sum_range_succ, sum_add_distrib] at key ⊢
    rw [← sub_eq_zero, ← sub_eq_zero.mpr key]
    abel

section Functions

variable {k Γ : Type u} [CommRing k] [Group Γ] (A : Rep.{u} k Γ) (g : Γ)

def conjHomotopyFun (n : ℕ) (φ : (Fin (n + 1) → Γ) → A) : (Fin n → Γ) → A :=
  fun γ => ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) • φ (prismTuple g i γ)

def conjCochainFun {n : ℕ} (φ : (Fin n → Γ) → A) : (Fin n → Γ) → A :=
  fun γ => A.ρ g (φ fun l => g⁻¹ * γ l * g)

/- English proof (translation)
Rewrite using `[conjHomotopyFun, Fin.sum_univ_eq_sum_range (fun i => (-1 : k) ^ i • φ (prismTuple g i (seqTuple n X))) (n + 1)]`. Use `sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[prismTuple_seqTuple g (by simp at hi; omega)]`.
-/
theorem conjHomotopyFun_seqTuple (n : ℕ) (φ : (Fin (n + 1) → Γ) → A) (X : ℕ → Γ) :
    conjHomotopyFun A g n φ (seqTuple n X) =
      ∑ i ∈ range (n + 1), (-1 : k) ^ i • φ (seqTuple (n + 1) (prismSeq g i X)) := by
  rw [conjHomotopyFun, Fin.sum_univ_eq_sum_range
    (fun i => (-1 : k) ^ i • φ (prismTuple g i (seqTuple n X))) (n + 1)]
  refine sum_congr rfl fun i hi => ?_
  rw [prismTuple_seqTuple g (by simp at hi; omega)]

/- English proof (translation)
Rewrite using `[inhomogeneousCochains.d_hom_apply]`. Use `congr 1`. Conclude with `Fin.sum_univ_eq_sum_range (fun j => (-1 : k) ^ (j + 1) • f (seqTuple m (contractSeq j Y))) (m + 1)`.
-/
theorem d_seqTuple (m : ℕ) (f : (Fin m → Γ) → A) (Y : ℕ → Γ) :
    (inhomogeneousCochains.d A m).hom f (seqTuple (m + 1) Y) =
      A.ρ (Y 0) (f (seqTuple m fun l => Y (l + 1))) +
        ∑ j ∈ range (m + 1), (-1 : k) ^ (j + 1) • f (seqTuple m (contractSeq j Y)) := by
  rw [inhomogeneousCochains.d_hom_apply]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j => (-1 : k) ^ (j + 1) • f (seqTuple m (contractSeq j Y)))
    (m + 1)

/- English proof (translation)
Use function extensionality and compare the values at `γ`. Rewrite using `[← seqTuple_tupleSeq γ]`. Use `set F := tupleSeq γ`. Use `set ψ : (ℕ → Γ) → A := fun X => φ (seqTuple (n + 1) X) with hψ`. Express the relevant statement in the definitionally equal form `(inhomogeneousCochains.d A n).hom (conjHomotopyFun A g n φ) (seqTuple (n + 1) F) + conjHomotopyFun A g (n + 1) ((inhomogeneousCochains.d A (n + 1)).hom φ) (seqTuple (n + 1) F) = A.ρ g (ψ fun l => g⁻¹ * F l * g) - ψ F`.

Rewrite using `[d_seqTuple, conjHomotopyFun_seqTuple]`. Simplify using `only [conjHomotopyFun_seqTuple]`. Use `set s : ℕ → ℕ → A := fun i j => (-1 : k) ^ i • ((-1 : k) ^ (j + 1) • ψ (contractSeq j (prismSeq g i F))) with hs`. Use `set r : ℕ → ℕ → A := fun i j => (-1 : k) ^ (j + 1) • ((-1 : k) ^ i • ψ (prismSeq g i (contractSeq j F))) with hr`. Establish `hP` using `prism_double_sum_eq s r (fun i j hij => by`.

Take `⟨i', rfl⟩ : ∃ i', i = i' + 1` from `⟨i - 1, by omega⟩`. Simplify using `only [hs, hr, contractSeq_prismSeq_of_lt g hij, smul_smul, ← neg_smul]`. Use `congr 1`. Simplify using `only [Nat.add_sub_cancel]`. Use the proof step `ring)`.

Use the proof step `(fun i j hij => by`. Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Simplify using `only [hs, hr, contractSeq_prismSeq_of_gt g hij, smul_smul, ← neg_smul]`. Use `congr 1`. Simplify using `only [Nat.add_sub_cancel]`.

Use the proof step `ring)`. Use the proof step `(fun i => by`. Simplify using `only [hs, contractSeq_prismSeq_self g i F, smul_smul, ← add_smul]`. Use `zero_smul k _` and compare the differences between its conclusion and the goal. Use the proof step `ring)`.

Use the proof step `(n + 1)`. Establish `hlast : s (n + 1) (n + 1) = -ψ F`. Simplify using `only [hs, smul_smul]`. Rewrite using `[show ψ (contractSeq (n + 1) (prismSeq g (n + 1) F)) = ψ F from congrArg φ (contractSeq_prismSeq_last g (n + 1) F), ← neg_one_smul k (ψ F)]`. Use `congr 1`.

Rewrite using `[← pow_add, show n + 1 + (n + 1 + 1) = 2 * (n + 1) + 1 by ring, pow_succ, pow_mul]`. Evaluate the numerical expressions. Rewrite `hP` using `[hlast]`. Establish `hH : ∑ i ∈ range (n + 1 + 1), (-1 : k) ^ i • A.ρ (prismSeq g i F 0) (φ (seqTuple (n + 1) fun l => prismSeq g i F (l + 1))) = A.ρ g (ψ fun l => g⁻¹ * F l * g) - A.ρ (F 0) (∑ i ∈ range (n + 1), (-1 : k) ^ i • ψ (prismSeq g i fun l => F (l + 1)))`. Rewrite using `[sum_range_succ', map_sum]`.

Simplify using `only [prismSeq_zero_zero, prismSeq_succ_zero, prismSeq_succ_succ, pow_zero, one_smul, map_smul]`. Establish `e0 : (fun l => prismSeq g 0 F (l + 1)) = fun l => g⁻¹ * F l * g`. Use function extensionality and compare the values at `fun l => prismSeq_zero_succ g F l`. Rewrite using `[e0, sub_eq_add_neg, add_comm, ← sum_neg_distrib]`. Use `congr 1`.

Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ, mul_neg_one, neg_smul]`. Establish `hL2 : ∑ i ∈ range (n + 1 + 1), (-1 : k) ^ i • (inhomogeneousCochains.d A (n + 1)).hom φ (seqTuple (n + 1 + 1) (prismSeq g i F)) = ∑ i ∈ range (n + 1 + 1), (-1 : k) ^ i • A.ρ (prismSeq g i F 0) (φ (seqTuple (n + 1) fun l => prismSeq g i F (l + 1))) + ∑ i ∈ range (n + 1 + 1), ∑ j ∈ …`. Rewrite using `[← sum_add_distrib]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[d_seqTuple, smul_add, smul_sum]`. Establish `hL1 : ∑ j ∈ range (n + 1), (-1 : k) ^ (j + 1) • ∑ i ∈ range (n + 1), (-1 : k) ^ i • φ (seqTuple (n + 1) (prismSeq g i (contractSeq j F))) = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), r i j`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_sum]`.

Rewrite using `[hL2, hL1, hH]`. Rewrite using `[← sub_eq_zero, ← sub_eq_zero.mpr hP]`. Normalize the expressions using the abelian group laws.
-/
theorem conjHomotopyFun_spec (n : ℕ) (φ : (Fin (n + 1) → Γ) → A) :
    (inhomogeneousCochains.d A n).hom (conjHomotopyFun A g n φ) +
        conjHomotopyFun A g (n + 1) ((inhomogeneousCochains.d A (n + 1)).hom φ) =
      conjCochainFun A g φ - φ := by
  funext γ
  rw [← seqTuple_tupleSeq γ]
  set F := tupleSeq γ
  set ψ : (ℕ → Γ) → A := fun X => φ (seqTuple (n + 1) X) with hψ
  change (inhomogeneousCochains.d A n).hom (conjHomotopyFun A g n φ) (seqTuple (n + 1) F) +
      conjHomotopyFun A g (n + 1) ((inhomogeneousCochains.d A (n + 1)).hom φ)
        (seqTuple (n + 1) F) =
    A.ρ g (ψ fun l => g⁻¹ * F l * g) - ψ F
  rw [d_seqTuple, conjHomotopyFun_seqTuple]
  simp only [conjHomotopyFun_seqTuple]

  set s : ℕ → ℕ → A := fun i j =>
    (-1 : k) ^ i • ((-1 : k) ^ (j + 1) • ψ (contractSeq j (prismSeq g i F))) with hs
  set r : ℕ → ℕ → A := fun i j =>
    (-1 : k) ^ (j + 1) • ((-1 : k) ^ i • ψ (prismSeq g i (contractSeq j F))) with hr
  have hP := prism_double_sum_eq s r
    (fun i j hij => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [hs, hr, contractSeq_prismSeq_of_lt g hij, smul_smul, ← neg_smul]
      congr 1
      simp only [Nat.add_sub_cancel]
      ring)
    (fun i j hij => by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [hs, hr, contractSeq_prismSeq_of_gt g hij, smul_smul, ← neg_smul]
      congr 1
      simp only [Nat.add_sub_cancel]
      ring)
    (fun i => by
      simp only [hs, contractSeq_prismSeq_self g i F, smul_smul, ← add_smul]
      convert zero_smul k _
      ring)
    (n + 1)
  have hlast : s (n + 1) (n + 1) = -ψ F := by
    simp only [hs, smul_smul]
    rw [show ψ (contractSeq (n + 1) (prismSeq g (n + 1) F)) = ψ F from
      congrArg φ (contractSeq_prismSeq_last g (n + 1) F), ← neg_one_smul k (ψ F)]
    congr 1
    rw [← pow_add, show n + 1 + (n + 1 + 1) = 2 * (n + 1) + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [hlast] at hP

  have hH : ∑ i ∈ range (n + 1 + 1), (-1 : k) ^ i • A.ρ (prismSeq g i F 0)
        (φ (seqTuple (n + 1) fun l => prismSeq g i F (l + 1))) =
      A.ρ g (ψ fun l => g⁻¹ * F l * g) -
        A.ρ (F 0) (∑ i ∈ range (n + 1), (-1 : k) ^ i •
          ψ (prismSeq g i fun l => F (l + 1))) := by
    rw [sum_range_succ', map_sum]
    simp only [prismSeq_zero_zero, prismSeq_succ_zero, prismSeq_succ_succ, pow_zero, one_smul,
      map_smul]
    have e0 : (fun l => prismSeq g 0 F (l + 1)) = fun l => g⁻¹ * F l * g :=
      funext fun l => prismSeq_zero_succ g F l
    rw [e0, sub_eq_add_neg, add_comm, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [pow_succ, mul_neg_one, neg_smul]

  have hL2 : ∑ i ∈ range (n + 1 + 1), (-1 : k) ^ i •
        (inhomogeneousCochains.d A (n + 1)).hom φ (seqTuple (n + 1 + 1) (prismSeq g i F)) =
      ∑ i ∈ range (n + 1 + 1), (-1 : k) ^ i • A.ρ (prismSeq g i F 0)
          (φ (seqTuple (n + 1) fun l => prismSeq g i F (l + 1))) +
        ∑ i ∈ range (n + 1 + 1), ∑ j ∈ range (n + 1 + 1), s i j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [d_seqTuple, smul_add, smul_sum]
  have hL1 : ∑ j ∈ range (n + 1), (-1 : k) ^ (j + 1) • ∑ i ∈ range (n + 1), (-1 : k) ^ i •
        φ (seqTuple (n + 1) (prismSeq g i (contractSeq j F))) =
      ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), r i j := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [smul_sum]
  rw [hL2, hL1, hH]
  rw [← sub_eq_zero, ← sub_eq_zero.mpr hP]
  abel

/- English proof (translation)
Use function extensionality and compare the values at `γ`. Establish `e : ∀ x : Fin 0 → Γ, x = γ` using `fun _ => Subsingleton.elim _ _`. Rewrite using `[← seqTuple_tupleSeq γ, conjHomotopyFun_seqTuple, sum_range_one, d_seqTuple, sum_range_one, prismSeq_zero_zero]`. Simplify using `only [pow_zero, one_smul, zero_add, pow_one, neg_one_smul, conjCochainFun, Pi.sub_apply]`. Establish `e' : ∀ x : Fin 0 → Γ, φ x = φ γ` using `fun x => congrArg φ (e x)`.

Simplify using `only [e', sub_eq_add_neg]`.
-/
theorem conjHomotopyFun_spec_zero (φ : (Fin 0 → Γ) → A) :
    conjHomotopyFun A g 0 ((inhomogeneousCochains.d A 0).hom φ) = conjCochainFun A g φ - φ := by
  funext γ
  have e : ∀ x : Fin 0 → Γ, x = γ := fun _ => Subsingleton.elim _ _
  rw [← seqTuple_tupleSeq γ, conjHomotopyFun_seqTuple, sum_range_one, d_seqTuple, sum_range_one,
    prismSeq_zero_zero]
  simp only [pow_zero, one_smul, zero_add, pow_one, neg_one_smul, conjCochainFun, Pi.sub_apply]
  have e' : ∀ x : Fin 0 → Γ, φ x = φ γ := fun x => congrArg φ (e x)
  simp only [e', sub_eq_add_neg]

end Functions

section Homotopy

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (A : Rep.{u} k Γ) [IsDiscreteRep A] (g : Γ)

omit [IsTopologicalGroup Γ] in
/- English proof (translation)
Unfold `tupleSeq`. Use `split_ifs with h`. Conclude with `continuous_apply _`. Conclude with `continuous_const`.
-/
theorem continuous_tupleSeq_apply {n : ℕ} (m : ℕ) : Continuous fun γ : Fin n → Γ => tupleSeq γ m := by
  unfold tupleSeq
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

/- English proof (translation)
Use `continuous_pi fun l => ?_` and prove the remaining obligations. Simplify using `only [prismTuple, seqTuple, prismSeq]`. Use `split_ifs`. Conclude with `continuous_tupleSeq_apply _`. Conclude with `continuous_const`.

Conclude with `(continuous_const.mul (continuous_tupleSeq_apply _)).mul continuous_const`.
-/
theorem continuous_prismTuple (i n : ℕ) : Continuous fun γ : Fin n → Γ => prismTuple g i γ := by
  refine continuous_pi fun l => ?_
  simp only [prismTuple, seqTuple, prismSeq]
  split_ifs
  · exact continuous_tupleSeq_apply _
  · exact continuous_const
  · exact (continuous_const.mul (continuous_tupleSeq_apply _)).mul continuous_const

omit [IsDiscreteRep A] in

/- English proof (translation)
Establish `e : conjHomotopyFun A g n φ = ∑ i : Fin (n + 1), fun γ => (-1 : k) ^ (i : ℕ) • φ (prismTuple g i γ)`. Use function extensionality and compare the values at `γ`. Simplify using `[conjHomotopyFun, Finset.sum_apply]`. Rewrite using `[e]`. Conclude with `Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb) (IsLocallyConstant.const 0) fun i _ => (hφ.comp_continuous (continuous_prismTuple g i n)).comp _`.
-/
theorem isLocallyConstant_conjHomotopyFun {n : ℕ} {φ : (Fin (n + 1) → Γ) → A}
    (hφ : IsLocallyConstant φ) : IsLocallyConstant (conjHomotopyFun A g n φ) := by
  have e : conjHomotopyFun A g n φ =
      ∑ i : Fin (n + 1), fun γ => (-1 : k) ^ (i : ℕ) • φ (prismTuple g i γ) := by
    funext γ
    simp [conjHomotopyFun, Finset.sum_apply]
  rw [e]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb)
    (IsLocallyConstant.const 0) fun i _ =>
      (hφ.comp_continuous (continuous_prismTuple g i n)).comp _

noncomputable def conjHomotopyLinear (n : ℕ) :
    locallyConstantCochains A (n + 1) →ₗ[k] locallyConstantCochains A n where
  toFun φ := ⟨conjHomotopyFun A g n φ.1, isLocallyConstant_conjHomotopyFun A g φ.2⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext γ
    simp [conjHomotopyFun, smul_add, sum_add_distrib]
  map_smul' r φ := by
    apply Subtype.ext
    funext γ
    simp [conjHomotopyFun, smul_sum, smul_comm r]

noncomputable def conjHomotopyHom :
    ∀ i j, (ComplexShape.up ℕ).Rel j i → ((cochainsComplex A).X i ⟶ (cochainsComplex A).X j)
  | _, j, rfl => ModuleCat.ofHom (conjHomotopyLinear A g j)

/- English proof (translation)
Rewrite using `[cochainsComplex_d]`. Both sides reduce to the same expression.
-/
theorem cochainsComplex_d_hom_apply_coe (n : ℕ) (x : (cochainsComplex A).X n) :
    (((cochainsComplex A).d n (n + 1)).hom x).1 = (inhomogeneousCochains.d A n).hom x.1 := by
  rw [cochainsComplex_d]
  rfl

/- English proof (translation)
Use `HomologicalComplex.hom_ext _ _ fun n => ?_` and prove the remaining obligations. Rewrite using `[HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]`. Break down `n with _ | n` into its components or cases. Rewrite using `[Homotopy.nullHomotopicMap'_f_of_not_rel_right (c := ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 0 1 from rfl) (fun l hl => by simp at hl)]`. Use `ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)` and prove the remaining obligations.

Establish `h` using `conjHomotopyFun_spec_zero A g (x : locallyConstantCochains A 0).1`. Express the relevant statement in the definitionally equal form `_ = conjHomotopyFun A g 0 (((cochainsComplex A).d 0 1).hom x).1`. Rewrite using `[cochainsComplex_d_hom_apply_coe, h]`. Both sides reduce to the same expression. Rewrite using `[Homotopy.nullHomotopicMap'_f (c := ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl) (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl)]`.

Use `ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)` and prove the remaining obligations. Establish `h` using `conjHomotopyFun_spec A g n (x : locallyConstantCochains A (n + 1)).1`. Express the relevant statement in the definitionally equal form `_ = conjHomotopyFun A g (n + 1) (((cochainsComplex A).d (n + 1) (n + 1 + 1)).hom x).1 + (((cochainsComplex A).d n (n + 1)).hom (conjHomotopyLinear A g n x)).1`. Rewrite using `[cochainsComplex_d_hom_apply_coe]`. Use `erw [cochainsComplex_d_hom_apply_coe]`.

Establish `h' : conjHomotopyFun A g (n + 1) ((inhomogeneousCochains.d A (n + 1)).hom x.1) + (inhomogeneousCochains.d A n).hom (conjHomotopyFun A g n x.1) = conjCochainFun A g x.1 - x.1` using `(add_comm _ _).trans h`. Conclude with `Eq.trans rfl h'.symm`.
-/
theorem cochainsMapAlong_innerConj_sub_id :
    cochainsMapAlong (innerConjHom g) (continuous_innerConjHom g) (innerConjMor A g) -
        𝟙 (cochainsComplex A) = Homotopy.nullHomotopicMap' (conjHomotopyHom A g) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
  rcases n with _ | n
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (c := ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl) (fun l hl => by simp at hl)]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    have h := conjHomotopyFun_spec_zero A g (x : locallyConstantCochains A 0).1
    change _ = conjHomotopyFun A g 0 (((cochainsComplex A).d 0 1).hom x).1
    rw [cochainsComplex_d_hom_apply_coe, h]
    rfl
  · rw [Homotopy.nullHomotopicMap'_f (c := ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl)]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    have h := conjHomotopyFun_spec A g n (x : locallyConstantCochains A (n + 1)).1
    change _ = conjHomotopyFun A g (n + 1) (((cochainsComplex A).d (n + 1) (n + 1 + 1)).hom x).1 +
        (((cochainsComplex A).d n (n + 1)).hom (conjHomotopyLinear A g n x)).1
    rw [cochainsComplex_d_hom_apply_coe]
    erw [cochainsComplex_d_hom_apply_coe]
    have h' : conjHomotopyFun A g (n + 1) ((inhomogeneousCochains.d A (n + 1)).hom x.1) +
        (inhomogeneousCochains.d A n).hom (conjHomotopyFun A g n x.1) =
          conjCochainFun A g x.1 - x.1 :=
      (add_comm _ _).trans h
    exact Eq.trans rfl h'.symm

noncomputable def conjHomotopy :
    Homotopy (cochainsMapAlong (innerConjHom g) (continuous_innerConjHom g) (innerConjMor A g))
      (𝟙 (cochainsComplex A)) :=
  Homotopy.equivSubZero.symm ((Homotopy.ofEq (cochainsMapAlong_innerConj_sub_id A g)).trans
    (Homotopy.nullHomotopy' (conjHomotopyHom A g)))

end Homotopy

end GroundTheory.ProfCoh
